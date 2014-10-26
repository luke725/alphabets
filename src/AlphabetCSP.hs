-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module AlphabetCSP where
	import Debug.Trace
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import Data.Map (Map)
	import qualified Data.Map as Map
	import Math.Algebra.Group.PermutationGroup(Permutation, (~^))
	import qualified Math.Algebra.Group.PermutationGroup as PG
	import qualified Math.Algebra.Group.SchreierSims as SS

	import RelationalStructure
	import Letter
	import Utils
	import SAC3
	
	type Element = (Int, Permutation Int)

	data RName = Original (Automorphisms, Partition) | Unary Element | SMatch Int deriving (Show, Ord, Eq)

	type AStructure a = Structure RName a
	
	type GroupGens = [[[Atom]]]

	one :: Int -> Element
	one r = (r, PG.p [])
	
	eltArity :: Element -> Int
	eltArity (ar, _) = ar
	
	eltArities :: Relation RName Element -> Set Int
	eltArities (Relation (_, _, ts)) = 
		if Set.null ts
		then Set.empty
		else
			Set.fromList (map eltArity t)
		where
			Tuple t = Set.findMin ts
	
	
	findMajorityLetter :: Letter -> Maybe (Map (Tuple Element) Element)
	findMajorityLetter letter =	
		findMajorityAutomorphisms (letterAutomorphisms letter)

	checkMajorityAutomorphisms :: Automorphisms -> Bool
	checkMajorityAutomorphisms automorphisms = (findMajorityAutomorphisms automorphisms /= Nothing)

	findMajorityAutomorphisms :: Automorphisms -> Maybe (Map (Tuple Element) Element)
	findMajorityAutomorphisms automorphisms =
		findAlphMajority rels'
		where	
			maxAr = List.length $ fst automorphisms
			rels = 
				map
					(\(as, (ar, s)) -> Relation (Original (automorphisms, as), ar, s)) 
					(Map.toList (relationsFromAutomorphisms automorphisms))
			rels' =
				filter 
					(\r ->
						Set.null 
							(Set.intersection 
								(Set.fromList [maxAr, maxAr - 1]) 
								(eltArities r))
					) 
					rels
					
	ggElements :: GroupGens -> [Permutation Atom]
	ggElements gg = SS.elts (map (PG.fromCycles) gg)
	
	ggAtoms :: GroupGens -> [Atom]
	ggAtoms gg = List.nub (concat $ concat gg)
					
	findMajorityGG :: GroupGens -> Maybe (Map (Tuple Element) Element)
	findMajorityGG gg = findMajorityAutomorphisms (ggAtoms gg, ggElements gg)
	
	findMajorityGGMany :: [Atom] -> [GroupGens] -> Maybe (Map (Tuple Element) Element)
	findMajorityGGMany _atoms ggList =
		findAlphMajority rels'
		where
			maxAr :: Int = List.maximum $ map (\gg -> List.length (ggAtoms gg)) ggList
			rels =
				map (\(k, (ar, s)) -> Relation (k, ar, s)) 
				$ Map.toList
				$ removeDup
				$ Map.unions
				$ map (\(i, gg) -> Map.mapKeys (\as -> Original ((ggAtoms gg, ggElements gg), as)) $ relationsFromAutomorphisms (ggAtoms gg, trace (show i) $ ggElements gg))
				$ zip [1..length ggList] ggList
			rels' =
				filter 
					(\r -> 
						Set.null 
							(Set.intersection 
								(Set.fromList [maxAr, maxAr - 1]) 
								(eltArities r))
					) 
					rels

	checkMajorityAutomorphismsMany :: [Automorphisms] -> Bool
	checkMajorityAutomorphismsMany automorphismsList = (findMajorityAutomorphismsMany automorphismsList /= Nothing)
					
	findMajorityAutomorphismsMany :: [Automorphisms] -> Maybe (Map (Tuple Element) Element)
	findMajorityAutomorphismsMany automorphismsList =
			findAlphMajority rels'
		where
			maxAr = List.length $ fst $ head automorphismsList
			rels =
				map (\(k, (ar, s)) -> Relation (k, ar, s)) 
				$ Map.toList
				$ removeDup
				$ Map.unions
				$ map (\autos -> Map.mapKeys (\as -> Original (autos, as)) $ relationsFromAutomorphisms autos)
				$ automorphismsList
			rels' =
				filter 
					(\r -> 
						Set.null 
							(Set.intersection 
								(Set.fromList [maxAr, maxAr - 1]) 
								(eltArities r))
					) 
					rels

	isConjClassRep :: Element -> Bool
	isConjClassRep (i, p) =
		conjClassRep (Set.fromList [0..i-1]) p == p

	findAlphMajority :: [Relation RName Element] -> Maybe (Map (Tuple Element) Element)
	findAlphMajority rels =
		findSolutionFast tstr str 
		where
			elts = elementsFromRels rels
			
			rels' = 
				rels 
				++ map (\e -> Relation (Unary e, Arity 1, Set.singleton (Tuple [e]))) (Set.toList elts) 
			
			str :: Structure RName Element
			str = 
				(flip $ foldl (\str' (i, p) -> addToRelation (SMatch i) (Arity 1) [Tuple [(i, p)]] str')) (Set.toList elts)
				$ createStructure (sigFromRels rels') elts rels'
			
			tstr :: Structure RName (Tuple Element)
			tstr =
				conjClassOnly
				$ resetElements 
				$ foldl 
					(\tstr' e@(ar, _) -> 
						addToRelation 
							(Unary e) (Arity 1)
							[Tuple [Tuple [e, e]]]
						$ addToRelation
							(Unary (one ar)) (Arity 1)
							[Tuple [Tuple [e, one ar]], Tuple [Tuple [one ar, e]]] 
							tstr'
					) 
					(structPower str 2) 
					(Set.toList elts)
					
			conjClassOnly :: Structure RName (Tuple Element) -> Structure RName (Tuple Element)
			conjClassOnly (Structure (sig, elems, relMap)) =
				substructure (Structure (sig, elems, relMap)) (classReps elems)
				
			classReps :: Set (Tuple Element) -> Set (Tuple Element)
			classReps elems =
				fst $ foldl (\(cr, ce) e -> if Set.member e ce then (cr, ce) else (Set.insert e cr, Set.union (classElems e) ce)) (Set.empty, Set.empty) (Set.toList elems)
				
			classElems :: Tuple Element -> Set (Tuple Element)
			classElems (Tuple [(n1, p1), (n2, p2)]) = -- n1 == n2
				if (n1 /= n2) then error "error" else
					Set.fromList (map (\g -> Tuple [(n1, p1 ~^ g), (n2, p2 ~^ g)]) (map PG.fromList (List.permutations [0..n1-1])))
			classElems _ = error "Wrong pattern"

