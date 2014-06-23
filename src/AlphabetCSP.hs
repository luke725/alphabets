-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module AlphabetCSP where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.Maybe as Maybe
	import Math.Algebra.Group.PermutationGroup(Permutation)
	import qualified Math.Algebra.Group.PermutationGroup as PG
	import qualified Math.Algebra.Group.SchreierSims as SS

	import RelationalStructure
	import Letter
	import SAC3
	import ConstraintNetwork
	import Utils
	
	type Element = (Arity, Permutation Int)

	type RName = (Either ([Permutation Atom], [[Atom]]) Element)

	type AStructure a = Structure RName a
	
	type GroupGens = [[[Atom]]]

	one :: Arity -> Element
	one r = (r, PG.p [])
	
	eltArity :: Element -> Int
	eltArity (ar, _) = ar
	
	eltArities :: Relation RName Element -> Set Arity
	eltArities (_, _, ts) = 
		if Set.null ts
		then Set.empty
		else
			Set.fromList (map eltArity (Set.findMin ts))
	
	
	findMajorityLetter :: Letter -> Maybe (Map (Tuple Element) Element)
	findMajorityLetter letter =	
		findMajorityAutomorphisms (Set.toList (letterAtoms letter)) (letterAutomorphisms letter)

	checkMajorityAutomorphisms :: [Atom] -> [Permutation Atom] -> Bool
	checkMajorityAutomorphisms atoms automorphisms = (findMajorityAutomorphisms atoms automorphisms /= Nothing)

	findMajorityAutomorphisms :: [Atom] -> [Permutation Atom] -> Maybe (Map (Tuple Element) Element)
	findMajorityAutomorphisms atoms automorphisms =
		case mm' of
		 	Just m' ->
		 		case mm'' of
		 			Just m'' -> Just (Map.union m' m'')
		 			Nothing -> Nothing 
		 	Nothing -> Nothing
		where
			mm' = findAlphMajority rels'
			mm'' = findAlphMajority rels''		
			maxAr = List.length atoms
			rels = 
				map 
					(\(as, (ar, s)) -> (Left (automorphisms, as), ar, s)) 
					(Map.toList (relationsFromAutomorphisms atoms automorphisms))
			rels' =
				filter 
					(\r -> 
						Set.null 
							(Set.intersection 
								(Set.fromList [maxAr, maxAr - 1, maxAr - 2]) 
								(eltArities r))
					) 
					rels
			
			rels'' =
				filter
					(\r ->
						not $ Set.null
							(Set.intersection
								(Set.fromList [maxAr - 2, 1, 2])
								(eltArities r))
					)
					rels
					
	ggElements :: GroupGens -> [Permutation Atom]
	ggElements gg = SS.elts (map (PG.fromCycles) gg)
	
	ggAtoms :: GroupGens -> [Atom]
	ggAtoms gg = 
		if n < 4 then
			ggList ++ [100..(103 - n)]
		else
			ggList
		where
			n = List.length ggList
			ggList = List.nub (concat $ concat gg)
					
	findMajorityGG :: GroupGens -> Maybe (Map (Tuple Element) Element)
	findMajorityGG gg = findMajorityAutomorphisms (ggAtoms gg) (ggElements gg)
	
	findMajorityGGMany :: [GroupGens] -> Maybe (Map (Tuple Element) Element)
	findMajorityGGMany ggList =
		 case mm' of
		 	Just m' ->
		 		case mm'' of
		 			Just m'' -> Just (Map.union m' m'')
		 			Nothing -> Nothing 
		 	Nothing -> Nothing
		where
			mm' = findAlphMajority rels'
			mm'' = findAlphMajority rels''
			maxAr :: Int = List.maximum $ map (\gg -> List.length (ggAtoms gg)) ggList
			rels =
				map (\(k, (ar, s)) -> (k, ar, s)) 
				$ Map.toList
				$ removeDup
				$ Map.unions
				$ map (\gg -> Map.mapKeys (\as -> Left ((ggElements gg), as)) $ relationsFromAutomorphisms (ggAtoms gg) (ggElements gg))
				$ ggList
			rels' =
				filter 
					(\r -> 
						Set.null 
							(Set.intersection 
								(Set.fromList [maxAr, maxAr - 1, maxAr - 2]) 
								(eltArities r))
					) 
					rels
			
			rels'' =
				filter
					(\r ->
						not $ Set.null
							(Set.intersection
								(Set.fromList [maxAr - 2, 1, 2])
								(eltArities r))
					)
					rels

	checkMajorityAutomorphismsMany :: [Atom] -> [[Permutation Atom]] -> Bool
	checkMajorityAutomorphismsMany atoms automorphismsList = (findMajorityAutomorphismsMany atoms automorphismsList /= Nothing)
					
	findMajorityAutomorphismsMany :: [Atom] -> [[Permutation Atom]] -> Maybe (Map (Tuple Element) Element)
	findMajorityAutomorphismsMany atoms automorphismsList =
		 case mm' of
		 	Just m' ->
		 		case mm'' of
		 			Just m'' -> Just (Map.union m' m'')
		 			Nothing -> Nothing 
		 	Nothing -> Nothing
		where
			mm' = findAlphMajority rels'
			mm'' = findAlphMajority rels''
			maxAr = List.length atoms
			rels =
				map (\(k, (ar, s)) -> (k, ar, s)) 
				$ Map.toList
				$ removeDup
				$ Map.unions
				$ map (\autos -> Map.mapKeys (\as -> Left (autos, as)) $ relationsFromAutomorphisms atoms autos)
				$ automorphismsList
			rels' =
				filter 
					(\r -> 
						Set.null 
							(Set.intersection 
								(Set.fromList [maxAr, maxAr - 1, maxAr - 2]) 
								(eltArities r))
					) 
					rels
			
			rels'' =
				filter
					(\r ->
						not $ Set.null
							(Set.intersection
								(Set.fromList [maxAr - 2, 1, 2])
								(eltArities r))
					)
					rels

	findAlphMajority :: [Relation RName Element] -> Maybe (Map (Tuple Element) Element)
	findAlphMajority rels =
		case findSAC3Solution cn of
			Just m' -> Just (Map.fromList $ Maybe.catMaybes $ map mapMap $ map (\(v', d') -> (backV ! v', backD ! d')) $ Map.toList m')
			Nothing -> Nothing
		where
			mapMap (CSPElem v, CSPElem d) = Just (v, d)
			mapMap (CSPTuple _, CSPTuple _) = Nothing
			mapMap (_, _) = error ("Unexpected pattern in findAlphMajority")
			
			(cn, backV, backD) = translate (fromCSP tstr str)
			elts = elementsFromRels rels
			
			rels' = rels ++ map (\e -> (Right e, 1, Set.singleton [e])) (Set.toList elts)
			
			str :: Structure RName Element
			str = createStructure (sigFromRels rels') elts rels'
			
			tstr :: Structure RName (Tuple Element)
			tstr =
				resetElements 
				$ foldl 
					(\tstr' e@(ar, _) -> 
						addToRelation 
							(Right e) 1
							[[[e, e]]]
						$ addToRelation
							(Right (one ar)) 1
							[[[e, one ar]], [[one ar, e]]] 
							tstr'
					) 
					(structPower str 2) 
					(Set.toList elts)


