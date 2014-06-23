-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module AlphabetCSP where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import qualified Data.Map as Map
	import Math.Algebra.Group.PermutationGroup(Permutation)
	import qualified Math.Algebra.Group.PermutationGroup as PG

	import RelationalStructure
	import Letter
	import ArcConsistency
	
	type Element = (Int, Permutation Int)

	type RName = Either [[Atom]] Element

	type AStructure a = Structure RName a

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
	

	checkMajorityLetter :: Letter -> Bool
	checkMajorityLetter letter =	
		checkMajorityAutomorphisms (Set.toList (letterAtoms letter)) (letterAutomorphisms letter)

	checkMajorityAutomorphisms :: [Atom] -> [Permutation Atom] -> Bool
	checkMajorityAutomorphisms atoms automorphisms =
		checkAlphMajority rels' && checkAlphMajority rels''
		where
			maxAr = List.length atoms
			rels = 
				map 
					(\(as, s) -> Relation (Left as, Arity $ List.length as, s)) 
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

	checkAlphMajority :: [Relation RName Element] -> Bool
	checkAlphMajority rels =
		findSACSolution tstr str /= Nothing
		where
			elts = elementsFromRels rels
			
			rels' = rels ++ map (\e -> Relation (Right e, Arity 1, Set.singleton (Tuple [e]))) (Set.toList elts)
			
			str :: Structure RName Element
			str = createStructure (sigFromRels rels') elts rels'
			
			tstr :: Structure RName (Tuple Element)
			tstr =
				resetElements 
				$ foldl 
					(\tstr' e@(ar, _) -> 
						addToRelation 
							(Right e) (Arity 1)
							[Tuple [Tuple [e, e]]]
						$ addToRelation
							(Right (one ar)) (Arity 1)
							[Tuple [Tuple [e, one ar]], Tuple [Tuple [one ar, e]]] 
							tstr'
					) 
					(structPower str 2) 
					(Set.toList elts)

