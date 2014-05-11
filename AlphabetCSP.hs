-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module AlphabetCSP where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.Maybe as Maybe
	import qualified Control.Monad as Monad
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PG

	import RelationalStructure
	import Letter
	import ArcConsistency
	
	type Element = (Arity, Permutation Int)

	type RName = Either [[Atom]] Element

	type AStructure a = Structure RName a

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
	

	checkMajorityLetter :: Letter -> Bool
	checkMajorityLetter letter =	
		checkMajorityAutomorphisms (Set.toList (atoms letter)) (letterAutomorphisms letter)

	checkMajorityAutomorphisms :: [Atom] -> [Permutation Atom] -> Bool
	checkMajorityAutomorphisms atoms automorphisms =
		checkAlphMajority rels' && checkAlphMajority rels''
		where
			maxAr = List.length atoms
			rels = 
				map 
					(\(as, s) -> (Left as, List.length as, s)) 
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
			
			rels' = rels ++ map (\e -> (Right e, 1, Set.singleton [e])) (Set.toList elts)
			
			str :: Structure RName Element
			str = createStructure (sigFromRels rels') elts rels'
			
			tstr :: Structure RName (Tuple Element)
			tstr =
				resetElements 
				$ foldl 
					(\tstr e@(ar, _) -> 
						addToRelation 
							(Right e) 1
							[[[e, e]]]
						$ addToRelation
							(Right (one ar)) 1
							[[[e, one ar]], [[one ar, e]]] 
							tstr
					) 
					(structPower str 2) 
					(Set.toList elts)

