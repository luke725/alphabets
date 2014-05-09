-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module Letter where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.Maybe as Maybe
	import qualified Control.Monad as Monad
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PermutationGroup

	import RelationalStructure (Tuple)
	
	type Atom = Int
	
	data Letter = LSet (Set Letter) | LAtom Atom deriving (Show, Ord, Eq)
	
	
	setL :: [Letter] -> Letter
	setL letters = LSet (Set.fromList letters)
	
	setA :: [Atom] -> Letter
	setA ats = setL (map LAtom ats)
	
	atoms :: Letter -> Set Atom
	atoms (LAtom a) = Set.singleton a
	atoms (LSet set) = Set.unions (map atoms (Set.toList set))
	
	isAutomorphism :: Letter -> Permutation Atom -> Bool
	isAutomorphism letter f =
		applyAutomorphism f letter == letter
		where
			applyAutomorphism f (LAtom a) = LAtom (a .^ f)
			applyAutomorphism f (LSet set) = LSet (Set.map (applyAutomorphism f) set)
	
	letterAutomorphisms :: Letter -> [Permutation Atom]
	letterAutomorphisms letter =
		filter (isAutomorphism letter) allPermutations
		where
			ats = Set.toList (atoms letter)
			allPermutations =
				map 
					(\perm -> PermutationGroup.fromPairs (zip ats perm)) 
					(List.permutations ats)
		
			
	allPartitions :: [a] -> [[[a]]]
	allPartitions l =
		allPartitions' l [] []
		where
			allPartitions' :: [a] -> [a] -> [[a]] -> [[[a]]]
			allPartitions' [] [] sol = [reverse sol]
			allPartitions' [] (ha:ta) sol = [reverse (reverse (ha:ta) : sol)]
			allPartitions' (h:t) [] sol = allPartitions' t [h] sol
			allPartitions' (h:t) (ha:ta) sol =
				allPartitions' t (h:ha:ta) sol
				++ allPartitions' (h:t) [] (reverse (ha:ta) : sol)

	allPermPart :: (Ord a) => [a] -> Set ([[a]])
	allPermPart l =
		Set.fromList 
			(concatMap 
				(\p -> map List.sort (allPartitions p)) 
				(List.permutations l))
				
			
	automorphismPreservesPartition :: [[Atom]] -> Permutation Atom -> Bool
	automorphismPreservesPartition part f =
		all (\set -> set == Set.map (\a -> a .^ f) set) partSets
		where
			partSets = map Set.fromList part
		
	allJust :: [Maybe a] -> Maybe [a]
	allJust = Monad.sequence	
	
	translateAutomorphism :: [[Atom]] -> Permutation Atom -> Maybe (Tuple (Int, Permutation Int))
	translateAutomorphism part f = 
		allJust (map permute part)
		where
			permute :: [Atom] -> Maybe (Int, Permutation Int)
			permute p =
				case allJust (map (\e -> List.elemIndex e pp) p) of
					Just l  -> Just (List.length l, PermutationGroup.fromList l)
					Nothing -> Nothing
				where
					pp = map (\a -> a .^ f) p

	letterRelations :: Letter -> Map [[Atom]] (Set (Tuple (Int, Permutation Int)))
	letterRelations letter =
		removeDup
		$ Map.fromList
		$ map
			(\part -> (part, Set.fromList (Maybe.mapMaybe (translateAutomorphism part) automorphisms)))
			partitions
		where
			automorphisms = letterAutomorphisms letter
			partitions = Set.toList (allPermPart (Set.toList (atoms letter)))
			
			removeDup :: (Ord a, Ord b) => Map a b -> Map a b
			removeDup m =
				Map.fromList 
				$ map (\(b, a) -> (a, b)) 
				$ Map.toList 
				$ Map.fromList 
				$ map (\(a, b) -> (b, a)) 
				$ Map.toList m
