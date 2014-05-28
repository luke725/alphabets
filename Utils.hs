-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module Utils where
	import Debug.Trace
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import qualified Control.Monad as Monad
	
	type Tuple element = [element]

	filterToMaybe :: (a -> Bool) -> a -> Maybe a
	filterToMaybe f a =
		if f a
		then Just a
		else Nothing

	cartesian :: (Ord a) => Set (Tuple a) -> Set (Tuple a) -> Set (Tuple a)
	cartesian set1 set2 =
		Set.unions (map (\t1 -> Set.map (\t2 -> t1 ++ t2) set2) (Set.toList set1))
	
		
	cartesianPower :: (Ord a) => Set a -> Int -> Set (Tuple a)
	cartesianPower set i = 
		cartesianPower' set' i empty
		where
			empty = Set.fromList [[]]
			set' = Set.map (\a -> [a]) set
			cartesianPower' set' i tail =
				if i <= 0
				then tail
				else cartesianPower' set' (i-1) (cartesian set' tail)
				
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
				
	allJust :: [Maybe a] -> Maybe [a]
	allJust = Monad.sequence
	
	showRes :: (Show a) => a -> a
	showRes res = 
		trace (show res) res
		
	
	cube :: [a] -> [(a, a, a)]
	cube l =
		concatMap (\(as, a) -> map (\(b, c) -> (b, c, a)) (sq as)) (zz [] l)
		where
			zz _ [] = []
			zz l (h:t) =
				(h:l, h):zz (h:l) t
			sq l =
				concatMap (\x -> map (\y -> (x, y)) l) l	
	
	square :: [a] -> [(a, a)]
	square l = 
		concatMap (\(as, a) -> map (\b -> (b, a)) as) (zz [] l)
		where
			zz _ [] = []
			zz l (h:t) =
				(h:l, h):zz (h:l) t
