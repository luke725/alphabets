-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module Utils where
	import Debug.Trace
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.List as List
	import qualified Control.Monad as Monad

	newtype Arity = Arity Int deriving (Show, Eq, Ord)	
	
	newtype Tuple element = Tuple [element] deriving (Show, Eq, Ord)
	
	arity :: Tuple a -> Arity
	arity (Tuple t) = Arity (length t)
	
	mapTuple :: (a -> b) -> Tuple a -> Tuple b
	mapTuple f (Tuple t) = Tuple (map f t)

	filterToMaybe :: (a -> Bool) -> a -> Maybe a
	filterToMaybe f a =
		if f a
		then Just a
		else Nothing

	cartesian :: (Ord a) => Set (Tuple a) -> Set (Tuple a) -> Set (Tuple a)
	cartesian set1 set2 =
		Set.unions (map (\(Tuple t1) -> Set.map (\(Tuple t2) -> Tuple (t1 ++ t2)) set2) (Set.toList set1))
	
		
	cartesianPower :: (Ord a) => Set a -> Int -> Set (Tuple a)
	cartesianPower set i = 
		cartesianPower' set' i empty
		where
			empty = Set.fromList [Tuple []]
			set' = Set.map (\a -> Tuple [a]) set
			cartesianPower' set'' j tl =
				if j <= 0
				then tl
				else cartesianPower' set'' (j-1) (cartesian set'' tl)
				
	-- all possible partitions of a list
	-- for example
	-- allPartitions [1,2,3] = [[[1,2,3]], [[1],[2,3]], [[1],[2],[3]], [[1,2],[3]]] up to order
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
			zz l' (h:t) =
				(h:l', h):zz (h:l') t
			sq l' =
				concatMap (\x -> map (\y -> (x, y)) l') l'	
	
	square :: [a] -> [(a, a)]
	square l = 
		concatMap (\(as, a) -> map (\b -> (b, a)) as) (zz [] l)
		where
			zz _ [] = []
			zz l' (h:t) =
				(h:l', h):zz (h:l') t
				
	removeDup :: (Ord a, Ord b) => Map a b -> Map a b
	removeDup m =
		Map.fromList 
		$ map (\(b, a) -> (a, b)) 
		$ Map.toList 
		$ Map.fromList 
		$ map (\(a, b) -> (b, a)) 
		$ Map.toList m

