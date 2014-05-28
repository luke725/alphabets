-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module Utils where
	import Data.Set (Set)
	import qualified Data.Set as Set
	
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
