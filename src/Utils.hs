-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module Utils where
	import Debug.Trace
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.List as List
	import qualified Control.Monad as Monad
	import Math.Algebra.Group.PermutationGroup(Permutation)
	import qualified Math.Algebra.Group.PermutationGroup as PG
	import Data.Foldable(foldlM)

	newtype Arity = Arity Int deriving (Show, Eq, Ord)	
	
	newtype Tuple element = Tuple [element] deriving (Show, Eq, Ord)
	
	fixPoint :: (Eq a) => (a -> a) -> a -> a
	fixPoint f a =
		if a == f a then a else fixPoint f (f a)
		
	fixPointM :: (Monad m, Eq a) => (a -> m a) -> a -> m a
	fixPointM f a = do
		a' <- f a
		if a == a' then return a else fixPointM f a'
	
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
				
	partPreservesOrbits :: (Eq a) => [[a]] -> [[a]] -> Bool
	partPreservesOrbits orbits part =
		all (\p -> any (\o -> all (\pe -> List.elem pe o) p) orbits) part
		
	allPermPartPreserveOrbits :: (Ord a, Eq a) => [Permutation a] -> [a] -> Set ([[a]])
	allPermPartPreserveOrbits g l =
		Set.filter (partPreservesOrbits (PG.orbits g)) (allPart2 l)

				
	allJust :: [Maybe a] -> Maybe [a]
	allJust = Monad.sequence
	
	
	showRes :: (Show a) => a -> a
	showRes res = 
		trace (show res) res

		
	-- remove duplicate elements
	removeDup :: (Ord a, Ord b) => Map a b -> Map a b
	removeDup m =
		Map.fromList 
		$ map (\(b, a) -> (a, b)) 
		$ Map.toList 
		$ Map.fromList 
		$ map (\(a, b) -> (b, a)) 
		$ Map.toList m
	
	conjClassRep :: (Ord a) => Set a -> Permutation a -> Permutation a
	conjClassRep elts p =
		PG.fromCycles $ fst 
		$ foldl 
			(\(r, elts') l -> (take l elts':r, drop l elts'))
			([], Set.toList elts)
			conjClass
		where
			conjClass = List.reverse $ List.sort $ map length $ PG.toCycles p
			
			
	tr :: (Show a) => a -> a
	tr a = trace (show a) a
	
	
	allPartL :: [a] -> [[[a]]]
	allPartL l = do
		(le, nle) <- leaders
		let n = length le
		let leMap = Map.fromList (zip [1..n] le)
		nleMap <- foldlM (\m e -> do {i <- [1..n]; return (Map.insertWith (++) i [e] m)}) Map.empty nle
		let allMap = Map.mapWithKey (\i le' -> (le', Map.findWithDefault [] i nleMap)) leMap
		let allVal = Map.elems allMap
		mapM (\(le', nles) -> do {p <- List.permutations nles; return (le':p)}) allVal	
		where
			leaders = foldlM (\(le, nle) e -> [(e:le, nle), (le, e:nle)]) ([], []) l
			
	allPart2 :: (Ord a) => [a] -> Set [[a]]
	allPart2 l = Set.fromList (allPartL l)
	
	firstTuple :: [Set v] -> Maybe (Tuple v)
	firstTuple [] = Just (Tuple [])
	firstTuple (hs:ts) = 
		if Set.size hs == 0
		then Nothing 
		else 
			case firstTuple ts of
				Just (Tuple r) -> Just (Tuple (Set.findMin hs : r))
				Nothing -> Nothing
	
	
	nextTuple :: (Ord v) => [Set v] -> Tuple v -> Maybe (Tuple v)
	
	nextTuple [] (Tuple []) = Just (Tuple [])
	
	nextTuple [hs] (Tuple [ht]) =
		let (_, _, ls) = Set.splitMember ht hs in firstTuple [ls]	
	
	nextTuple (hs:ts) (Tuple (ht:tt)) =
		case Set.splitMember ht hs of
			(_, False, ls) -> firstTuple (ls:ts)
			(_, True, ls) ->
				case nextTuple ts (Tuple tt) of
					Just (Tuple rt) -> Just (Tuple (ht:rt))
					Nothing -> firstTuple (ls:ts)

	nextTuple [] (Tuple (_:_)) = error ("Unexpected pattern in nextTuple")

	nextTuple (_:_) (Tuple []) = error ("Unexpected pattern in nextTuple")

