-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module UtilsTest (tests) where
	import Test.Tasty
	import Test.QuickCheck.Instances
	import Test.QuickCheck.Modifiers
	import Test.Tasty.QuickCheck as QC
	import Test.Tasty.HUnit
	
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map)
	import qualified Data.Map as Map
	import qualified Data.List as List
	
	import Utils
	
	instance Arbitrary Arity where
		arbitrary = QC.elements [Arity 0,Arity 1,Arity 2,Arity 3,Arity 4]
		shrink _  = []
		
	instance CoArbitrary a => CoArbitrary (Tuple a) where
		coarbitrary (Tuple t) = coarbitrary t
	
	tests :: TestTree
	tests = testGroup "Utils" [testCartesianPowerLength, testRemoveDupOne, testRemoveDupDouble, testPartitionsConcat, testPartitionsSimple, testPartitions2Concat, testPartitions2Simple, testAllTuples]
		
	testCartesianPowerLength = 
		QC.testProperty "cartesian power length"
		$ (\(Arity ar) (set :: Set Int) -> 
			Set.size set < 20 QC.==> 
			Set.null $ Set.filter (\t -> arity t /= Arity ar) $ cartesianPower set ar
		)
		
	testRemoveDupOne = 
		QC.testProperty "removeDup for one"
		$ (\(keys :: [Int]) (val :: Char) ->
			length keys > 0 QC.==> 
			let m = removeDup $ Map.fromList $ map (\k -> (k, val)) keys 
			in Map.size m == 1 && Map.elems m == [val]
		)
		
	testRemoveDupDouble =
		QC.testProperty "removeDup for doubled"
		$ (\(m :: Map Int Char) -> 
			let m' = removeDup $ Map.union (Map.mapKeys Left m) (Map.mapKeys Right m) 
			in Map.size m' == Map.size (removeDup m) && Set.fromList (Map.elems m') == Set.fromList (Map.elems $ removeDup m)
		)
		
	testPartitionsConcat =
		QC.testProperty "allPartitions and concat"
		$ (\(l :: [Int]) ->
			length l < 7 QC.==> all (\p -> l == concat p) (allPartitions l)
		)
		
	testPartitionsSimple =
		testCase "example for allPartitions"
		$ List.sort (allPartitions [1,2,3]) @?= List.sort [[[1,2,3]], [[1],[2,3]], [[1],[2],[3]], [[1,2],[3]]]

	testPartitions2Concat =
		QC.testProperty "allPartAndPerms and concat"
		$ (\(l :: [Int]) ->
			length l < 7 QC.==> all (\p -> Set.fromList l == foldl (\s e -> Set.union s (Set.fromList e)) Set.empty p) (Set.toList $ allPartAndPerms l)
		)
		
	testPartitions2Simple =
		testCase "example for allPartAndPerms"
		$ Set.map List.sort (allPartAndPerms [1,2,3]) @?= Set.map List.sort (Set.fromList [[[1,2,3]], [[2,1,3]], [[2,3,1]], [[1,3,2]], [[3,1,2]], [[3,2,1]], [[1],[2,3]], [[1],[2],[3]], [[1,2],[3]], [[2],[1,3]], [[2,1],[3]], [[2],[3,1]], [[1],[3,2]]])
		
	allTuples :: (Ord v) => [Set v] -> [Tuple v]
	allTuples s =
		case firstTuple s of
			Just t  -> t : allNextTuples t
			Nothing -> []
		where
			allNextTuples t =
				case nextTuple s t of
					Just t' -> t' : allNextTuples t'
					Nothing -> []
		
		
	testAllTuples =
		testCase "all tuples"
		$ allTuples [Set.fromList [1,2], Set.fromList [3], Set.fromList [4,5]] @?= [Tuple [1,3,4], Tuple [1,3,5], Tuple [2,3,4], Tuple [2,3,5]]
		
