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
	
	import Utils
	
	instance Arbitrary Arity where
		arbitrary = QC.elements [Arity 0,Arity 1,Arity 2,Arity 3,Arity 4]
		shrink _  = []
		
	instance CoArbitrary a => CoArbitrary (Tuple a) where
		coarbitrary (Tuple t) = coarbitrary t
	
	tests :: TestTree
	tests = testGroup "Utils" [testCartesianPowerLength, testRemoveDupOne, testRemoveDupDouble, testPartitionsConcat, testPartitionsSimple]
		
	testCartesianPowerLength = 
		QC.testProperty "cartesian power length"
		$ (\(Arity ar) set -> Set.size set < 20 QC.==> Set.null $ Set.filter (\t -> arity t /= Arity ar) $ cartesianPower (set :: Set Int) ar)
		
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
		$ Set.fromList (allPartitions [1,2,3]) @?= Set.fromList [[[1,2,3]], [[1],[2,3]], [[1],[2],[3]], [[1,2],[3]]]
		
