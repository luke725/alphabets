-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module RelationalStructureTest (tests) where
	import Test.Tasty
	import Test.QuickCheck.Instances
	import Test.QuickCheck.Modifiers
	import Test.Tasty.QuickCheck as QC
	import Test.Tasty.HUnit
	
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Debug.Trace
	
	import RelationalStructure
	import Utils
	import UtilsTest hiding (tests)
		
	genFun :: (Arbitrary rname, Arbitrary element, CoArbitrary element, Ord element) => Gen (Set element -> Relation rname element)
	genFun = do
		rname <- arbitrary
		ar <- arbitrary
		f <- arbitrary	
		return (\elts -> createRelation rname ar elts f)
		
	instance (Arbitrary rname, Arbitrary element, CoArbitrary element, Ord element) => Arbitrary (Relation rname element) where
		arbitrary = do
			f <- genFun
			elts <- arbitrary `suchThat` (\s -> Set.size s < 10)
			return (f elts)
		shrink _ = []
			
	instance (Arbitrary rname, Arbitrary element, CoArbitrary element, Ord element, Ord rname) => Arbitrary (Structure rname element) where
		arbitrary = do
			elts <- arbitrary `suchThat` (\s -> Set.size s < 10)
			relNum <- QC.elements [1,2,3,4,5]
			fs <- QC.vectorOf relNum genFun
			let rels = map (\f -> f elts) fs
			let sig = sigFromRels rels
			return (createStructure sig elts rels)
	
	
	
	
	tests :: TestTree
	tests = testGroup "RelationalStructure" [testRelation, testStructure, testAutomorphism, testSubstructure, testPowerStructure]
		
	testRelation = QC.testProperty "check relation" 
		(forAll (genFun :: Gen (Set Int -> Relation Char Int)) (\f elts -> Set.size elts < 10 QC.==> checkRelation elts (f elts)))
		
	testStructure = QC.testProperty "check structure" (checkStructure :: Structure Char Int -> Bool)
	
	testAutomorphism = QC.testProperty "check automorphism" (\(str :: Structure Char Int) -> isHomomorphism str str id)
	
	testSubstructure = 
		QC.testProperty "check automorphism" 
			(\(fsub :: Int -> Bool) (str :: Structure Char Int) -> 
				let substr = substructure str (Set.filter fsub $strElements str) 
				in isHomomorphism substr str id)
				
	testPowerStructure =
		QC.testProperty "power structure" 
			(\(str :: Structure Char Int) ->
				Set.size (strElements str) < 5 QC.==>
				let p = structPower str 2 in
				isHomomorphism p str (\(Tuple [e, _]) -> e)
				&& isHomomorphism p str (\(Tuple [e, _]) -> e)
				&& isHomomorphism str p (\e -> Tuple [e, e]))

