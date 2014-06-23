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
	
	instance Arbitrary Arity where
		arbitrary = QC.elements [Arity 0,Arity 1,Arity 2,Arity 3,Arity 4]
		shrink _  = []
		
	instance CoArbitrary a => CoArbitrary (Tuple a) where
		coarbitrary (Tuple t) = coarbitrary t
		
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
	tests = testGroup "RelationalStructure" [testCartesianPowerLength, testRelation, testStructure, testAutomorphism, testSubstructure, testPowerStructure]
	
	testCartesianPowerLength = 
		QC.testProperty "cartesian power length"
		$ (\(Arity ar) set -> Set.size set < 20 QC.==> Set.null $ Set.filter (\t -> arity t /= Arity ar) $ cartesianPower (set :: Set Int) ar)
		
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

