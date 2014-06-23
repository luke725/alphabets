-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module UtilsTest (tests) where
	import Test.Tasty
	import Test.QuickCheck.Instances
	import Test.QuickCheck.Modifiers
	import Test.Tasty.QuickCheck as QC
	import Test.Tasty.HUnit
	
	import Data.Set(Set)
	import qualified Data.Set as Set
	
	import Utils
	
	instance Arbitrary Arity where
		arbitrary = QC.elements [Arity 0,Arity 1,Arity 2,Arity 3,Arity 4]
		shrink _  = []
		
	instance CoArbitrary a => CoArbitrary (Tuple a) where
		coarbitrary (Tuple t) = coarbitrary t
	
	tests :: TestTree
	tests = testGroup "Utils" [testCartesianPowerLength]
		
	testCartesianPowerLength = 
		QC.testProperty "cartesian power length"
		$ (\(Arity ar) set -> Set.size set < 20 QC.==> Set.null $ Set.filter (\t -> arity t /= Arity ar) $ cartesianPower (set :: Set Int) ar)
