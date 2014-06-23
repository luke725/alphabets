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
	
	tests :: TestTree
	tests = testGroup "RelationalStructure" [testCartesianPowerLength]
	
	testCartesianPowerLength = 
		QC.testProperty "cartesian power length"
		$ QC.forAll (QC.elements [0,1,2,3,4])
		$ (\ar set -> Set.size set < 20 QC.==> Set.null $ Set.filter (\t -> arity t /= Arity ar) $ cartesianPower (set :: Set Int) ar)
		
