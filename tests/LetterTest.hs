-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module LetterTest (tests) where
	import Test.Tasty
	import Test.QuickCheck.Instances
	import Test.QuickCheck.Modifiers
	import Test.Tasty.QuickCheck as QC
	import Test.Tasty.HUnit
	
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map)
	import qualified Data.Map as Map
	
	import Letter

	
	genLetterLimitedDepth :: Int -> Gen Letter
	genLetterLimitedDepth depth = do
		b <- arbitrary
		if b && depth > 0
		then do
			l <- QC.listOf (genLetterLimitedDepth (depth-1))
			return (LSet $ Set.fromList l)
		else do
			a <- arbitrary
			return (LAtom a)
			
			
	instance Arbitrary Atom where
		arbitrary =
			QC.elements [Atom 0, Atom 1, Atom 2, Atom 3, Atom 4]
		shrink _  = []
		
		
	instance Arbitrary Letter where
		arbitrary = genLetterLimitedDepth 3
		shrink _  = []
	
	
	
	tests :: TestTree
	tests = testGroup "Letter" [testLetterAutomorphisms]
	
	testLetterAutomorphisms =
		QC.testProperty "letter automorphisms"
		$ (\(l :: Letter) -> all (\a -> isAutomorphism l a) (letterAutomorphisms l))
