-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

import Test.Tasty

import qualified RelationalStructureTest as RelationalStructureTest
import qualified UtilsTest as UtilsTest
import qualified LetterTest as LetterTest

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Unit Tests" [RelationalStructureTest.tests, UtilsTest.tests, LetterTest.tests]
