-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

import Control.Parallel.Strategies
import System.Environment

import Debug.Trace

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Control.Monad as Monad
import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
import qualified Math.Algebra.Group.PermutationGroup as PG
import qualified Math.Algebra.Group.SchreierSims as SS

import RelationalStructure
import Letter
import ArcConsistency
import AlphabetCSP

triple a b c = setL[setA [a], setA[a,b], setA[a,b,c]]

letter = setL[triple 1 3 5, triple 1 4 6, triple 2 3 6, triple 2 4 5]

-- main = putStrLn $ show $ checkMajority letter

run :: [Atom] -> [[[Atom]]] -> Bool
run atoms cyclesList =
	checkMajorityAutomorphisms atoms automorphisms
	where
		automorphisms = SS.elts (map (PG.fromCycles) cyclesList)
		
runAll :: [Atom] -> [[[[Atom]]]] -> [([[[Atom]]], Bool)]
runAll atoms sl =
	runEval (myParMap (\cl -> showRes (cl, run atoms cl)) sl)
	
showRes res = 
	trace (show res) res
	
myParMap :: (a -> b) -> [a] -> Eval [b]
myParMap f [] = return []
myParMap f (a:as) = do
   b <- rpar (f a)
   bs <- myParMap f as
   return (b:bs)
	
main = do
	args <- getArgs
	let n = read (List.head args)
	putStrLn $ show $ runAll [1..n] (s !! (n-1))
	
main' =
	putStrLn $ show $ run [1..5] [ [[3,4,5]], [[4,5]] ]

s :: [[[[[Atom]]]]]
s = [s1, s2, s3, s4, s5, s6, s7]

s1 :: [[[[Atom]]]]
s1 = [ [  ] ]

s2 :: [[[[Atom]]]]
s2 = [ [ [[]] ], [ [[1,2]] ] ]

s3 :: [[[[Atom]]]]
s3 = [ [  ], [ [[2,3]] ], [ [[1,2,3]] ], [ [[1,2,3]], [[2,3]] ] ]

s4 :: [[[[Atom]]]]
s4 = [ [  ], [ [[1,3],[2,4]] ], [ [[3,4]] ], [ [[2,4,3]] ], [ [[1,4],[2,3]], [[1,3],[2,4]] ], 
  [ [[3,4]], [[1,2],[3,4]] ], [ [[1,3,2,4]], [[1,2],[3,4]] ], [ [[3,4]], [[2,4,3]] ], 
  [ [[1,4],[2,3]], [[1,3],[2,4]], [[3,4]] ], [ [[1,4],[2,3]], [[1,3],[2,4]], [[2,4,3]] ], 
  [ [[1,4],[2,3]], [[1,3],[2,4]], [[2,4,3]], [[3,4]] ] ]
  
s5 :: [[[[Atom]]]]
s5 = [ [  ], [ [[4,5]] ], [ [[2,3],[4,5]] ], [ [[3,4,5]] ], [ [[2,3],[4,5]], [[2,4],[3,5]] ], 
  [ [[2,3],[4,5]], [[2,4,3,5]] ], [ [[4,5]], [[2,3]] ], [ [[1,2,3,4,5]] ], 
  [ [[3,4,5]], [[4,5]] ], [ [[3,4,5]], [[1,2],[4,5]] ], [ [[4,5]], [[1,2,3]] ], 
  [ [[4,5]], [[2,3]], [[2,4],[3,5]] ], [ [[1,2,3,4,5]], [[2,5],[3,4]] ], 
  [ [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]] ], [ [[4,5]], [[1,2,3]], [[2,3]] ], 
  [ [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4]] ], 
  [ [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5]] ], [ [[1,2,3,4,5]], [[3,4,5]] ], 
  [ [[1,2,3,4,5]], [[1,2]] ] ]


s6 :: [[[[Atom]]]]
s6 = [ [  ], [ [[5,6]] ], [ [[1,2],[3,4],[5,6]] ], [ [[3,4],[5,6]] ], [ [[4,5,6]] ], 
  [ [[1,2,3],[4,5,6]] ], [ [[3,4],[5,6]], [[1,2],[5,6]] ], [ [[3,4],[5,6]], [[3,5],[4,6]] ], 
  [ [[3,4],[5,6]], [[1,2],[3,5,4,6]] ], [ [[3,4],[5,6]], [[1,2],[3,5],[4,6]] ], 
  [ [[3,4],[5,6]], [[3,5,4,6]] ], [ [[5,6]], [[3,4]] ], [ [[5,6]], [[1,2],[3,4]] ], 
  [ [[2,3,4,5,6]] ], [ [[1,2,3],[4,5,6]], [[1,4],[2,6],[3,5]] ], [ [[4,5,6]], [[5,6]] ], 
  [ [[4,5,6]], [[2,3],[5,6]] ], [ [[1,2,3],[4,5,6]], [[2,3],[5,6]] ], 
  [ [[1,2],[3,4],[5,6]], [[1,3,5],[2,4,6]] ], [ [[5,6]], [[2,3,4]] ], 
  [ [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]] ], [ [[5,6]], [[3,4]], [[1,2]] ], 
  [ [[5,6]], [[3,4]], [[1,2],[3,5],[4,6]] ], [ [[5,6]], [[3,4]], [[3,5],[4,6]] ], 
  [ [[3,4],[5,6]], [[3,5],[4,6]], [[1,2],[5,6]] ], 
  [ [[3,4],[5,6]], [[3,5,4,6]], [[1,2],[5,6]] ], [ [[5,6]], [[1,2],[3,4]], [[1,3,2,4]] ], 
  [ [[4,5,6]], [[1,2,3]] ], [ [[2,3,4,5,6]], [[3,6],[4,5]] ], 
  [ [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]] ], 
  [ [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]] ], [ [[5,6]], [[2,3,4]], [[3,4]] ], 
  [ [[1,2],[3,4],[5,6]], [[1,3,5],[2,4,6]], [[3,5],[4,6]] ], 
  [ [[3,4]], [[5,6]], [[3,5],[4,6]], [[1,2]] ], [ [[4,5,6]], [[1,2,3]], [[2,3],[5,6]] ], 
  [ [[4,5,6]], [[1,2,3]], [[1,4],[2,5],[3,6]] ], [ [[4,5,6]], [[5,6]], [[1,2,3]] ], 
  [ [[2,3,4,5,6]], [[3,6],[4,5]], [[3,4,6,5]] ], 
  [ [[5,6]], [[3,4]], [[1,2]], [[1,3,5],[2,4,6]] ], 
  [ [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
  [ [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]], [[1,2],[5,6]] ], 
  [ [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]], [[3,5],[4,6]] ], 
  [ [[3,4],[5,6]], [[1,2],[5,6]], [[1,3,5],[2,4,6]], [[3,5,4,6]] ], 
  [ [[3,4],[5,6]], [[3,5],[4,6]], [[4,5,6]], [[5,6]] ], 
  [ [[4,5,6]], [[5,6]], [[1,2,3]], [[2,3]] ], 
  [ [[4,5,6]], [[1,2,3]], [[2,3],[5,6]], [[1,4],[2,5],[3,6]] ], 
  [ [[4,5,6]], [[1,2,3]], [[2,3],[5,6]], [[1,4],[2,5,3,6]] ], 
  [ [[5,6]], [[3,4]], [[1,2]], [[1,4,5],[2,3,6]], [[3,5],[4,6]] ], 
  [ [[5,6]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], [ [[1,2,3,4,5]], [[3,4,5]] ],
  [ [[1,2,3,4,6]], [[1,4],[5,6]] ], 
  [ [[4,6,5]], [[4,5]], [[1,2,3]], [[2,3]], [[1,4],[2,5],[3,6]] ], 
  [ [[1,5,4,3,2]], [[2,4,3]], [[4,5]] ], [ [[1,5,3,6,4]], [[1,6],[2,4]], [[3,4,6,5]] ], 
  [ [[1,2,3,4,5]], [[4,5,6]] ], [ [[1,2,3,4,5,6]], [[1,2]] ] ]
  
s7 :: [[[[Atom]]]]
s7 = [ [  ], [ [[6,7]] ], [ [[4,5],[6,7]] ], [ [[2,3],[4,5],[6,7]] ], [ [[5,6,7]] ], 
  [ [[2,3,4],[5,6,7]] ], [ [[4,5],[6,7]], [[4,6],[5,7]] ], [ [[4,5],[6,7]], [[2,3],[6,7]] ], 
  [ [[6,7]], [[4,5]] ], [ [[4,5],[6,7]], [[4,6,5,7]] ], [ [[4,5],[6,7]], [[2,3],[4,6,5,7]] ],
  [ [[4,5],[6,7]], [[2,3],[4,6],[5,7]] ], [ [[6,7]], [[2,3],[4,5]] ], [ [[3,4,5,6,7]] ], 
  [ [[5,6,7]], [[6,7]] ], [ [[5,6,7]], [[1,2],[3,4]] ], [ [[5,6,7]], [[1,2],[3,4],[6,7]] ], 
  [ [[2,3,4],[5,6,7]], [[2,5],[3,7],[4,6]] ], [ [[5,6,7]], [[3,4],[6,7]] ], 
  [ [[6,7]], [[3,4,5]] ], [ [[2,3],[4,5],[6,7]], [[2,4,6],[3,5,7]] ], 
  [ [[2,3,4],[5,6,7]], [[3,4],[6,7]] ], [ [[1,2,3,4,5,6,7]] ], 
  [ [[6,7]], [[2,3],[4,5]], [[2,4],[3,5]] ], [ [[6,7]], [[4,5]], [[2,3]] ], 
  [ [[6,7]], [[4,5]], [[4,6],[5,7]] ], [ [[6,7]], [[2,3],[4,5]], [[2,4,3,5]] ], 
  [ [[4,5],[6,7]], [[4,6,5,7]], [[2,3],[6,7]] ], [ [[6,7]], [[4,5]], [[2,3],[4,6],[5,7]] ], 
  [ [[4,5],[6,7]], [[4,6],[5,7]], [[2,3],[6,7]] ], [ [[5,6,7]], [[2,3,4]] ], 
  [ [[3,4,5,6,7]], [[1,2],[4,7],[5,6]] ], [ [[3,4,5,6,7]], [[4,7],[5,6]] ], 
  [ [[6,7]], [[1,2,3,4,5]] ], [ [[4,5],[6,7]], [[4,6],[5,7]], [[5,6,7]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]] ], 
  [ [[4,5],[6,7]], [[4,6],[5,7]], [[1,2,3],[5,6,7]] ], [ [[6,7]], [[4,5]], [[1,2,3]] ], 
  [ [[4,5],[6,7]], [[2,3],[6,7]], [[2,4,6],[3,5,7]] ], 
  [ [[5,6,7]], [[3,4],[6,7]], [[1,2],[6,7]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4],[6,7]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3,2,4],[6,7]] ], [ [[5,6,7]], [[6,7]], [[1,2],[3,4]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3,2,4]] ], [ [[6,7]], [[3,4,5]], [[4,5]] ], 
  [ [[6,7]], [[3,4,5]], [[1,2],[4,5]] ], 
  [ [[2,3],[4,5],[6,7]], [[2,4,6],[3,5,7]], [[4,6],[5,7]] ], 
  [ [[1,2,3,4,5,6,7]], [[2,7],[3,6],[4,5]] ], [ [[4,5]], [[6,7]], [[4,6],[5,7]], [[2,3]] ], 
  [ [[5,6,7]], [[2,3,4]], [[3,4],[6,7]] ], [ [[5,6,7]], [[2,3,4]], [[2,5],[3,6],[4,7]] ], 
  [ [[5,6,7]], [[6,7]], [[2,3,4]] ], [ [[3,4,5,6,7]], [[4,7],[5,6]], [[1,2],[4,5,7,6]] ], 
  [ [[6,7]], [[1,2,3,4,5]], [[2,5],[3,4]] ], [ [[3,4,5,6,7]], [[4,7],[5,6]], [[4,5,7,6]] ], 
  [ [[1,2,3,4,5,6,7]], [[2,3,5],[4,7,6]] ], 
  [ [[4,5],[6,7]], [[4,6],[5,7]], [[5,6,7]], [[6,7]] ], 
  [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3],[2,4]] ], [ [[6,7]], [[4,5]], [[1,2,3]], [[2,3]] ]
    , [ [[4,5]], [[6,7]], [[4,6],[5,7]], [[1,2,3]] ], 
  [ [[5,6,7]], [[3,4],[6,7]], [[1,2],[6,7]], [[1,3],[2,4],[6,7]] ], 
  [ [[6,7]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]] ], 
  [ [[4,5],[6,7]], [[2,3],[6,7]], [[2,4,6],[3,5,7]], [[4,6,5,7]] ], 
  [ [[6,7]], [[4,5]], [[2,3]], [[2,4,6],[3,5,7]] ], 
  [ [[6,7]], [[4,5]], [[1,2,3]], [[2,3],[4,6],[5,7]] ], 
  [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3,2,4]] ], 
  [ [[5,6,7]], [[3,4],[6,7]], [[1,2],[6,7]], [[1,3],[2,4]] ], 
  [ [[4,5],[6,7]], [[4,6],[5,7]], [[5,6,7]], [[2,3],[6,7]] ], 
  [ [[4,5],[6,7]], [[2,3],[6,7]], [[2,4,6],[3,5,7]], [[4,6],[5,7]] ], 
  [ [[4,5],[6,7]], [[4,6],[5,7]], [[1,2,3],[5,6,7]], [[2,3],[6,7]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
  [ [[5,6,7]], [[2,3,4]], [[3,4],[6,7]], [[2,5],[3,6],[4,7]] ], 
  [ [[5,6,7]], [[6,7]], [[2,3,4]], [[3,4]] ], 
  [ [[5,6,7]], [[2,3,4]], [[3,4],[6,7]], [[2,5],[3,6,4,7]] ], 
  [ [[6,7]], [[1,2,3,4,5]], [[2,5],[3,4]], [[2,3,5,4]] ], 
  [ [[1,2,3,4,5,6,7]], [[2,3,5],[4,7,6]], [[2,7],[3,6],[4,5]] ], 
  [ [[6,7]], [[2,3],[4,5]], [[2,4],[3,5]], [[3,4,5]], [[4,5]] ], 
  [ [[4,5]], [[6,7]], [[4,6],[5,7]], [[1,2,3]], [[2,3]] ], 
  [ [[6,7]], [[4,5]], [[2,3]], [[2,5,6],[3,4,7]], [[4,6],[5,7]] ], 
  [ [[1,2,3,4,5]], [[3,4,5]] ], [ [[1,2,3,4,6]], [[1,4],[5,6]] ], 
  [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], 
  [ [[5,6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4],[6,7]] ], 
  [ [[5,7,6]], [[5,6]], [[2,4,3]], [[3,4]], [[2,5],[3,6],[4,7]] ], 
  [ [[1,2,3,4,5]], [[3,4,5]], [[6,7]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[4,5]] ], 
  [ [[1,2,3,4,5]], [[3,4,5]], [[4,5],[6,7]] ], [ [[1,5,3,6,4]], [[1,6],[2,4]], [[3,4,6,5]] ]
    , [ [[5,6,7]], [[6,7]], [[1,2],[3,4]], [[1,3],[2,4]], [[2,3,4]], [[3,4]] ], 
  [ [[1,2,3,4,5,6,7]], [[1,2],[3,6]] ], [ [[1,2,3,4,5]], [[3,4,5]], [[6,7]], [[4,5]] ], 
  [ [[1,2,3,4,5]], [[4,5,6]] ], [ [[1,6,5,4,3]], [[2,4,3]], [[5,6]] ], 
  [ [[1,2,3,4,5,6,7]], [[5,6,7]] ], [ [[1,2,3,4,5,6,7]], [[1,2]] ] ]

