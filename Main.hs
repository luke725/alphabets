-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

import Control.Parallel.Strategies
import System.Environment

import Debug.Trace

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Map (Map, (!))
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
import Data

triple a b c = setL[setA [a], setA[a,b], setA[a,b,c]]

letter = setL[triple 1 3 5, triple 1 4 6, triple 2 3 6, triple 2 4 5]

-- main = putStrLn $ show $ checkMajority letter

run :: [Atom] -> [[[Atom]]] -> Bool
run atoms cyclesList =
	checkMajorityAutomorphisms atoms automorphisms
	where
		automorphisms = SS.elts (map (PG.fromCycles) cyclesList)
		
run2 :: [Atom] -> [[[Atom]]] -> [[[Atom]]] -> Bool
run2 atoms cyclesList1 cyclesList2 =
	checkMajorityAutomorphismsMany atoms [autos1, autos2]
	where
		autos1 = SS.elts (map (PG.fromCycles) cyclesList1)
		autos2 = SS.elts (map (PG.fromCycles) cyclesList2)
		
runAll :: [Atom] -> [[[[Atom]]]] -> [([[[Atom]]], Bool)]
runAll atoms sl =
	runEval (myParMap (\cl -> showRes (cl, run atoms cl)) sl)
	
showRes res = 
	trace (show res) res
	
myZz :: [a] -> [(a, a)]
myZz l = 
	concatMap (\(as, a) -> map (\b -> (b, a)) as) (zz [] l)
	where
		zz _ [] = []
		zz l (h:t) =
			(l, h):zz (h:l) t
	
myParMap :: (a -> b) -> [a] -> Eval [b]
myParMap f [] = return []
myParMap f (a:as) = do
   b <- rpar (f a)
   bs <- myParMap f as
   return (b:bs)
	
main'' = do
	args <- getArgs
	let n = read (List.head args)
	putStrLn $ show $ runAll [1..n] (s !! (n-1))
	
main' =
	putStrLn $ show $ run [1..5] [ [[3,4,5]], [[4,5]] ]
	
main = do
	let n = 6
	l <- readFile "all8.txt"
	clf <- readFile "data6.txt"
	let rs :: [([[[Atom]]], Bool)] = read l
	let cl :: [[[[[Atom]]]]] = read clf
--	let clMap = Map.fromList $ map (\c -> (List.head c, c)) cl
	let z = map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	let zzt = concatMap (\(as1, as2) -> map (\as' -> (as1, as')) (Maybe.fromJust $ List.find (elem as2) cl)) $ myZz z
	let zz = runEval (myParMap (\(as1, as2) -> showRes ((as1, as2), run2 [1..n] as1 as2)) zzt)
	let z2 = map (\(ass, _) -> ass) $ filter (\(_, b) -> not b) zz
	putStrLn $ show $ Maybe.listToMaybe z2

