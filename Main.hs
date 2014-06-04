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
import Math.Algebra.Group.PermutationGroup(Permutation)
--import qualified Math.Algebra.Group.PermutationGroup as PG
--import qualified Math.Algebra.Group.SchreierSims as SS

--import RelationalStructure
import Letter
import ArcConsistency
import AlphabetCSP
import Data
import Utils
		
runAll :: [Atom] -> [GroupGens] -> [(GroupGens, Bool)]
runAll atoms sl =
	runEval (myParMap (\cl -> showRes (cl, checkMajorityAutomorphisms (ggAtoms cl) (ggElements cl))) sl)
	
myParMap :: (a -> b) -> [a] -> Eval [b]
myParMap f [] = return []
myParMap f (a:as) = do
   b <- rpar (f a)
   bs <- myParMap f as
   return (b:bs)
	
run args = do
	let n = read (List.head args)
	putStrLn $ show $ runAll [1..n] (s !! (n-1))
	
	
pairs _ = do
	let n = 6
	rs <- results6
	cl <- classes6
	let standard = map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	let pairs = 
		concatMap 
			(\(as1, as2) -> 
				map (\as' -> (as1, as')) (Maybe.fromJust $ List.find (List.elem as2) cl)
			)
			(square standard)
	let allRes = 
		runEval (myParMap 
			(\(as1, as2) -> 
				showRes ((as1, as2), checkMajorityAutomorphismsMany [1..n] [ggElements as1, ggElements as2])
			) 
			pairs)
	let negRes = map (\(ass, _) -> ass) $ filter (\(_, b) -> not b) allRes
	putStrLn $ show $ Maybe.listToMaybe negRes
	
triples _ = do
	let n = 6
	rs <- results6
	cl <- classes6
	let standard = take 15 $ map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	let triples = 
		concatMap 
			(\(as1, as2, as3) -> 
				concatMap 
					(\as3' -> map (\as2' -> (as1, as2', as3')) (Maybe.fromJust $ List.find (List.elem as2) cl)) 
					(Maybe.fromJust $ List.find (List.elem as3) cl)
			)
			(cube standard)
	let allRes = 
		runEval (myParMap 
			(\(as1, as2, as3) -> 
				showRes ((as1, as2, as3), checkMajorityAutomorphismsMany [1..n] [ggElements as1, ggElements as2, ggElements as3])
			) 
			triples)
	let negRes = map (\(ass, _) -> ass) $ filter (\(_, b) -> not b) allRes
	putStrLn $ show $ Maybe.listToMaybe negRes
	
allTogether args = do
	let n = 7
	let k = read (head args)
	rs <- results7
	let standard = take k $ map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	putStrLn (show $ length standard)
	let b = checkMajorityGGMany standard
	putStrLn (show b)
	
runPart args = do
	let n = 7
	rs <- results7
	let done = map (\(w, _) -> w) rs
	putStrLn $ show $ runAll [1..n] $ filter (\x -> not $ elem x done) $ (s !! (n-1))

	
main = do
	args <- getArgs
	case head args of
		"run" -> run (tail args)
		"runPart" -> runPart (tail args)
		"pairs" -> pairs (tail args)
		"triples" -> triples (tail args)
		"all" -> allTogether (tail args)

