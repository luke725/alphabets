-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

import Control.Parallel.Strategies
import System.Environment
import System.Exit (ExitCode(..), exitWith)
import System.IO

import qualified Data.List as List
import qualified Math.Algebra.Group.SchreierSims as SS
import qualified Math.Algebra.Group.PermutationGroup as PG

import Utils
import Letter
import AlphabetCSP

type GroupGens = [[[Atom]]]
	
myParMap :: (a -> b) -> [a] -> Eval [b]
myParMap _ [] = return []
myParMap f (a:as) = do
   b <- rpar (f a)
   bs <- myParMap f as
   return (b:bs)
   
getGroupGens :: [[[Int]]] -> GroupGens
getGroupGens = map (map (map Atom))

ggAuto :: GroupGens -> AutomorphismGroup
ggAuto gg = (List.nub (concat $ concat gg), SS.elts (map (PG.fromCycles) gg))
	
classifyAll :: IO ()
classifyAll = do
	l <- getContents
	let rs :: [[[[Atom]]]] = map getGroupGens $ read l
	putStrLn $ show $ runEval (myParMap (\cl -> showRes (cl, checkMajorityAutomorphisms [ggAuto cl])) rs)
	
classifyOne :: IO ()
classifyOne = do
	l <- getLine
	let r :: [[[Atom]]] = getGroupGens $ read l
	putStrLn $ show $ checkMajorityAutomorphisms [ggAuto r]
	
sumOfStandard :: IO ()
sumOfStandard = do
	l <- getContents
	let rs :: [([[[Atom]]], Bool)] = map (\(x, b) -> (getGroupGens x, b)) $ read l
	let standard = map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	putStrLn $ show $ checkMajorityAutomorphisms (map ggAuto standard)

	
main :: IO ()
main = do
	args <- getArgs
	case args of
		["all"] -> classifyAll
		["one"] -> classifyOne
		["sum"] -> sumOfStandard
		_ -> dump header >> exitWith (ExitFailure 1)

	where
		dump = hPutStrLn stderr
		header = 
			"Usage: alphabets [command] \n\
			\commands: \n\
			\ all - classify all given single-orbit alphabets\n\
			\ one - classify one given single-orbit alphabet\n\
			\ sum - classify sum of all standard alphabet given at the input;\n\
			\       it takes as an input the output of [alphabets all]"

