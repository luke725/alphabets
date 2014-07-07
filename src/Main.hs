-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

import Control.Parallel.Strategies
import System.Environment
import System.Exit (ExitCode(..), exitWith)
import System.Console.GetOpt
import System.IO

import qualified Data.Map as Map
import qualified Control.Monad as Monad
import Letter
import AlphabetCSP

import Data
import Utils

		
runAll :: [Atom] -> [GroupGens] -> [(GroupGens, Bool)]
runAll _atoms sl =
	runEval (myParMap (\cl -> showRes (cl, checkMajorityAutomorphisms (ggAtoms cl) (ggElements cl))) sl)
	
run1 :: GroupGens -> (GroupGens, Bool)
run1 cl = showRes (cl, checkMajorityAutomorphisms (ggAtoms cl) (ggElements cl))
	
myParMap :: (a -> b) -> [a] -> Eval [b]
myParMap _ [] = return []
myParMap f (a:as) = do
   b <- rpar (f a)
   bs <- myParMap f as
   return (b:bs)
	
run :: Int -> IO ()
run n = do
	putStrLn $ show $ runAll (map Atom [1..n]) (s !! (n-1))
	
	
allTogether :: String -> Int -> IO ()	
allTogether path k = do
	let n = 8
	rs <- results8 path
	let standard = take k $ map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	putStrLn (show $ length standard)
	let b = findMajorityGGMany (map Atom [1..n]) standard
	case b of 
		Nothing -> putStrLn "Nothing"
		Just m ->
			Monad.foldM (\() (Tuple [x,y], z) -> putStrLn (show x ++ "; " ++ show y ++ "; " ++ show z)) () (Map.toList m)


all5 :: IO ()	
all5 = do
	let b = findMajorityGGMany (map Atom [1..5]) s5
	case b of 
		Nothing -> putStrLn "Nothing"
		Just m ->
			Monad.foldM (\() (Tuple [x,y], z) -> putStrLn (show x ++ "; " ++ show y ++ "; " ++ show z)) () (Map.toList m)	
	
	
runPart :: String -> IO ()	
runPart path = do
	let n = 8
	rs <- results8 path
	let done = map (\(w, _) -> w) rs
	putStrLn $ show $ runAll (map Atom [1..n]) $ filter (\x -> not $ elem x done) $ (s !! (n-1))
	
	
data Flag = Path String deriving (Eq)


options :: [OptDescr Flag]
options = 
	[
		Option ['p'] ["path"]       
			(ReqArg (\p -> Path p) "PATH")
			"Path to data files" 
	]
	
main :: IO ()
main = do
	args <- getArgs
	case getOpt Permute options args of
		([Path path], comm, []) ->
			case comm of
				["runPart"] -> runPart path
				["all", ks] -> allTogether path (read ks)
				_ -> dump info >> exitWith (ExitFailure 1)
		([], comm, []) ->
			case comm of
				["run", ns] -> run (read ns)
				["run1"] -> putStrLn $ show $ run1 $ getGroupGens [[[3,4]],[[5,6]],[[3,5],[4,6]],[[1,2]]]
				["all5"] -> all5
				_ -> dump info >> exitWith (ExitFailure 1)
		(_, _, errs) ->
			dump (concat errs ++ info) >> exitWith (ExitFailure 1)
	where
		dump = hPutStrLn stderr
		info = usageInfo header options
		header = "Usage: alphabets command [-p path]"

