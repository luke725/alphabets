-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

import Control.Parallel.Strategies
import System.Environment

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
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
	
run :: [String] -> IO ()
run args = do
	let n = read (List.head args)
	putStrLn $ show $ runAll [1..n] (s !! (n-1))

runPairs :: [String] -> IO ()	
runPairs _ = do
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
	
runTriples :: [String] -> IO ()	
runTriples _ = do
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
	
allTogether :: [String] -> IO ()	
allTogether args = do
	let k = read (head args)
	rs <- results7
	let standard = take k $ map (\(as, _) -> as) $ filter (\(_, b) -> b) rs
	putStrLn (show $ length standard)
	let b = findMajorityGGMany standard
	case b of 
		Nothing -> putStrLn "Nothing"
		Just m ->
			Monad.foldM (\() ([x,y], z) -> putStrLn (show x ++ "; " ++ show y ++ "; " ++ show z)) () (Map.toList m)

all5 :: [String] -> IO ()	
all5 _ = do
	let b = findMajorityGGMany s5
	case b of 
		Nothing -> putStrLn "Nothing"
		Just m ->
			Monad.foldM (\() ([x,y], z) -> putStrLn (show x ++ "; " ++ show y ++ "; " ++ show z)) () (Map.toList m)	
	
	
runPart :: [String] -> IO ()	
runPart _ = do
	let n = 8
	rs <- results8
	let done = map (\(w, _) -> w) rs
	putStrLn $ show $ runAll [1..n] $ filter (\x -> not $ elem x done) $ (s !! (n-1))

	
main :: IO ()
main = do
	args <- getArgs
	case head args of
		"run" -> run (tail args)
		"run1" -> putStrLn $ show $ run1 [[[1,2,3,4,5]],[[3,4,5]],[[6,7]]]
		"runPart" -> runPart (tail args)
		"pairs" -> runPairs (tail args)
		"triples" -> runTriples (tail args)
		"all" -> allTogether (tail args)
		"all5" -> all5 (tail args)
		_ -> error "Unknown command"

