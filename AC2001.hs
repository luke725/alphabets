-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module AC2001 (ac2001, notEmpty, PossibleSolutions, ACStore) where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import Control.Monad
	import Control.Monad.State
	import Control.Conditional
	
	import ConstraintNetwork
	import RelationalStructure
	
	type PossibleSolutions a b = Map a (Set b)
	
	data ACStore v d = 
		ACStore
		{ solutions :: PossibleSolutions v d
		, lastMatch :: Map (v, d, v) d
		}
	
	getSolutions :: State (ACStore v d) (PossibleSolutions v d)
	getSolutions = do
		st <- get
		return (solutions st)
		
	setSolutions :: PossibleSolutions v d -> State (ACStore v d) ()
	setSolutions solutions' = do
		st <- get
		put (st {solutions = solutions'})
		
	getLast :: (Ord v, Ord d) => v -> d -> v -> State (ACStore v d) (Maybe d)
	getLast v1 d1 v2 = do
		st <- get
		return (Map.lookup (v1, d1, v2) (lastMatch st))
		
	setLast :: (Ord v, Ord d) => v -> d -> v -> d -> State (ACStore v d) ()
	setLast v1 d1 v2 d2 = do
		st <- get
		put (st { lastMatch = Map.insert (v1, d1, v2) d2 (lastMatch st) })
		
		
	isLastOk :: (Ord v, Ord d) => v -> d -> v -> State (ACStore v d) Bool
	isLastOk v1 d1 v2 = do
		sol <- getSolutions
		l <- getLast v1 d1 v2
		case l of
			Just d2 -> return (Set.member d2 (sol ! v2))
			Nothing -> return False
	
	revise :: forall v d. (Ord v, Ord d) => ConstraintNetwork v d -> v -> v -> State (ACStore v d) Bool
	revise cn v w = do
		sol <- getSolutions
		dToCheck <- filterM (\d -> notM $ isLastOk v d w) (Set.toList (sol ! v))
		hasChangedList <- mapM (\d -> reviseElem v d w) dToCheck
		return (or hasChangedList)
		where
			reviseElem :: v -> d -> v -> State (ACStore v d) Bool
			reviseElem v1 d1 v2 = do
				sol <- getSolutions
				l <- getLast v1 d1 v2
				let dSet = case l of
					Just d2Old -> snd (Set.split d2Old (sol ! v2))
					Nothing    -> sol ! v2
				let tuples = constraint cn (v1, v2)
				let d2Possible =  filter (\d2 -> Set.member (d1, d2) tuples) (Set.toList dSet)
				case d2Possible of
					d2:_ -> do
						setLast v1 d1 v2 d2
						return False -- didn't change
					[] -> do
						setSolutions (Map.insert v1 (Set.delete d1 (sol!v1)) sol)
						return True
					
					
	ac2001 :: forall v d. (Ord v, Ord d) => ConstraintNetwork v d -> (PossibleSolutions v d, Map (v, d, v) d) -> (PossibleSolutions v d, Map (v, d, v) d)
	ac2001 cn (sol', last') =
		(solutions store', lastMatch store')
		where
			((), store') =
				runState (run qInit) (ACStore {solutions = sol', lastMatch = last'})
				
			run :: [(v, v)] -> State (ACStore v d) ()
			run [] = return ()
			run ((v, w):t) = do
				changed <- revise cn v w
				if changed 
				then do
					sol <- getSolutions
					if Set.null (sol ! v)
					then return ()
					else
						run ((map (\w' -> (w', v)) $ Set.toList $ Set.delete w $ neighbors cn v) ++ t)
				else
					run t
					
			qInit = 
				concatMap (\(v, ws) -> map (\w -> (v, w)) $ Set.toList ws) 
				$ Map.toList
				$ neighborsMap cn
				
				
	notEmpty :: PossibleSolutions a b -> Bool
	notEmpty sol =
		all (\set -> not (Set.null set)) (Map.elems sol)
				
				

				
	
	
	
