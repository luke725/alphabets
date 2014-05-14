-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module OptSAC where
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
	
	data Store v d = 
		Store
		{ -- cn :: ConstrainNetwork v d
		 dom :: PossibleSolutions v d
		, lastMatch :: Map (v, d, v) d
--		; qSAC :: Map v (Set d)
		}
		
	type SACState v d = State (Store v d)
	
--	getCN :: SACState (PossibleSolutions v d)
--	getCN = do
--		st <- get
--		return (cn st)
	
	getDom :: SACState v d (PossibleSolutions v d)
	getDom = do
		st <- get
		return (dom st)
		
	setDom :: PossibleSolutions v d -> SACState v d ()
	setDom dom' = do
		st <- get
		put (st {dom = dom'})
		
	getLast :: (Ord v, Ord d) => v -> d -> v -> SACState v d (Maybe d)
	getLast v1 d1 v2 = do
		st <- get
		return (Map.lookup (v1, d1, v2) (lastMatch st))
		
	setLast :: (Ord v, Ord d) => v -> d -> v -> d -> SACState v d ()
	setLast v1 d1 v2 d2 = do
		st <- get
		put (st { lastMatch = Map.insert (v1, d1, v2) d2 (lastMatch st) })
		
		
	isLastOk :: (Ord v, Ord d) => v -> d -> v -> SACState v d Bool
	isLastOk v1 d1 v2 = do
		dom <- getDom
		l <- getLast v1 d1 v2
		case l of
			Just d2 -> return (Set.member d2 (dom ! v2))
			Nothing -> return False
	
	revise :: forall v d. (Ord v, Ord d) => ConstraintNetwork v d -> v -> v -> SACState v d Bool
	revise cn v w = do
		dom <- getDom
		dToCheck <- filterM (\d -> notM $ isLastOk v d w) (Set.toList (dom ! v))
		hasChangedList <- mapM (\d -> reviseElem v d w) dToCheck
		return (or hasChangedList)
		where
			reviseElem :: v -> d -> v -> SACState v d Bool
			reviseElem v1 d1 v2 = do
				dom <- getDom
				l <- getLast v1 d1 v2
				let dSet = case l of
					Just d2Old -> snd (Set.split d2Old (dom ! v2))
					Nothing    -> dom ! v2
				let tuples = constraint cn (v1, v2)
				let d2Possible =  filter (\d2 -> Set.member (d1, d2) tuples) (Set.toList dSet)
				case d2Possible of
					d2:_ -> do
						setLast v1 d1 v2 d2
						return False -- didn't change
					[] -> do
						setDom (Map.insert v1 (Set.delete d1 (dom!v1)) dom)
						return True
					
					
	ac2001 :: forall v d. (Ord v, Ord d) => ConstraintNetwork v d -> PossibleSolutions v d -> Maybe (PossibleSolutions v d)
	ac2001 cn sol =
		if res
		then Just (dom store)
		else Nothing
		where
			(res, store) =
				runState (run qInit) (Store {dom = sol, lastMatch = Map.empty })
				
			run :: [(v, v)] -> SACState v d Bool
			run [] = return True
			run ((v, w):t) = do
				changed <- revise cn v w
				if changed 
				then do
					dom <- getDom
					if Set.null (dom ! v)
					then return False
					else
						run ((map (\w' -> (w', v)) $ Set.toList $ Set.delete w $ neighbors cn v) ++ t)
				else
					run t
					
			qInit = 
				concatMap (\(v, ws) -> map (\w -> (v, w)) $ Set.toList ws) 
				$ Map.toList 
				$ neighborsMap cn
	
	
