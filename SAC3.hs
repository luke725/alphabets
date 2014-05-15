-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module SAC3 where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import qualified Data.Maybe as Maybe
	import Control.Monad
	import Control.Monad.State
	import Control.Conditional
	
	import ConstraintNetwork
	import RelationalStructure
	import AC2001
	
	import Debug.Trace
	
	data Store v d = 
		Store
		{ dom :: PossibleSolutions v d
		, lastMatch :: Map (v, d, v) d
		, qsac :: Map v (Set d)
		, qsacLoc :: Map v (Set d)
		}
	
	getDom :: State (Store v d) (PossibleSolutions v d)
	getDom = do
		st <- get
		return (dom st)
		
	setDom :: PossibleSolutions v d -> State (Store v d) ()
	setDom dom' = do
		st <- get
		put (st {dom = dom'})
		
		
	getLast :: State (Store v d) (Map (v, d, v) d)
	getLast = do
		st <- get
		return (lastMatch st)
		
	setLast :: Map (v, d, v) d -> State (Store v d) ()
	setLast last' = do
		st <- get
		put (st {lastMatch = last'})
		
	withACStore :: (PossibleSolutions v d, Map (v, d, v) d) -> State (Store v d) a -> State (Store v d) a
	withACStore (sol, last) m = do
		st <- get
		put (st {dom = sol, lastMatch = last})
		a <- m
		st' <- get
		put (st' {dom = (dom st), lastMatch = (lastMatch st)})
		return a
	
	withSingletonDom :: (Ord v) => v -> d -> State (Store v d) a -> State (Store v d) a
	withSingletonDom v d m = do
		dom <- getDom
		setDom (Map.insert v (Set.singleton d) dom)
		a <- m
		setDom dom
		return a
		
	pickAndDel :: (Ord v, Ord d) => State (Store v d) (Maybe (v, d))
	pickAndDel = do
		st <- get
		if Map.null (qsacLoc st)
		then return Nothing
		else do
			let ((v, ds), qsacLoc') = Map.deleteFindMin (qsacLoc st)
			put (st {qsacLoc = qsacLoc'})
			
			let ds' = Set.intersection ds (dom st ! v)
			(if Set.null ds'
				then
					pickAndDel
				else do
					let d = Set.findMin ds'
					st' <- get
					put (st' {qsac = Map.insert v (Set.delete d (qsac st ! v)) (qsac st')})
					return $ Just (v, d))
				
	addToQsac :: (Ord v, Ord d) => v -> d -> State (Store v d) ()
	addToQsac v d = do
		st <- get
		let qsac' = Map.insertWith Set.union v (Set.singleton d) (qsac st)
		put (st {qsac = qsac', qsacLoc = Map.insert v (qsac' ! v) (qsacLoc st)})
		
	resetQsac :: (Ord v, Ord d) => State (Store v d) ()
	resetQsac = do
		st <- get
		let qsac' = Map.intersectionWith Set.intersection (qsac st) (dom st)
		let qsac'' = Map.filter (\ds -> not $ Set.null ds) qsac'
		put (st {qsac = qsac'', qsacLoc = qsac''})
		
	removeSingletons :: (Ord v, Ord d) => State (Store v d) ()
	removeSingletons = do
		st <- get
		let qsac' =
			foldl (\qsac' (v, d) -> if Map.member v qsac' then Map.insert v (Set.delete d (qsac' ! v)) qsac' else qsac') (qsac st)
			$ map (\(v, ds) -> (v, Set.findMin ds)) 
			$ filter (\(_, ds) -> Set.size ds == 1) 
			$ Map.toList (dom st)
		put (st {qsac = qsac'})

	
	data BranchResult v d = CheckedAll | StillRemain | Finished (Map v d)

	buildBranch :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> State (Store v d) (BranchResult v d)
	buildBranch cn = do
		pd <- pickAndDel
		case pd of
			Nothing -> return CheckedAll
			Just (v, d) -> do
				dom <- getDom
				last <- getLast
				let (dom', last') = ac2001 cn (Map.insert v (Set.singleton d) dom, last)
				if notEmpty dom'
				then withACStore (dom', last') buildBranch'
				else do
					let (dom'', last'') = ac2001 cn (Map.insert v (Set.delete d (dom ! v)) dom, last)
					setDom dom''
					setLast last''
					if notEmpty dom''
					then return StillRemain
					else return CheckedAll
		where
			buildBranch' = do
				pd <- pickAndDel
				case pd of
					Nothing -> do
						dom <- getDom
						if all (\ds -> Set.size ds == 1) (Map.elems dom)
						then
							return $ Finished $ Map.map Set.findMin dom
						else do
							removeSingletons
							return StillRemain
					Just (v, d) -> do
						dom <- getDom
						last <- getLast
						let (dom', last') = ac2001 cn (Map.insert v (Set.singleton d) dom, last)
						if notEmpty dom'
						then withACStore (dom', last') buildBranch'
						else do
							addToQsac v d
							removeSingletons
							return StillRemain


	buildBranches :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> State (Store v d) (Maybe (Map v d))
	buildBranches cn = do
		resetQsac
		c <- buildBranch cn
		case c of
			CheckedAll  -> return Nothing
			StillRemain -> buildBranches cn
			Finished m  -> return $ Just m

						
	sac3' :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> PossibleSolutions v d -> PossibleSolutions v d
	sac3' cn dom' =
		sac3'' (ac2001 cn (dom', Map.empty))
		where
			sac3'' (dom', last') =
				if notEmpty dom'
				then 
					if dom st == dom'
					then dom'
					else sac3'' (dom st, lastMatch st)
				else dom'
				where
					qsac' = Map.filterWithKey (\v _ -> Set.member v (coreElems cn)) dom'
					st = execState (buildBranches cn) (Store {dom = dom', qsac = qsac', qsacLoc = qsac', lastMatch = last'})


	sac3 :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> PossibleSolutions v d
	sac3 cn =
		sac3' cn (domainMap cn)
				
	findSAC3Solution :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> Maybe (Map v d)
	findSAC3Solution cn =
		findSol (domainMap cn)
		where
			findSol dom =
				if not $ notEmpty dom
				then Nothing
				else
					case 
						Maybe.listToMaybe 
						$ filter (\(_, ds) -> Set.size ds > 1)
						$ Map.toList dom
					of
						Nothing -> Just $ Map.map (\ds -> Set.findMin ds) dom
						Just (v, ds) -> 
							case 
								Maybe.listToMaybe 
								$ filter (\dom' -> notEmpty dom') 
								$ map (\d -> sac3' cn (Map.insert v (Set.singleton d) dom))
								$ Set.toList ds
							of
							Just dom' -> findSol dom'
							Nothing   -> Nothing
						

			
