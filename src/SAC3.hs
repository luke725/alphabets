-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module SAC3 where
	import Prelude hiding (last)
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.Maybe as Maybe
	import Control.Monad.State
	
	import ConstraintNetwork
	import AC2001
	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	
	
	data Store v d = 
		Store
		{ dom :: PossibleSolutions v d
		, lastMatch :: Last v d
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
		
		
	getLast :: State (Store v d) (Last v d)
	getLast = do
		st <- get
		return (lastMatch st)
		
	setLast :: Last v d -> State (Store v d) ()
	setLast last' = do
		st <- get
		put (st {lastMatch = last'})
		
	withACStore :: (PossibleSolutions v d, Last v d) -> State (Store v d) a -> State (Store v d) a
	withACStore (sol, last) m = do
		st <- get
		put (st {dom = sol, lastMatch = last})
		a <- m
		st' <- get
		put (st' {dom = (dom st), lastMatch = (lastMatch st)})
		return a
	
	withSingletonDom :: (Ord v) => v -> d -> State (Store v d) a -> State (Store v d) a
	withSingletonDom v d m = do
		dom' <- getDom
		setDom (PS.setValue v d dom')
		a <- m
		setDom dom'
		return a
		
	pickAndDel :: (Ord v, Ord d) => State (Store v d) (Maybe (v, d))
	pickAndDel = do
		st <- get
		if Map.null (qsacLoc st)
		then return Nothing
		else do
			let ((v, ds), qsacLoc') = Map.deleteFindMin (qsacLoc st)
			put (st {qsacLoc = qsacLoc'})
			
			let ds' = Set.intersection ds (PS.domain (dom st) v)
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
		let qsac' = Map.intersectionWith Set.intersection (qsac st) (PS.toMap $ dom st)
		let qsac'' = Map.filter (\ds -> not $ Set.null ds) qsac'
		put (st {qsac = qsac'', qsacLoc = qsac''})
		
	removeSingletons :: (Ord v, Ord d) => State (Store v d) ()
	removeSingletons = do
		st <- get
		let qsac' =
			foldl 
				(\qsac'' (v, d) -> 
					if Map.member v qsac'' 
					then Map.insert v (Set.delete d (qsac'' ! v)) qsac''
					else qsac''
				) 
				(qsac st)
			$ map (\(v, ds) -> (v, Set.findMin ds)) 
			$ filter (\(_, ds) -> Set.size ds == 1) 
			$ Map.toList $ PS.toMap (dom st)
		put (st {qsac = qsac'})

	
	data BranchResult v d = CheckedAll | StillRemain | Finished (Map v d)

	buildBranch 
		:: (Ord v, Ord d, Show v, Show d) 
		=> ConstraintNetwork v d 
		-> State (Store v d) (BranchResult v d)
		
	buildBranch cn = do
		pd <- pickAndDel
		case pd of
			Nothing -> return CheckedAll
			Just (v, d) -> do
				dom' <- getDom
				last <- getLast
				let (dom'', last') = ac2001SingleChange cn v last (PS.setValue v d dom')
				if PS.notEmpty dom''
				then withACStore (dom'', last') buildBranch'
				else do
					let (dom''', last'') = 
						ac2001SingleChange cn v last (PS.removeFromDomain v d dom')
					setDom dom'''
					setLast last''
					if PS.notEmpty dom'''
					then return StillRemain
					else return CheckedAll
		where
			buildBranch' = do
				pd <- pickAndDel
				case pd of
					Nothing -> do
						dom' <- getDom
						if PS.isUnique dom'
						then
							return $ Finished $ PS.anySolution dom'
						else do
							removeSingletons
							return StillRemain
					Just (v, d) -> do
						dom' <- getDom
						last <- getLast
						let (dom'', last') = 
							ac2001SingleChange cn v last (PS.setValue v d dom')
						if PS.notEmpty dom''
						then withACStore (dom'', last') buildBranch'
						else do
							addToQsac v d
							removeSingletons
							return StillRemain


	buildBranches 
		:: (Ord v, Ord d, Show v, Show d) 
		=> ConstraintNetwork v d 
		-> State (Store v d) (Maybe (Map v d))
	
	buildBranches cn = do
		resetQsac
		c <- buildBranch cn
		case c of
			CheckedAll  -> return Nothing
			StillRemain -> buildBranches cn
			Finished m  -> return $ Just m
				
	sac3' 
		:: forall v d. (Ord v, Ord d, Show v, Show d) 
		=> ConstraintNetwork v d 
		-> (PossibleSolutions v d, Last v d)
		-> (PossibleSolutions v d, Last v d)

	sac3' cn (dom', last') =
		if PS.notEmpty dom'
		then 
			if dom st == dom'
			then (dom', last')
			else sac3' cn (dom st, lastMatch st)
		else (dom', last')
		where
			qsac' = Map.filterWithKey (\v _ -> Set.member v (coreElems cn)) (PS.toMap dom')
			st = 
				execState 
					(buildBranches cn) 
					(Store {dom = dom', qsac = qsac', qsacLoc = qsac', lastMatch = last'})


	sac3 :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> Bool
	sac3 cn =
		PS.notEmpty $ fst $ sac3' cn (ac2001 cn emptyLast (PS.fromMap $ domainMap cn))
		
				
	findSAC3Solution :: (Ord v, Ord d, Show v, Show d) => ConstraintNetwork v d -> Maybe (Map v d)
	findSAC3Solution cn =
		findSol (sac3' cn (ac2001 cn emptyLast (PS.fromMap $ domainMap cn)))
		where
			findSol (dom', last) =
				if not $ PS.notEmpty dom'
				then Nothing
				else
					case 
						Maybe.listToMaybe 
						$ filter (\(_, ds) -> Set.size ds > 1)
						$ filter (\(v, _) -> Set.member v (coreElems cn))
						$ Map.toList $ PS.toMap dom'
					of
						Nothing -> 
							Just
							$ Map.filterWithKey (\v _ -> Set.member v (coreElems cn)) 
							$ PS.anySolution dom'
						Just (v, ds) -> 
							case 
								Maybe.listToMaybe 
								$ filter (\(s, _) -> PS.notEmpty s)
								$ map (\d -> sac3' cn (ac2001 cn last (PS.setValue v d dom')))
								$ Set.toList ds
							of
							Just (dom'', last') -> findSol (dom'', last')
							Nothing   -> Nothing
						

			
