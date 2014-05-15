-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module SAC3 where
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
	
	data Store v d = 
		Store
		{ dom :: PossibleSolutions v d
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
		
	withDom :: PossibleSolutions v d -> State (Store v d) a -> State (Store v d) a
	withDom dom' m = do
		dom'' <- getDom
		setDom dom'
		a <- m
		setDom dom''
		return a
	
	withSingletonDom :: v -> d -> State (Store v d) a -> State (Store v d) a
	withSingletonDom v d m = do
		dom <- getDom
		setDom (Map.insert v (Set.singleton d) dom)
		a <- m
		setDom dom
		return a
		
	pickAndDel :: State (Store v d) (Maybe (v, d))
	pickAndDel = do
		st <- get
		if Map.null (qsacLoc st)
		then Nothing
		else do
			let (v, ds) = Map.findMin (qsacLoc st)
			put (st {qsacLoc = Map.delete v (qsacLoc st)})
			let ds' = Set.intersect ds (dom st ! v)
			if Set.null ds'
			then
				pickAndDel
			else do
				let d = Set.findMin ds'
				put (st {qsac = Map.insert v (Set.delete d (qsac st ! v)) (qsac st)})
				return $ Just (v, d)
				
	addToQsac :: v -> d -> State (Store v d) ()
	addToQsac v d = do
		st <- get
		let qsac' = Map.insertWith Set.union v (Set.singleton d) (qsac st)
		put (st {qsac = qsac', qsacLoc = Map.insert v (qsac' ! v) qsacLoc})
		
	resetQsac :: State (Store v d) ()
	resetQsac = do
		st <- get
		let qsac' = Map.intersectionWith Set.intersection (qsac st) (dom st)
		let qsac'' = Map.filter (\ds -> not $ Set.null ds) qsac'
		put (st {qsac = qsac'', qsacLoc = qsac''})
		
		
		
	
	buildBranch :: ConstraintNetwork v d -> State (Store v d) Bool
	buildBranch cn = do
		pd <- pickAndDel 
		case pd of
			Nothing -> return False
			Just (v, d) -> do
				dom <- getDom
				let dom' = ac2001 cn (Map.insert v (Set.singleton d) dom)
				if notEmpty dom'
				then withDom dom' buildBranch'
				else do
					let dom'' = ac2001 cn (Map.insert v (Set.delete d (dom ! v)) dom)
					setDom dom''
					return (notEmpty dom'')
								
		where
			buildBranch' = do
				pd <- pickAndDel
				case pd of
					Nothing -> return ()
					Just (v, d) -> do
						dom <- getDom
						let dom' = ac2001 cn (Map.insert v (Set.singleton d) dom)
						if notEmpty dom'
						then withDom dom' buildBranch'
						else do
							addToQsac v d
							return True
							
	buildBranches :: ConstraintNetwork v d -> State (Store v d) ()
	buildBranches cn = do
		c <- buildBranch cn
		resetQsac
		if c
		then buildBranches cn
		else return ()
						
						
	sac3 :: ConstraintNetwork v d -> PossibleSolutions v d -> PossibleSolutions v d
	sac3 cn dom =
		sac3' (ac2001 cn dom)
		where
			sac3' dom' =
				if notEmpty dom'
				then 
					sac3' (dom st)
				else dom'
				where
					st = execState (buildBranches cn) (Store {dom = dom', qsac = qsacFromDom dom', qsacLoc = qsacFromDom dom'})
						
			qsacFromDom dom =
				concatMap (\(v, ds) -> map (\d -> (v, d)) (Set.toList ds)) (Map.toList dom)
				
				
	findSAC3Solution :: ConstraintNetwork v d -> Maybe (Map v d)
	findSAC3Solution cn =
		findSol (domainMap cn)
		where
			findSol dom =
				if isEmpty dom
				then Nothing
				else
					case 
						Maybe.listToMaybe 
						$ filter (\(_, ds) -> Set.size ds > 1)
						$ Map.fromList dom 
					of
						Nothing -> Just $ Map.map (\ds -> Set.findMin ds) dom
						Just (v, ds) -> 
							case 
								Maybe.listToMaybe 
								$ filter (\dom' -> notEmpty dom') 
								$ map (\d -> sac3 cn (Map.insert v (Set.singleton d) ds) 
								$ Set.toList ds of
							Just dom' -> findSol dom'
							Nothing   -> Nothing
						

			
