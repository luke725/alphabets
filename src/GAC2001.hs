-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module GAC where
	newtype Constraint rname v = Constraint (rname, Tuple v)
	newtype Last rname v d = Last (Map ((v, d), Constraint rname v) (Tuple d))
	type GACState rname v d = State (Last rname v d, PossibleSolutions v d)
	
	gac2001
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> PossibleSoultions v d
		
	gac2001 vstr dstr sol = snd $ gac2001' vstr dstr (Last $ Map.empty) sol
	
	gac2001' 
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d 
		-> Last rname v d 
		-> PossibleSolutions v d 
		-> (Last rname v d, PossibleSoultions v d)
		
	gac2001' vstr dstr last sol =
		execState (gacStep q) (last, sol)
		where
			gacStep :: Set (v, Constraint rname v) -> GACState rname v d ()
			gacStep q =
				if Set.empty q
				then return ()
				else do
					let ((v, c), q') = Set.deleteFindMin q
					delete <- revise dstr (v, c)
					let q'' = if delete then addNeighbors (v, c) q' else q'
					gacStep q''
			
			
	revise :: (Ord v, Ord d, Ord rname) => Structure rname d -> (v, Constraint rname v) -> GACState rname v d Bool
	revise dstr (v, c) = do
		dom <- getDomain v
		orM (map reviseD $ Set.toList dom)
		where
			reviseD :: d -> GACState rname v d Bool
			reviseD d = do
				t <- getLast ((v,d), c)
				ok <- testTuple (c, t)
				if ok
				then return False
				else do
					dom <- getDomain v
					setDomain v (Set.singleton a)
					doms <- getDomains c
					let (Constraint (rname,_)) = c
					case nextOkTuple (RelationStructure.isInRelation dstr rname) doms t of
						Just t' -> do
							setLast ((v,d), c) t'
							setDomain v dom
							return False
						Nothing -> do
							setDomain v (Set.delete a dom)
							return True
							
			testTuple (c, Tuple ts) = do 
				doms <- getDomains c
				return $ all (\(v, d) -> Set.member v d) (zip ts doms)
				
			getDomains (Constraint (_, Tuple ts)) = do
				mapM getDomain ts
				
					
			
				
	
	getLast :: (Ord v, Ord d, Ord rname) => (Map ((v, d), Constraint rname v) -> GACState rname v d (Maybe (Tuple d))
	getLast k = do
		(Last m, _) <- get
		return $ Map.lookup k m
		
	setLast :: (Map ((v, d), Constraint rname v) -> Tuple d -> GACState rname v d ()
	setLast k t = do
		(Last m, sol) <- get
		set (Map.insert k t m, sol)
		
	getDomain :: (Ord v) => v -> GACState rname v d (Set d)
	getDomain v = do
		(_, sol) <- get
		return (PossibleSolutions.domain sol v)
		
	setDomain :: (Ord v) => v -> Set d -> GACState rname v d ()
	setDomain v ds = do
		(last, sol) <- get
		put (last, PossibleSolutions.setDomain v ds sol)
		
	allConstraints :: Structure rname v -> [Constraint rname v]
	
	firstTuple :: [Set v] -> Maybe (Tuple v)
	firstTuple [] = Just (Tuple [])
	firstTuple (hs:ts) = 
		if Set.empty hs 
		then Nothing 
		else 
			case firstTuple ts of
				Just r -> Just (Set.findMin hs : r)
				Nothing -> Nothing
	
	nextTuple :: [Set v] -> Tuple v -> Maybe (Tuple v)
	nextTuple [] (Tuple []) = Just (Tuple [])
	nextTuple [hs] (Tuple [ht]) =
		let (_, _, ls) in firstTuple [ls]
		
	nextTuple (hs:ts) (Tuple (ht:tt)) =
		case Set.splitMember ht hs of
			(_, False, ls) -> firstTuple (ls:ts)
			(_, True, ls) ->
				case nextTuple ts tt of
					Just (Tuple rt) -> Just (Tuple (ht:rt))
					Nothing -> firstTuple (ls:ts)
	nextTuple [] (_:_) = error
	nextTuple (_:_) [] = error
	
	nextOkTuple :: (Tuple v -> Bool) -> [Set v] -> Tuple v -> Maybe (Tuple v)
	nextOkTuple c s t =
		case nextTuple s t of
			Just nt -> okTuple c s nt
			Nothing -> Nothing
		where
			okTuple c s t =
				if c t 
				then Just t 
				else nextOkTuple c s t
				
	
		
