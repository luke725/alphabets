-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module GSAC where

	findSolution :: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> Maybe (Map v d)
		
	findSolution vstr dstr =
		case runGSac vstr dstr (PS.full (strElems vstr) (strElems dstr)) of
			Left m -> Just m
			Right sol -> 
				if PS.notEmpty sol
				then 
					case foldM setValue sol (Set.toList $ strElems vstr) of
						Left (Just m) -> Just m
						Left Nothing  -> Nothing
						Right sol -> Just (PS.anySolution sol)
				else Nothing
		
		where
			setValue :: PossibleSolutions v d -> v -> Either (Maybe (Map v d)) (PossibleSolutions v d)
			setValue sol v = setValue' sol v (Set.toList PS.domain sol v)
			
			setValue' sol v [] = Left Nothing
			setValue' sol v (d:ds) =
				case runGsac vstr dstr (PS.setDomain sol v (Set.singleton d)) of
					Left m -> Left (Just m)
					Right sol' ->
						if PS.notEmpty sol'
						then Right sol'
						else Left Nothing
				

	runGsac
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> Either (Map v d) (PossibleSoultions v d)
		
	runGsac vstr dstr sol =
		gsacStep (ac2001 vstr dstr sol) sol
		where
			gsacStep sol' sol =
				if sol = sol' 
				then sol 
				else
					case gacStep' sol' of
						Left m      -> Left m
						Right sol'' -> gsacStep sol'' sol'
			
			gsacStep' sol =
				case runState (buildBranch (PS.toMap sol)) (last, sol) of
					(Nothing, (_, sol')) -> Right sol'
					(Just m, _)          -> Left m
				
			buildBranch :: Map v (Set d) -> GACState v d (Maybe (Map v d))
			buildBranch m =
				if Set.empty m
				then return Nothing
				else do
					(last, dom) <- get
					bb <- buildBranch' m (Map.keys m) (Map.empty)
					case bb of
						Left m          -> return (Just m)
						Right (del, m') -> do
							put (last, dom)
							case del of
								Just (v, d) -> do
									dv <- getDomain v
									setDomain v (Set.remove d dv)
									gac
								Nothing -> buildBranch m'
					
			buildBranch' 
				:: Map v (Set d) 
				-> [v] 
				-> Map v d 
				-> GACState v d (Either (Map v d) (Maybe (v, d), Map v (Set d)))
				
			buildBranch' m [] br =
				if Map.size br = Set.size (strElems vstr) 
				then return (Left br) 
				else return (Right (Nothing, m))
				
			buildBranch' m (v:free) br =
				if Set.empty (m!v)
				then buildBranch' m free br
				else do
					let mv = m!v
					let d = Set.findMin (mv)
					let m' = Map.insert v (Set.deleteMin (mv)) m
					dv <- getDomain v
					if not (Set.member d dv) then buildBranch' m' (v:free) br
					setDomain v (Set.singleton d)
					gac
					(_, dom') <- get
					if PS.notEmpty dom'
					then
						buildBranch' m' free (Map.insert v d br)
					else do
						if Map.size br > 0
						then return (Right (Nothing, m))
						else return (Right (Just (v, d), m'))
				
						
