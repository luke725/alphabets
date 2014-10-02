-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module GSAC where

	gsac
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> PossibleSoultions v d
		
	gsac vstr dstr sol =
		gsacStep (ac2001 vstr dstr sol) sol
		where
			gsacStep sol' sol =
				if sol = sol' then sol else gsacStep (gacStep' sol') sol'
			
			gsacStep' sol =
				snd $ execState (buildBranch (PS.toMap sol)) (last, sol)
				
			buildBranch :: Map v (Set d) -> GACState v d ()
			buildBranch m =
				if Set.empty m
				then return ()
				else do
					(last, dom) <- get
					(del, m') <- buildBranch' m (Map.keys m) (Map.empty)
					put (last, dom)
					case del of
						Just (v, d) -> do
							dv <- getDomain v
							setDomain v (Set.remove d dv)
							gac	
						Nothing -> buildBranch m'
					
			buildBranch' :: Map v (Set d) -> [v] -> Map v d -> GACState v d (Maybe (v, d), Map v (Set d))
			buildBranch' m [] br = return (Nothing, m)
			buildBranch' m (v:free) br =
				if Set.empty (m!v)
				then buildBranch' m free br
				else do
					let mv = m!v
					let d = Set.findMin (mv)
					let m' = Map.insert v (Set.deleteMin (mv)) m
					dv <- getDomain v
					if not (Set.member d dv) then buildBranch' m' (v:free) br
					setDomain v (Set.singleton d) buildBranch' m free br
					gac
					if PS.notEmpty dom'
					then do
						buildBranch' m' free (Map.insert v d br)
					else do
						if Map.size br > 0
						then return (Nothing, m)
						else return (Just (v, d), m')
				
						
