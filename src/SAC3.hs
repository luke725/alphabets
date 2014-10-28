-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module SAC3 where
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map, (!))
	import qualified Data.Map as Map
	import Control.Monad.State
	import Prelude hiding (last)

	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	import RelationalStructure
	import AC2001
	import Utils
	
	-- finds solution with some generic optimizations
	findSolutionFast :: forall v d rname. (Ord v, Ord d, Ord rname, Show v, Show d) 
		=> Structure rname v 
		-> Structure rname d
		-> Maybe (Map v d)
		
	findSolutionFast vstr dstr =
		case findSolution vstrInt' dstrInt' of
			Just m -> Just $ Map.fromList $ map (\(vi, di) -> (vstrMap!vi, dstrMap!di)) $ Map.toList m
			Nothing -> Nothing
		where
			vstrInt' = renameRelations (\rname -> sigMapInt!rname) vstrInt
			dstrInt' = renameRelations (\rname -> sigMapInt!rname) dstrInt
			sigMapInt = sigMapToInt (structureSig vstrInt)
			(vstrInt, vstrMap, _) = intStructure vstr
			(dstrInt, dstrMap, _) = intStructure dstr
			
	applyUnaryConstraint :: (Ord v, Ord d, Ord rname) => Structure rname v -> Structure rname d -> PossibleSolutions v d
	applyUnaryConstraint vstr dstr =
		foldl 
			(\sol (v, ds) ->  PS.setDomain v (Set.intersection ds (PS.domain sol v)) sol) 
			(PS.full (structureElems vstr) (structureElems dstr)) 
			constraints
		where
			(Signature sigMap) = structureSig vstr
			constraints = 
				concatMap (\(vs, ds) -> map (\v -> (v, ds)) (Set.toList vs))
				$ map (\(Relation (_, _, vts), Relation (_, _, dts)) -> (Set.map (\(Tuple[v]) -> v) vts, Set.map (\(Tuple[d]) -> d) dts)) 
				$ map (\rname -> (getRelation vstr rname, getRelation dstr rname)) $ Map.keys $ Map.filter (\(Arity r) -> (r == 1)) sigMap
	

	findSolution :: forall v d rname. (Ord v, Ord d, Ord rname, Show v, Show d) 
		=> Structure rname v 
		-> Structure rname d
		-> Maybe (Map v d)
		
	findSolution vstr dstr =
		case runSAC' vstr dstr cspDataVD (applyUnaryConstraint vstr dstr) of
			Left m -> Just m
			Right sol -> 
				if PS.notEmpty sol
				then 
					case foldM setValue sol (Set.toList $ structureElems vstr') of
						Left (Just m) -> Just m
						Left Nothing  -> Nothing
						Right sol' -> Just (PS.anySolution sol')
				else Nothing
		
		where
			setValue :: PossibleSolutions v d -> v -> Either (Maybe (Map v d)) (PossibleSolutions v d)
			setValue sol v = setValue' sol v (Set.toList $ PS.domain sol v)
			
			setValue' _ _ [] = Left Nothing
			setValue' sol v (d:ds) =
				case runSAC' vstr' dstr' cspDataVD (PS.setDomain v (Set.singleton d) sol) of
					Left m -> Left (Just m)
					Right sol' ->
						if PS.notEmpty sol'
						then Right sol'
						else setValue' sol v ds
						
			cspDataVD = cspData vstr' dstr'
			
			vstr' = removeUnaryRelations vstr
			dstr' = removeUnaryRelations dstr

	runSAC
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> Either (Map v d) (PossibleSolutions v d)
		
	runSAC vstr dstr sol = runSAC' vstr dstr (cspData vstr dstr) sol
				

	runSAC'
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> CSPData v d
		-> PossibleSolutions v d 
		-> Either (Map v d) (PossibleSolutions v d)
		
	runSAC' vstr dstr cspDataVD sol = do
		(_, sol') <- fixPointM sacStep (emptyLast, runAC vstr dstr sol)
		return sol'
		where
			sacStep :: (Last v d, PossibleSolutions v d) -> Either (Map v d) (Last v d, PossibleSolutions v d)
			sacStep (last, dom) =
				case runState (buildBranch (PS.toMap dom)) (last, dom) of
					(Nothing, (last', dom')) -> Right (last', dom')
					(Just m, _)          -> Left m
				
			buildBranch :: Map v (Set d) -> ACState v d (Maybe (Map v d))
			buildBranch m =
				if Map.size m == 0
				then return Nothing
				else do
					(last, dom) <- get
					bb <- buildBranch' m (Map.keys m) (Map.empty)
					case bb of
						Left m'         -> return (Just m')
						Right (del, m') -> do
							put (last, dom)
							case del of
								Just (v, d) -> do
									dv <- getDomain v
									setDomain v (Set.delete d dv)
									ac cspDataVD
									return Nothing
								Nothing -> buildBranch m'
	
			buildBranch' 
				:: Map v (Set d) 
				-> [v] 
				-> Map v d 
				-> ACState v d (Either (Map v d) (Maybe (v, d), Map v (Set d)))
				
			buildBranch' m [] br =
				if Map.size br == Set.size (structureElems vstr) 
				then return (Left br) 
				else return (Right (Nothing, m))
				
			buildBranch' m (v:free) br =
				case Map.lookup v m of
					Nothing -> buildBranch' m free br
					Just mv ->
						if Set.size (m!v) == 0
						then buildBranch' (Map.delete v m) free br
						else do
							let d = Set.findMin mv
							let m' = 
								if Set.size mv > 1 
								then Map.insert v (Set.deleteMin (mv)) m 
								else Map.delete v m
							dv <- getDomain v
							if not (Set.member d dv) 
							then buildBranch' m' (v:free) br 
							else do
								setDomain v (Set.singleton d)
								ac cspDataVD
								(_, dom') <- get
								if PS.notEmpty dom'
								then
									buildBranch' m' free (Map.insert v d br)
								else do
									if Map.size br > 0
									then return (Right (Nothing, m))
									else return (Right (Just (v, d), m'))

