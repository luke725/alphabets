-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module SAC3 where
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import Control.Monad.State
	import Prelude hiding (last)

	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	import RelationalStructure
	import AC2001
	import Utils
	import Constraint (CSPData)
	import qualified Constraint
	
	type PairSet a b = Map a (Set b)
	
	data BuildBranchResult a b = Branch [(a, b)] | ZeroBranch (a, b) deriving (Eq, Ord, Show)
	
	-- finds solution with some generic optimizations
	findSolutionFast :: forall v d rname. (Ord v, Ord d, Ord rname, Show v, Show d) 
		=> Structure rname v 
		-> Structure rname d
		-> Maybe (Map v d)
		
	findSolutionFast vstr dstr =
		case findSolution vstrInt dstrInt of
			Just m -> Just $ Map.fromList $ map (\(vi, di) -> (vstrMap!vi, dstrMap!di)) $ Map.toList m
			Nothing -> Nothing
		where
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
		case runSAC' cspData (applyUnaryConstraint vstr dstr) of
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
				case runSAC' cspData (PS.setDomain v (Set.singleton d) sol) of
					Left m -> Left (Just m)
					Right sol' ->
						if PS.notEmpty sol'
						then Right sol'
						else setValue' sol v ds
						
			cspData = Constraint.createCspData vstr' dstr'
			
			vstr' = removeUnaryRelations vstr
			dstr' = removeUnaryRelations dstr

	runSAC
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> Either (Map v d) (PossibleSolutions v d)
		
	runSAC vstr dstr sol = runSAC' (Constraint.createCspData vstr dstr) sol
				

	runSAC'
		:: forall v d. (Ord v, Ord d) 
		=> CSPData v d
		-> PossibleSolutions v d 
		-> Either (Map v d) (PossibleSolutions v d)
		
	runSAC' cspData sol = do
		(_, sol') <- fixPointM sacStep (emptyLast, runAC' cspData sol)
		return sol'
		where
			sacStep :: (Last v d, PossibleSolutions v d) -> Either (Map v d) (Last v d, PossibleSolutions v d)
			sacStep (last, dom) =
				case runState (buildBranches (pairSetFromMap $ PS.toMap dom)) (last, dom) of
					(Nothing, (last', dom')) -> Right (last', dom')
					(Just m, _)              -> Left m
			
			-- returns Just m if accidentaly found a full solution
			buildBranches :: PairSet v d -> ACState v d (Maybe (Map v d))
			buildBranches m =
				if pairSetSize m == 0
				then return Nothing
				else do
					(last, dom) <- get
					bb <- buildBranch m (pairSetKeys m) []
					put (last, dom)
					case bb of
						Branch l ->
							if List.length l == Set.size (PS.variables dom)
							then return $ Just (Map.fromList l)
							else buildBranches (removePairs l m)
						ZeroBranch (v, d) -> do
							dv <- getDomain v
							setDomain v (Set.delete d dv)
							ac cspData
							buildBranches (removePair (v, d) m)
	
			buildBranch
				:: PairSet v d 
				-> [v] 
				-> [(v, d)]
				-> ACState v d (BuildBranchResult v d)
				
			buildBranch _ [] br = return (Branch br)
				
			buildBranch m (v:free) br =
				case getAny m v of
					Nothing -> buildBranch m free br
					Just d -> do
							let ps' = removePair (v, d) m
							setDomain v (Set.singleton d)
							ac cspData
							(_, dom') <- get
							if PS.notEmpty dom'
							then
								buildBranch ps' free ((v, d):br)
							else
								case br of
									[]    -> return (ZeroBranch (v, d))
									(_:_) -> return (Branch br)


	--auxiliary functions that operate on PairSet					
									
	pairSetFromMap :: Map a (Set b) -> PairSet a b
	pairSetFromMap m = Map.filter (\s -> Set.size s > 0) m
	
	removePair :: (Ord a, Ord b) => (a, b) -> PairSet a b -> PairSet a b
	removePair (a, b) ps =
		if Set.null bs
		then Map.delete a ps
		else Map.insert a bs ps
		where
			bs = Set.delete b (ps!a)
			
	removePairs :: (Ord a, Ord b) => [(a, b)] -> PairSet a b -> PairSet a b
	removePairs l ps = foldl (\ps' (a, b) -> removePair (a, b) ps') ps l
	
	getAny :: (Ord a, Ord b) => PairSet a b -> a -> Maybe b
	getAny ps a =
		case Map.lookup a ps of
			Just bs -> Just (Set.findMin bs)
			Nothing -> Nothing
			
	pairSetSize :: PairSet a b -> Int
	pairSetSize ps = Map.size $ Map.filter (\s -> Set.size s > 0) ps
	
	pairSetKeys :: PairSet a b -> [a]
	pairSetKeys = Map.keys

