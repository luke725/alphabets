-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module GAC2001 where
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map, (!))
	import qualified Data.Map as Map
	import Control.Monad.State
	import Prelude hiding (last)

	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	import Utils
	import RelationalStructure

	newtype Constraint v d = Constraint (Tuple v, Set (Tuple d)) deriving (Show, Eq, Ord)
	newtype Last v d = Last (Map ((v, d), Constraint v d) (Tuple d)) deriving (Show, Eq, Ord)
	type GACState v d = State (Last v d, PossibleSolutions v d)
	
	type CSPData v d = (Set (v, Constraint v d), Map v [(v, Constraint v d)])
	
	runGac :: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> PossibleSolutions v d
		
	runGac vstr dstr sol = snd $ execState (gac $ cspData vstr dstr) (emptyLast, sol)
	
	gac :: forall v d. (Ord v, Ord d) 
		=> CSPData v d
		-> GACState v d ()
		
	gac (allCs, mapCs) =
		gacStep allCs
		where
			gacStep :: Set (v, Constraint v d) -> GACState v d ()
			gacStep q =
				if Set.size q == 0
				then return ()
				else do
					let ((v, c), q') = Set.deleteFindMin q
					delete <- revise (v, c)
					let q'' = if delete then addNeighbors (v, c) q' else q'
					gacStep q''
					
			addNeighbors :: (v, Constraint v d) -> Set (v, Constraint v d) -> Set (v, Constraint v d)
			addNeighbors (v, c) q =
				foldl (\q' e -> Set.insert e q') q 
				$ filter (\(v', c') -> v /= v' && c /= c' && elem v' (constraintVars c'))
				$ (mapCs!v)
			
	cspData :: (Ord v, Ord d, Ord rname) => Structure rname v -> Structure rname d -> CSPData v d
	cspData vstr dstr = 
		(Set.fromList allCs, mapCs)
		where
			conPairs c = map (\v -> (v, c)) (constraintVars c)
			allCs = concatMap conPairs $ allConstraints vstr dstr
			mapCs = 
				foldl (\m (v, vc) -> Map.insertWith (++) v [vc] m) Map.empty 
				$ concatMap (\(v, c) -> map (\v' -> (v, (v',c))) (constraintVars c)) 
				$ allCs
				
				
			
			
	revise :: forall v d. (Ord v, Ord d) => (v, Constraint v d) -> GACState v d Bool
	revise (v, c) = do
		dom <- getDomain v
		rs <- (mapM reviseD $ Set.toList dom)
		return (or rs)
		where
			reviseD :: d -> GACState v d Bool
			reviseD d = do
				mt <- getLast ((v,d), c)
				ok <- case mt of
					Just t -> testTuple t
					Nothing -> return False
				if ok
				then return False
				else do
					dom <- getDomain v
					setDomain v (Set.singleton d)
					doms <- getDomains c
					case nextOkTuple (meetsConstraint c) doms mt of
						Just t' -> do
							setLast ((v,d), c) t'
							setDomain v dom
							return False
						Nothing -> do
							setDomain v (Set.delete d dom)
							return True
							
			testTuple (Tuple ts) = do 
				doms <- getDomains c
				return $ all (\(v', d') -> Set.member v' d') (zip ts doms)
				
			getDomains (Constraint (Tuple ts, _)) = do
				mapM getDomain ts	
	
	getLast :: (Ord v, Ord d) => ((v, d), Constraint v d) -> GACState v d (Maybe (Tuple d))
	getLast k = do
		(Last m, _) <- get
		return $ Map.lookup k m
		
	setLast :: (Ord v, Ord d) => ((v, d), Constraint v d) -> Tuple d -> GACState v d ()
	setLast k t = do
		(Last m, sol) <- get
		put (Last $ Map.insert k t m, sol)
		
	getDomain :: (Ord v) => v -> GACState v d (Set d)
	getDomain v = do
		(_, sol) <- get
		return (PS.domain sol v)
		
	setDomain :: (Ord v) => v -> Set d -> GACState v d ()
	setDomain v ds = do
		(last, sol) <- get
		put (last, PS.setDomain v ds sol)
		
	allConstraints :: (Ord rname) => Structure rname v -> Structure rname d -> [Constraint v d]
	allConstraints vstr dstr =
		concatMap 
			(\rname -> 
				map 
					(\t -> Constraint (t, relationTuples dstr rname)) 
					(Set.toList $ relationTuples vstr rname)) 
			(relationNames $ signature vstr)
	
	meetsConstraint :: (Ord d) => Constraint v d -> Tuple d -> Bool
	meetsConstraint (Constraint (_,ds)) t = Set.member t ds
	
	constraintVars :: Constraint v d -> [v]
	constraintVars (Constraint (Tuple vs, _)) = vs
	
	emptyLast :: Last v d
	emptyLast = Last Map.empty
	
	nextOkTuple :: (Ord v) => (Tuple v -> Bool) -> [Set v] -> Maybe (Tuple v) -> Maybe (Tuple v)
	nextOkTuple c s mt =
		case mt of
			Just t -> nextTuple s t >>= okTuple
			Nothing -> firstTuple s >>= okTuple
		where
			okTuple t =
				if c t 
				then Just t 
				else nextOkTuple c s (Just t)
	
