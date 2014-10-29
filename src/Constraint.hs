module Constraint where
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map)
	import qualified Data.Map as Map

	import Utils
	import RelationalStructure
	
	-- Constraint (tv, ds) means that the tuple tv can only be mapped to elements of ds
	newtype Constraint v d = Constraint (Tuple v, Set (Tuple d)) deriving (Show, Eq, Ord)
	
	-- data needed for AC2001 algorithm
	-- carries the same information a set of structure where elements have type v and d,
	-- but speeds up the computation
	-- first element is a set of all pairs (v, c), where v \in vars(c)
	-- second element is a map v |-> l, where l is the list of all (v', c) where v != v' and v, v' \in vars(c)
	type CSPData v d = (Set (v, Constraint v d), Map v [(v, Constraint v d)])
	
	createCspData :: (Ord v, Ord d, Ord rname) => Structure rname v -> Structure rname d -> CSPData v d
	createCspData vstr dstr =
		(Set.fromList allCs, mapCs)
		where
			conPairs c = map (\v -> (v, c)) (vars c)
			allCs = concatMap conPairs $ allConstraints vstr dstr
			mapCs = 
				foldl (\m (v, vc) -> Map.insertWith (++) v [vc] m) Map.empty 
				$ concatMap (\(v, c) -> map (\v' -> (v, (v',c))) (vars c))
				$ allCs
				
	allConstraints :: (Ord rname, Ord v, Ord d) => Structure rname v -> Structure rname d -> [Constraint v d]
	allConstraints vstr dstr =
		removeDuplicates
		$ concatMap relationConstraints
		$ relationNames
		$ structureSig vstr
		where
			relationConstraints rname =
				map (\t -> Constraint (t, relationTuples dstr rname)) 
				$ Set.toList 
				$ relationTuples vstr rname
	
	meetsConstraint :: (Ord d) => Constraint v d -> Tuple d -> Bool
	meetsConstraint (Constraint (_,ds)) t = Set.member t ds
	
	vars :: Constraint v d -> [v]
	vars (Constraint (Tuple vs, _)) = vs
	
	removeDuplicates :: (Ord v, Ord d) => [Constraint v d] -> [Constraint v d]
	removeDuplicates cs =
		map Constraint
		$ Map.toList
		$ foldl (\m (Constraint (vt, dts)) -> Map.insertWith Set.intersection vt dts m) Map.empty cs
		
	nextTupleMeetingConstraint :: (Ord v) => Constraint v' v -> [Set v] -> Maybe (Tuple v) -> Maybe (Tuple v)
	nextTupleMeetingConstraint c s mt =
		case mt of
			Just t -> nextTuple s t >>= okTuple
			Nothing -> firstTuple s >>= okTuple
		where
			okTuple t =
				if meetsConstraint c t 
				then Just t 
				else nextTupleMeetingConstraint c s (Just t)
