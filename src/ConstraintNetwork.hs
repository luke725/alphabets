-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module ConstraintNetwork where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import Debug.Trace

	import RelationalStructure
	import Utils

	data ConstraintNetwork v d = 
		ConstraintNetwork 
			{ coreElems :: Set v
			, domainMap :: Map v (Set d)
			, constraintMap :: Map (v, v) (Set (d, d)) -- symmetric
			, neighborsMap :: Map v (Set v)
			} deriving Show
	 
	data CSPType e = CSPElem e | CSPTuple (Tuple e) deriving (Show, Eq, Ord)
	
	cnStats :: ConstraintNetwork v d -> String
	cnStats cn =
		"core elems: " 
		++ show (Set.size $ coreElems cn) 
		++ ", all: " 
		++ show (List.length $ Map.keys $ constraintMap cn)  
		++ ",nbs: " ++ show (sum $ map Set.size $ Map.elems $ constraintMap cn)
		
	translate :: (Ord v, Ord d) => ConstraintNetwork v d -> (ConstraintNetwork Int Int, Map Int v, Map Int d)
	translate cn =
		(ConstraintNetwork 
			{ coreElems = coreElems'
			, domainMap = domainMap'
			, constraintMap = constraintMap'
			, neighborsMap = neighborsMap'
			},
		 Map.fromList $ zip [1..length elemsV] elemsV,
		 Map.fromList $ zip [1..length elemsD] elemsD)
		where
			elemsV = Set.toList $ Set.fromList (elemsVcm ++ elemsVce ++ elemsVdm ++ elemsVnm)
			elemsVcm = concatMap (\(v1, v2) -> [v1, v2]) $ Map.keys $ constraintMap cn 
			elemsVce = Set.toList $ coreElems cn
			elemsVdm = Map.keys $ domainMap cn
			elemsVnm = Map.keys $ neighborsMap cn
			
			elemsD = Set.toList $ Set.fromList (elemsDcm ++ elemsDdm)
			elemsDdm = Set.toList $ Set.unions $ Map.elems $ domainMap cn	
			elemsDcm = Set.toList $ Map.fold (\ds s -> Set.fold (\(d1, d2) s' -> Set.insert d1 $ Set.insert d2 s') s ds) Set.empty $ constraintMap cn
			
			mapV = Map.fromList $ zip elemsV [1..length elemsV]
			mapD = Map.fromList $ zip elemsD [1..length elemsD]
			coreElems' = Set.map (\e -> mapV ! e) $ coreElems cn
			domainMap' = Map.mapKeys (\e -> mapV ! e) $ Map.map (Set.map (\e -> mapD ! e)) $ domainMap cn
			constraintMap' = Map.mapKeys (\(e1, e2) -> (mapV ! e1, mapV ! e2)) $ Map.map (Set.map (\(e1, e2) -> (mapD ! e1, mapD ! e2))) $ constraintMap cn
			neighborsMap' = Map.mapKeys (\e -> mapV ! e) $ Map.map (Set.map (\e -> mapV ! e)) $ neighborsMap cn
	
	create :: (Ord v, Ord d) => Set v -> Map v (Set d) -> Map (v, v) (Set (d, d)) -> ConstraintNetwork v d
	create coreElems' domainMap' constraintMap' =
		trace (cnStats cn) cn
		where
			cn = ConstraintNetwork
				{ coreElems = coreElems',
				  domainMap = domainMap', 
				  constraintMap = symConstraintMap, 
				  neighborsMap = neighborsMap'
				}
			symConstraintMap =
				foldl 
					(\m ((v1, v2), s) -> 
						Map.insertWith Set.intersection 
							(v2, v1) 
							(Set.map (\(d1, d2) -> (d2, d1)) s) 
							m
					)
					constraintMap'
					(Map.toList constraintMap')
					
			neighborsMap' =
				foldl 
					(\m (v1, v2) -> Map.insertWith Set.union v1 (Set.singleton v2) m) 
					Map.empty 
					(Map.keys symConstraintMap)
	
	
	variables :: ConstraintNetwork v d -> [v]
	variables cn = Map.keys (domainMap cn)
	
	
	domain :: (Ord v) => ConstraintNetwork v d -> v -> Set d
	domain cn v =
		domainMap cn ! v
	
	
	constraint :: (Ord v) => ConstraintNetwork v d -> (v, v) -> Set (d, d)
	constraint cn vs =
		constraintMap cn ! vs
	
	
	neighbors :: (Ord v) => ConstraintNetwork v d -> v -> Set v
	neighbors cn v =
		Map.findWithDefault Set.empty v (neighborsMap cn)
		
	 
	fromCSP :: forall rname v d. (Ord rname, Ord d, Ord v) => Structure rname v -> Structure rname d -> ConstraintNetwork (CSPType v) (CSPType d)
	fromCSP (Structure (Signature sigMap, eltsV, relMapV)) (Structure (_, eltsD, relMapD)) =
		create coreElems' domainMap' constraintMap'
		where
			nonUnaryRels = 
				map (\(rname, _) -> rname) $ filter (\(_, Arity ar) -> ar > 1) (Map.toList sigMap)
				
			unaryRels =
				map (\(rname, _) -> rname) $ filter (\(_, Arity ar) -> ar == 1) (Map.toList sigMap)
			
			buildRestList :: Set a -> Set b -> [(a, Set b)]
			buildRestList sa sb =
				map (\v -> (v, sb)) (Set.toList sa)
				
			mapFromRestList :: (Ord a, Ord b) => [(a, Set b)] -> Map a (Set b)
			mapFromRestList =
				foldl
					(\m (k, s) -> Map.insertWith Set.intersection k s m)
					Map.empty
			
			unaryRelRestList :: rname -> [(v, Set d)]
			unaryRelRestList rname =
				buildRestList elsV elsD
				where
					Relation (_, _, tsV) = relMapV ! rname
					Relation (_, _, tsD) = relMapD ! rname
					elsV = Set.map (\(Tuple [v]) -> v) tsV
					elsD = Set.map (\(Tuple [d]) -> d) tsD
					
			relRestList :: rname -> [(Tuple v, Set (Tuple d))]
			relRestList rname =
				buildRestList tsV tsD
				where
					Relation (_, _, tsV) = relMapV ! rname
					Relation (_, _, tsD) = relMapD ! rname
							
				
			domainEltsList =
				map (\e -> (e, eltsD)) (Set.toList eltsV)
				++ concatMap unaryRelRestList unaryRels
				
			domainTuplesList =
				concatMap relRestList nonUnaryRels
				
			coreElems' = 
				Set.fromList $ map (\(v, _) -> CSPElem v) domainEltsList
				
			domainMap' =
				mapFromRestList
					(map (\(x, s) -> (CSPElem x, Set.map CSPElem s)) domainEltsList 
					 ++ map (\(x, s) -> (CSPTuple x, Set.map CSPTuple s)) domainTuplesList)
					 
			constraintsFromRel :: rname -> [((CSPType v, CSPType v), Set (CSPType d, CSPType d))]
			constraintsFromRel rname =
				concatMap (\i -> buildRestList (tupleRel i tsV) (tupleRel i tsD)) [0..ar-1]
				where
					Arity ar = sigMap!rname
					Relation (_, _, tsV) = relMapV ! rname
					Relation (_, _, tsD) = relMapD ! rname
					
					tupleRel i ts =
						Set.map (\(Tuple t) -> (CSPElem (t !! i), CSPTuple (Tuple t))) ts
						
			constraintMap' = 
				mapFromRestList
					(concatMap constraintsFromRel nonUnaryRels)	
	
		
		
