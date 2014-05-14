-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module ConstraintNetwork where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List

	import RelationalStructure

	data ConstraintNetwork v d = 
		ConstraintNetwork 
			{ domainMap :: Map v (Set d)
			, constraintMap :: Map (v, v) (Set (d, d)) -- symmetric
			, neighborsMap :: Map v (Set v)
			} deriving Show
	
	data CSPType e = CSPElem e | CSPTuple (Tuple e) deriving (Show, Eq, Ord)
	
	create :: (Ord v, Ord d) => Map v (Set d) -> Map (v, v) (Set (d, d)) -> ConstraintNetwork v d
	create domainMap' constraintMap' =
		ConstraintNetwork
			{ domainMap = domainMap', 
			  constraintMap = symConstraintMap, 
			  neighborsMap = neighborsMap'
			}
		where
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
	fromCSP (sig, eltsV, relMapV) (_, eltsD, relMapD) =
		create domainMap constraintMap
		where
			nonUnaryRels = 
				map (\(rname, _) -> rname) $ filter (\(_, ar) -> ar > 1) (Map.toList sig)
				
			unaryRels =
				map (\(rname, _) -> rname) $ filter (\(_, ar) -> ar == 1) (Map.toList sig)
				
			tuples (_, _, ts) = ts
			
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
					(_, _, tsV) = relMapV ! rname
					(_, _, tsD) = relMapD ! rname
					elsV = Set.map (\[v] -> v) tsV
					elsD = Set.map (\[d] -> d) tsD
					
			relRestList :: rname -> [(Tuple v, Set (Tuple d))]
			relRestList rname =
				buildRestList tsV tsD
				where
					(_, _, tsV) = relMapV ! rname
					(_, _, tsD) = relMapD ! rname
							
				
			domainEltsList =
				map (\e -> (e, eltsD)) (Set.toList eltsV)
				++ concatMap unaryRelRestList unaryRels
				
			domainTuplesList =
				concatMap relRestList nonUnaryRels
				
			domainMap =
				mapFromRestList
					(map (\(x, s) -> (CSPElem x, Set.map CSPElem s)) domainEltsList 
					 ++ map (\(x, s) -> (CSPTuple x, Set.map CSPTuple s)) domainTuplesList)
					 
			constraintsFromRel :: rname -> [((CSPType v, CSPType v), Set (CSPType d, CSPType d))]
			constraintsFromRel rname =
				concatMap (\i -> buildRestList (tupleRel i tsV) (tupleRel i tsD)) [0..arity-1]
				where
					domList = relRestList rname
					arity = sig!rname
					(_, _, tsV) = relMapV ! rname
					(_, _, tsD) = relMapD ! rname
					
					tupleRel i ts =
						Set.map (\t -> (CSPElem (t !! i), CSPTuple t)) ts
						
			constraintMap = 
				mapFromRestList
					(concatMap constraintsFromRel nonUnaryRels)	
	
		
		