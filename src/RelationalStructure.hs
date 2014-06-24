-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module RelationalStructure where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List

	import Utils
	
	
	newtype Signature rname = Signature (Map rname Arity) deriving (Show, Eq, Ord)
	
	
	newtype Relation rname element = 
		Relation (rname, Arity, Set (Tuple element))
		deriving (Show, Eq, Ord)
	
	
	newtype Structure rname element = 
		Structure (Signature rname, Set element, Map rname (Relation rname element))
		deriving (Show, Eq, Ord)
	
	
	stats :: Structure rname element -> String
	stats (Structure (Signature sigMap, elems, _)) =
		"rels: " ++ show (Map.size sigMap) ++ ", elems: " ++ show (Set.size elems)
	
	
	sigFromList :: (Ord rname) => [(rname, Arity)] -> Signature rname
	sigFromList = Signature . Map.fromList
	
	
	sigFromRels :: (Ord rname) => [Relation rname element] -> Signature rname
	sigFromRels rels =
		Signature $ Map.fromList (map (\(Relation (rname, ar, _)) -> (rname, ar)) rels)

	
	relationArity :: (Ord rname) => Signature rname -> rname -> Arity
	relationArity (Signature arMap) rname = arMap ! rname
	
	
	containsRelation :: (Ord rname) => Signature rname -> rname -> Bool
	containsRelation (Signature arMap) rname = (Map.lookup rname arMap /= Nothing)

	
	relationNames :: Signature rname -> [rname]
	relationNames (Signature arMap) = Map.keys arMap

	
	createRelation 
		:: (Ord element) 
		=> rname 
		-> Arity 
		-> Set element 
		-> (Tuple element -> Bool) 
		-> Relation rname element
		
	createRelation rname (Arity ar) elts fun =
		Relation (rname, Arity ar, Set.filter fun tuples)
		where
			tuples = cartesianPower elts ar
	
	
	createStructure 
		:: (Ord rname)
		=> Signature rname 
		-> Set element 
		-> [Relation rname element] 
		-> Structure rname element
		
	createStructure sig elts rels =
		Structure (sig, elts, rel_map)
		where
			rel_map = 
				Map.fromList 
					(map (\(Relation (rname', arity', elts')) -> (rname', Relation (rname', arity', elts'))) rels)
		
		
	structureElems :: Structure rname element -> Set element
	structureElems (Structure (_, elts, _)) = elts
	
	
	signature :: Structure rname element -> Signature rname
	signature (Structure (sig, _, _)) = sig
		
				
	expectRelation :: (Ord rname, Show rname) => Signature rname -> rname -> Arity -> a -> a
	expectRelation (Signature sigMap) rname ar a =
		case Map.lookup rname sigMap of
			Just ar' -> 
				if ar == ar' 
				then a 
				else error ("Wrong arity of relation " ++ show rname)
			Nothing -> error ("No such relation " ++ show rname)			
			
			
	isInRelation 
		:: (Ord rname, Show rname, Ord element) 
		=> Structure rname element 
		-> rname 
		-> Tuple element 
		-> Bool
		
	isInRelation (Structure (sig, _, rels)) rname t =
		expectRelation sig rname (arity t) (Set.member t tuple_set)
		where
			(Relation (_, _, tuple_set)) = Map.findWithDefault (Relation (rname, Arity 0, Set.empty)) rname rels
			
			
	filterRelations :: (Ord rname) => Signature rname -> Structure rname element -> Structure rname element
	filterRelations sig (Structure (_, elts, relMap)) =
		Structure (sig, elts, relMap')
		where
			relMap' = Map.filterWithKey (\rname _ -> containsRelation sig rname) relMap
			
			
	addRelation 
		:: (Ord rname, Ord element) 
		=> Relation rname element 
		-> Structure rname element
		-> Structure rname element
		
	addRelation rel (Structure (Signature sigMap, elts, rels)) =
		(Structure (sig', elts, rels'))
		where
			Relation (rname, ar, _) = rel
			sig' = Signature $ Map.insert rname ar sigMap
			rels' = Map.insert rname rel rels
			
			
	renameRelations 
		:: (Ord rname, Ord element, Ord rname') 
		=> (rname -> rname') 
		-> Structure rname element 
		-> Structure rname' element
		
	renameRelations f (Structure (Signature sigMap, elts, rels)) =
		Structure (sig', elts, rels')
		where
			sig' = Signature $ Map.mapKeys f sigMap
			rels' = 
				Map.mapKeys f 
					(Map.map (\(Relation (rname, ar, tuples)) -> Relation (f rname, ar, tuples)) rels)
			
			
	isHomomorphism 
		:: (Ord rname, Ord e1, Ord e2) 
		=> Structure rname e1 
		-> Structure rname e2 
		-> (e1 -> e2) 
		-> Bool
		
	isHomomorphism (Structure (sig1, elts1, rels1)) (Structure (sig2, elts2, rels2)) fun =
		if sig1 /= sig2 
		then
			error "Signature mismatch"
		else
			mapsAll && preservesRelations
		where
			mapsAll = all (\e1 -> Set.member (fun e1) elts2) (Set.toList elts1)
				
			preservesRelation rname =
				all (\t1 -> Set.member (mapTuple fun t1) tuples2) (Set.toList tuples1)
				where
					Relation (_, _, tuples1) = rels1 ! rname
					Relation (_, _, tuples2) = rels2 ! rname
					
			preservesRelations = all preservesRelation (relationNames sig1)
			
			
	addToRelation 
		:: (Ord element, Ord rname) 
		=> rname
		-> Arity
		-> [Tuple element]
		-> Structure rname element
		-> Structure rname element
		
	addToRelation rname ar tuples (Structure (sig, elts, rels)) =
		Structure (sig, elts, rels')
		where
			rels' = 
				Map.insertWith 
					(\(Relation (rname', ar', ts1)) (Relation (_, _, ts2)) -> Relation (rname', ar', Set.union ts1 ts2)) 
					rname 
					(Relation (rname, ar, Set.fromList tuples))
					rels
	
	
	elementsFromRels :: (Ord element) => [Relation rname element] -> Set element
	elementsFromRels rels =
		Set.unions $ map
			(\(Relation (_, _, ts)) -> Set.unions $ map (\(Tuple t) -> Set.fromList t) $ Set.toList ts)
			rels
	
	resetElements :: (Ord element, Ord rname) => Structure rname element -> Structure rname element
	resetElements (Structure (sig, _, rels)) = 
		Structure (sig, elementsFromRels (Map.elems rels), rels)
	
	
	substructure 
		:: (Ord element) 
		=> Structure rname element 
		-> Set element 
		-> Structure rname element
		
	substructure (Structure (sig, elts, rels)) elts' =
		if (Set.isSubsetOf elts' elts)
		then Structure (sig, elts', rels')
		else error "Not a subset"
		where
			rels' = Map.map filterRelation rels 
			filterRelation (Relation (rname, ar, tuples)) =
				Relation (rname, ar, Set.filter (\(Tuple t) -> all (\e -> Set.member e elts') t) tuples)
	
	
	structPower 
		:: forall element rname. (Ord element) 
		=> Structure rname element 
		-> Int 
		-> Structure rname (Tuple element)
		
	structPower (Structure (sig, elts, rels)) i =
		Structure (sig, elts', rels')
		where
			elts' = cartesianPower elts i
			
			transform_relation :: Relation rname element -> Relation rname (Tuple element)
			transform_relation (Relation (rname, ar, set)) =
				Relation (rname, ar, set')
				where
					set' = Set.map tupleTranspose (cartesianPower set i)
					tupleTranspose (Tuple ts) = 
						Tuple $ map Tuple $ List.transpose $ map (\(Tuple t) -> t) ts

			rels' = Map.map transform_relation rels

