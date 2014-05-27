-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module RelationalStructure where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	

	type Arity = Int
	
	type Signature rname = Map rname Arity
	
	type Tuple element = [element]
	
	type Relation rname element = 
		(rname, Arity, Set (Tuple element))
	
	type Structure rname element = 
		(Signature rname, Set element, Map rname (Relation rname element))
		
	stats :: Structure rname element -> String
	stats (sig, elems, _) =
		"rels: " ++ show (Map.size sig) ++ ", elems: " ++ show (Set.size elems)
	
	
	sigFromList :: (Ord rname) => [(rname, Arity)] -> Signature rname
	sigFromList = Map.fromList
	
	
	sigFromRels :: (Ord rname) => [Relation rname element] -> Signature rname
	sigFromRels rels =
		Map.fromList (map (\(rname, ar, _) -> (rname, ar)) rels)
		
		
	cartesian :: (Ord a) => Set (Tuple a) -> Set (Tuple a) -> Set (Tuple a)
	cartesian set1 set2 =
		Set.unions (map (\t1 -> Set.map (\t2 -> t1 ++ t2) set2) (Set.toList set1))
	
		
	cartesianPower :: (Ord a) => Set a -> Int -> Set (Tuple a)
	cartesianPower set i = 
		cartesianPower' set' i empty
		where
			empty = Set.fromList [[]]
			set' = Set.map (\a -> [a]) set
			cartesianPower' set' i tail =
				if i <= 0
				then tail
				else cartesianPower' set' (i-1) (cartesian set' tail)
				
	
	relationArity :: (Ord rname) => Signature rname -> rname -> Arity
	relationArity sig rname = sig ! rname

	
	relationNames :: Signature rname -> [rname]
	relationNames sig = Map.keys sig

	
	createRelation 
		:: (Ord element) 
		=> rname 
		-> Arity 
		-> Set element 
		-> (Tuple element -> Bool) 
		-> Relation rname element
		
	createRelation rname ar elts fun =
		(rname, ar, Set.filter fun tuples)
		where
			tuples = cartesianPower elts ar
		
			
	checkRelation :: (Ord element) => Set element -> Relation rname element -> Bool
	checkRelation elts (_, ar, tuples) =
		all check_tuple (Set.toList tuples)
		where
			check_tuple t =
				(length t == ar) && (all (\e -> Set.member e elts) t)
	
	
	createStructure 
		:: (Ord rname)
		=> Signature rname 
		-> Set element 
		-> [Relation rname element] 
		-> Structure rname element
		
	createStructure sig elts rels =
		(sig, elts, rel_map)
		where
			rel_map = 
				Map.fromList 
					(map (\(rname, arity, elts) -> (rname, (rname, arity, elts))) rels)
	
	
	checkStructure :: (Ord rname, Ord element) => Structure rname element -> Bool
	checkStructure (sig, elts, rel_map) =
		(Map.keysSet sig == Map.keysSet rel_map)
		&& (all (\(rname, (rname', ar, tuples)) -> 
			(ar == relationArity sig rname) 
			&& checkRelation elts (rname', ar, tuples)) (Map.toList rel_map))
		
		
	elements :: Structure rname element -> Set element
	elements (_, elts, _) = elts
	
	signature :: Structure rname element -> Signature rname
	signature (sig, _, _) = sig
		
		
	expectRelation :: (Ord rname, Show rname) => Signature rname -> rname -> Arity -> a -> a
	expectRelation sig rname ar a =
		case Map.lookup rname sig of
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
		
	isInRelation (sig, _, rels) rname t =
		expectRelation sig rname (length t) (Set.member t tuple_set)
		where
			(_, _, tuple_set) = Map.findWithDefault (rname, 0, Set.empty) rname rels
			
			
	filterRelations :: (Ord rname) => Signature rname -> Structure rname element -> Structure rname element
	filterRelations sig (_, elts, relMap) =
		(sig, elts, relMap')
		where
			relMap' = Map.filterWithKey (\rname _ -> Map.lookup rname sig /= Nothing) relMap
			
			
	addRelation 
		:: (Ord rname, Ord element) 
		=> Relation rname element 
		-> Structure rname element
		-> Structure rname element
		
	addRelation rel (sig, elts, rels) =
		(sig', elts, rels')
		where
			(rname, ar, tuples) = rel
			sig' = Map.insert rname ar sig
			rels' = Map.insert rname rel rels
			
			
	renameRelations 
		:: (Ord rname, Ord element, Ord rname') 
		=> (rname -> rname') 
		-> Structure rname element 
		-> Structure rname' element
		
	renameRelations f (sig, elts, rels) =
		(sig', elts, rels')
		where
			sig' = Map.mapKeys f sig
			rels' = 
				Map.mapKeys f 
					(Map.map (\(rname, ar, tuples) -> (f rname, ar, tuples)) rels)
			
			
	isHomomorphism 
		:: (Ord rname, Ord e1, Ord e2) 
		=> Structure rname e1 
		-> Structure rname e2 
		-> (e1 -> e2) 
		-> Bool
		
	isHomomorphism (sig1, elts1, rels1) (sig2, elts2, rels2) fun =
		if sig1 /= sig2 
		then
			error "Signature mismatch"
		else
			mapsAll && preservesRelations
		where
			mapsAll = all (\e1 -> Set.member (fun e1) elts2) (Set.toList elts1)
				
			preservesRelation rname =
				all (\t1 -> Set.member (map fun t1) tuples2) (Set.toList tuples1)
				where
					(_, _, tuples1) = rels1 ! rname
					(_, _, tuples2) = rels2 ! rname
					
			preservesRelations = all preservesRelation (relationNames sig1)
			
			
	addToRelation 
		:: (Ord element, Ord rname) 
		=> rname
		-> Arity
		-> [Tuple element]
		-> Structure rname element
		-> Structure rname element
		
	addToRelation rname ar tuples (sig, elts, rels) =
		(sig, elts, rels')
		where
			rels' = 
				Map.insertWith 
					(\(rname, ar, ts1) (_, _, ts2) -> (rname, ar, Set.union ts1 ts2)) 
					rname 
					(rname, ar, Set.fromList tuples) 
					rels
	
	elementsFromRels :: (Ord element) => [Relation rname element] -> Set element
	elementsFromRels rels =
		Set.unions $ map
			(\(_, _, ts) -> Set.unions $ map Set.fromList $ Set.toList ts)
			rels
	
	resetElements :: (Ord element, Ord rname) => Structure rname element -> Structure rname element
	resetElements (sig, _, rels) = 
		(sig, elementsFromRels (Map.elems rels), rels)
	
	substructure 
		:: (Ord element) 
		=> Structure rname element 
		-> Set element 
		-> Structure rname element
		
	substructure (sig, elts, rels) elts' =
		if (Set.isSubsetOf elts' elts)
		then (sig, elts', rels')
		else error "Not a subset"
		where
			rels' = Map.map filterRelation rels 
			filterRelation (rname, ar, tuples) =
				(rname, ar, Set.filter (\t -> all (\e -> Set.member e elts') t) tuples)
	
	
	structPower 
		:: forall element rname. (Ord element) 
		=> Structure rname element 
		-> Int 
		-> Structure rname (Tuple element)
		
	structPower (sig, elts, rels) i =
		(sig, elts', rels')
		where
			elts' = cartesianPower elts i
			
			transform_relation :: Relation rname element -> Relation rname (Tuple element)
			transform_relation (rname, ar, set) =
				(rname, ar, set')
				where
					set' = Set.map List.transpose (cartesianPower set i)

			rels' = Map.map transform_relation rels

