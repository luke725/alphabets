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
	stats (Structure (Signature sigMap, elems, relMap)) =
		"rels: " ++ show (Map.size sigMap) ++ ", elems: " ++ show (Set.size elems) ++ ", max rel size: " ++ show maxSize
		where
			maxSize =
				List.maximum
				$ (\l -> 0:l)
				$ map (\(Relation (_, _, ts)) -> Set.size ts) 
				$ filter (\(Relation (_, Arity r, _)) -> r > 1) 
				$ Map.elems relMap
	
	
	sigFromRels :: (Ord rname) => [Relation rname element] -> Signature rname
	sigFromRels rels =
		Signature $ Map.fromList (map (\(Relation (rname, ar, _)) -> (rname, ar)) rels)

	
	relationArity :: (Ord rname) => Signature rname -> rname -> Arity
	relationArity (Signature arMap) rname = arMap ! rname
	
	
	containsRelation :: (Ord rname) => Signature rname -> rname -> Bool
	containsRelation (Signature arMap) rname = (Map.lookup rname arMap /= Nothing)
	
	getRelation :: (Ord rname) => Structure rname element -> rname -> Relation rname element
	getRelation (Structure (_, _, relMap)) rname = relMap ! rname

	
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
		Structure (sig, elts, relMap)
		where
			relMap = 
				Map.fromList 
				$ map (\(Relation (rname', arity', elts')) -> (rname', Relation (rname', arity', elts'))) 
				$ rels
		
	structureFromRels :: (Ord rname, Ord element) => [Relation rname element] -> Structure rname element
	structureFromRels rels =
		createStructure (sigFromRels rels) (elementsFromRels rels) rels
		
	structureElems :: Structure rname element -> Set element
	structureElems (Structure (_, elts, _)) = elts
	
	
	structureSig :: Structure rname element -> Signature rname
	structureSig (Structure (sig, _, _)) = sig
	
	
	relationTuples :: (Ord rname) => Structure rname element -> rname -> Set (Tuple element)
	relationTuples (Structure (_, _, relMap)) rname =
		relSet
		where
			Relation (_, _, relSet) = relMap!rname
			
			
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
			
	addRelations
		:: (Ord rname, Ord element) 
		=> [Relation rname element]
		-> Structure rname element
		-> Structure rname element
		
	addRelations rels str =
		foldl (\str' rel -> addRelation rel str') str rels
		
--	expandSignature :: (Ord rname, Ord element) => Signature rname -> Structure rname element -> Structure rname element
--	expandSignature (Signature sigMap) str =
		
		
	removeUnaryRelations :: (Ord rname, Ord element) => Structure rname element -> Structure rname element
	removeUnaryRelations (Structure (Signature sigMap, els, relMap)) =
		Structure (Signature sigMap', els, relMap')
		where
			sigMap' = Map.filter (\(Arity r) -> (r > 1)) sigMap
			relMap' = Map.filter (\(Relation (_, (Arity r), _)) -> (r > 1)) relMap
			
			
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
				$ Map.map (\(Relation (rname, ar, tuples)) -> Relation (f rname, ar, tuples)) 
				$ rels
			
			
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
			all (\e1 -> Set.member (fun e1) elts2) (Set.toList elts1) 
			&& all preservesRelation (relationNames sig1)
		where
			preservesRelation rname =
				all (\t1 -> Set.member (mapTuple fun t1) tuples2) (Set.toList tuples1)
				where
					Relation (_, _, tuples1) = rels1 ! rname
					Relation (_, _, tuples2) = rels2 ! rname
			
			
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
		Set.unions 
		$ map (\(Relation (_, _, ts)) -> Set.unions $ map (\(Tuple t) -> Set.fromList t) $ Set.toList ts)
		$ rels
	
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
				
				
	filterStructure :: (Ord element) => (element -> Bool) -> Structure rname element -> Structure rname element
	filterStructure f (Structure (sig, elts, rels)) =
		substructure (Structure (sig, elts, rels)) (Set.filter f elts)
	
	
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


	mapStructure :: (Ord e1, Ord e2, Ord rname) => (e1 -> e2) -> Structure rname e1 -> Structure rname e2
	mapStructure f (Structure (sig, elts, rels)) =
		Structure (sig, Set.map f elts, Map.map mapRel rels)
		where
			mapRel (Relation (rname, ar, tuples)) = 
				Relation (rname, ar, Set.map (\(Tuple xs) -> Tuple $ map f xs) tuples)

	sigMapToInt :: (Ord rname) => Signature rname -> Map rname Int
	sigMapToInt (Signature sigMap) =
		Map.fromList $ zip (Map.keys sigMap) [1..Map.size sigMap]

	-- isomorphic structure where elements have type Int
	intStructure
		:: forall element rname. (Ord element, Ord rname)
		=> Structure rname element
		-> (Structure rname Int, Map Int element, Map element Int)
		
	intStructure str =
		(mapStructure (\e -> map2!e) str, map1, map2)
		where
			elts = structureElems str
			eltsZipList = zip [1..Set.size elts] $ Set.toList elts
			map1 = Map.fromList eltsZipList
			map2 = Map.fromList $ map (\(a, b) -> (b, a)) eltsZipList
 
