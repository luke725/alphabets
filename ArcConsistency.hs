-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module ArcConsistency where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import RelationalStructure
	import Debug.Trace

	
	type PossibleSolutions a b = Map a (Set b)


	fullPossibleSolutions 
		:: Ord a 
		=> Structure rname a 
		-> Structure rname b 
		-> PossibleSolutions a b

	fullPossibleSolutions (_, elts1, _) (_, elts2, _) =
		Map.fromList (map (\e1 -> (e1, elts2)) (Set.toList elts1))
		
		
	notEmpty :: PossibleSolutions a b -> Bool
	notEmpty sol =
		all (\set -> not (Set.null set)) (Map.elems sol)
		
		
	checkArcConsistency 
		:: (Ord rname, Ord a, Ord b, Show rname, Show a, Show b) 
		=> Structure rname a 
		-> Structure rname b 
		-> Bool
		
	checkArcConsistency s1 s2 =
		notEmpty (runArcConsistency s1 s2 (fullPossibleSolutions s1 s2))
		
		
	runArcConsistency
		:: forall rname a b. (Ord rname, Ord a, Ord b, Show rname, Show a, Show b)
		=> Structure rname a 
		-> Structure rname b 
		-> PossibleSolutions a b 
		-> PossibleSolutions a b
		
	runArcConsistency s1 s2 sol =
		if sol' == sol
		then sol
		else runArcConsistency s1 s2 sol'
		where
			sol' = stepAC s1 s2 sol
			
			
	stepAC 
		:: forall rname a b. (Ord rname, Ord a, Ord b, Show rname, Show a, Show b)
		=> Structure rname a
		-> Structure rname b 
		-> PossibleSolutions a b 
		-> PossibleSolutions a b
		
	stepAC (sig1, elts1, rels1) (sig2, elts2, rels2) sol =
		foldl 
			(\sol (tuple1, rel2) -> stepTuple tuple1 rel2 sol)
			sol
			(concatMap 
				(\rname -> (map (\t -> (t, rels2!rname)) (relationTuples rels1 rname))) 
				(relationNames sig1))
		where	
			relationTuples rels name = Set.toList tuples 
				where 
					(_, _, tuples) = rels ! name
			
			stepTuple 
				:: Tuple a 
				-> Relation rname b 
				-> PossibleSolutions a b 
				-> PossibleSolutions a b
		
			stepTuple t1 rel2 sol =
				(Map.union newPosSol sol)
				where
					(_, _, tuples2) = rel2
		
					zipTuples :: [Tuple (a, b)]
					zipTuples = map (\t2 -> zip t1 t2) (Set.toList tuples2)
			
					possiblePartSol :: [Tuple (a, b)]
					possiblePartSol = filter (all (\(a, b) -> Set.member b (sol!a))) zipTuples
			
					newPosSol =
						foldl 
							(\m (a, b) -> Map.insertWith Set.union a (Set.singleton b) m)
							(Map.fromList (map (\a -> (a, Set.empty)) t1))
							(concat possiblePartSol)
							
	
	checkSAC 
		:: (Ord rname, Ord a, Ord b, Show rname, Show a, Show b)
		=> Structure rname a 
		-> Structure rname b 
		-> Bool
		
	checkSAC s1 s2 =
		notEmpty (runSAC s1 s2 (fullPossibleSolutions s1 s2))
		
		
	runSAC 
		:: (Ord rname, Ord a, Ord b, Show rname, Show a, Show b) 
		=> Structure rname a 
		-> Structure rname b 
		-> PossibleSolutions a b 
		-> PossibleSolutions a b
		
	runSAC s1 s2 sol =
		if sol' == sol
		then sol
		else runSAC s1 s2 sol'
		where
			sol' = 
				Map.mapWithKey 
					(\a -> Set.filter 
						(\b -> notEmpty (runArcConsistency s1 s2 (Map.insert a (Set.singleton b) sol)))
					) 
					sol
		
				
	findSACSolution
			:: forall rname a b.(Ord rname, Ord a, Ord b, Show rname, Show a, Show b)
			=> Structure rname a 
			-> Structure rname b 	
			-> Maybe (Map a b)
			
	findSACSolution s1 s2 =
		case sacIt s1 s2 (fullPossibleSolutions s1 s2) (Set.toList (elements s1)) of
			Just sol -> Just (Map.map Set.findMin sol)
			Nothing  -> Nothing
		where
			sacIt 
				:: Structure rname a 
				-> Structure rname b 
				-> PossibleSolutions a b 
				-> [a] 
				-> Maybe (PossibleSolutions a b)
				
			sacIt _ _ sol [] = Just sol
			sacIt s1 s2 sol (h:t) =
				if notEmpty sol'
				then
					sacIt s1 s2 sol'' t	
				else
					Nothing
				where
					sol' = runSAC s1 s2 sol
					sol'' = Map.insert h (Set.singleton (Set.findMin (sol'!h))) sol'
				
					
	detectMajority 
		:: forall rname a.(Ord rname, Ord a, Show rname, Show a)
		=> Structure rname a
		-> Maybe (Map (Tuple a) a)
		
	detectMajority str =
		findSACSolution p' s'
		where
			s = renameRelations Left str
			p = structPower s 3
			elts = Set.toList (elements s)
			
			s' :: Structure (Either rname a) a
			s' = foldl (\s e -> addRelation (Right e, 1, Set.singleton [e]) s) s elts
			
			p' :: Structure (Either rname a) (Tuple a)
			p' = foldl (\p e -> addRelation (Right e, 1, majTuples e) p) p elts
			majTuples e = 
				Set.fromList (concatMap (\e' -> [[[e, e, e']], [[e, e', e]], [[e', e, e]]]) elts)

