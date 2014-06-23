-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module ArcConsistency where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import RelationalStructure
	import Debug.Trace
	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	import Utils

	fullPossibleSolutions 
		:: Ord a 
		=> Structure rname a 
		-> Structure rname b 
		-> PossibleSolutions a b

	fullPossibleSolutions (_, elts1, _) (_, elts2, _) =
		PS.full elts1 elts2
		
		
	checkArcConsistency 
		:: (Ord rname, Ord a, Ord b, Show rname, Show a, Show b) 
		=> Structure rname a 
		-> Structure rname b 
		-> Bool
		
	checkArcConsistency s1 s2 =
		PS.notEmpty (runArcConsistency s1 s2 (fullPossibleSolutions s1 s2))
		
		
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
		
	stepAC (sig, _, rels1) (_, _, rels2) sol =
		foldl 
			(\sol' (tuple1, rel2) -> stepTuple tuple1 rel2 sol')
			sol
			(concatMap 
				(\rname -> (map (\t -> (t, rels2!rname)) (relationTuples rels1 rname))) 
				(relationNames sig))
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
				foldl (\sol (a, sb) -> PS.setDomain a sb sol) sol (Map.toList newPosSol)
				where
					(_, _, tuples2) = rel2
		
					zipTuples :: [Tuple (a, b)]
					zipTuples = map (\t2 -> zip t1 t2) (Set.toList tuples2)
			
					possiblePartSol :: [Tuple (a, b)]
					possiblePartSol = 
						filter
							(all (\(a, b) -> Set.member b (PS.domain sol a))) 
							zipTuples
			
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
		PS.notEmpty (runSAC s1 s2 (fullPossibleSolutions s1 s2))
		
		
	runSAC 
		:: (Ord rname, Ord a, Ord b, Show rname, Show a, Show b) 
		=> Structure rname a 
		-> Structure rname b 
		-> PossibleSolutions a b 
		-> PossibleSolutions a b
		
	runSAC s1 s2 sol =
		if sol'' == sol
		then sol
		else runSAC s1 s2 sol''
		where
			sol' = runArcConsistency s1 s2 sol
			sol'' = 
				PS.map 
					(\a sa ->
						if Set.size sa <= 1
						then sa
						else
							Set.filter (\b -> 
								PS.notEmpty (runArcConsistency s1 s2 (PS.setValue a b sol)))
								sa
					) 
					sol'
		
				
	findSACSolution
			:: forall rname a b.(Ord rname, Ord a, Ord b, Show rname, Show a, Show b)
			=> Structure rname a 
			-> Structure rname b 	
			-> Maybe (Map a b)
			
	findSACSolution s1 s2 =
		if PS.notEmpty initSol
		then
			case foldl 
					(\msol a -> msol >>= (\sol -> setSolOnElem sol a)) 
					(Just initSol) 
					(Set.toList (elements s1')) 
			of
				Just sol -> Just (PS.anySolution sol)
				Nothing  -> Nothing
		else
			Nothing
		where
			
			sig = signature s1
			sigUnary = Map.filter (\ar -> ar == 1) sig
			sig' = Map.filter (\ar -> ar > 1) sig
			
			s1' = filterRelations sig' s1
			s2' = filterRelations sig' s2
			
			initSol = 
				runSAC s1' s2' 
					(runArcConsistency 
						(filterRelations sigUnary s1) 
						(filterRelations sigUnary s2)
						(fullPossibleSolutions s1 s2))
			
			setSolOnElem :: PossibleSolutions a b -> a -> Maybe (PossibleSolutions a b)
			setSolOnElem sol h =
						if Set.size (PS.domain sol h) == 1
						then Just sol
						else
							List.find (const True)
							$ filter PS.notEmpty
							$ map (\ha -> runSAC s1' s2' (PS.setValue h ha sol))
							$ Set.toList (PS.domain sol h)
				
					
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
			s' = foldl (\s'' e -> addRelation (Right e, 1, Set.singleton [e]) s'') s elts
			
			p' :: Structure (Either rname a) (Tuple a)
			p' = foldl (\p'' e -> addRelation (Right e, 1, majTuples e) p'') p elts
			majTuples e = 
				Set.fromList (concatMap (\e' -> [[[e, e, e']], [[e, e', e]], [[e', e, e]]]) elts)

