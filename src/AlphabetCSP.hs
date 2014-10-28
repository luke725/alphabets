-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module AlphabetCSP where
--	import Debug.Trace
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.Maybe as Maybe
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PG
--	import qualified Math.Algebra.Group.SchreierSims as SS
	
--	import System.IO.Unsafe
--	import Data.Time

	import RelationalStructure
	import Letter
	import Utils
	import SAC3

	data RName = Original (AutomorphismGroup, Partition) | Unary Element | EType ElementType deriving (Show, Ord, Eq)
	
	newtype Element = Element (Int, Permutation Int) deriving (Show, Ord, Eq)
	
	data ElementType = CorrectType Int | ErrorType deriving (Show, Ord, Eq)
	
	class Typed a where
		elemType :: a -> ElementType
		
	instance Typed (Element) where
		elemType (Element (s, _)) = (CorrectType s)
		
	instance (Typed a) => Typed (Tuple a) where
		elemType (Tuple []) = ErrorType
		elemType (Tuple [x]) = elemType x
		elemType (Tuple (x:(h:t))) =
			if elemType x == elemType (Tuple (h:t))
			then elemType x
			else ErrorType
	
	type GroupGens = [[[Atom]]]

	neutralElement :: Element -> Element
	neutralElement (Element (r, _)) = Element (r, PG.p [])
	
	isNeutral :: Element -> Bool
	isNeutral e = (e == neutralElement e)
	
	relationsFromAlphabet :: Alphabet -> [Relation RName Element]
	relationsFromAlphabet alphabet =
		concatMap relsFromAutoGroup alphabet
		where
			relsFromAutoGroup (atoms, perm) =
				map (\(as, (ar, s)) -> Relation (Original ((atoms, perm), as), ar, s))
				$ Map.toList (relationsFromAutomorphisms (atoms, perm))
				

				
	structureT :: Alphabet -> Structure RName Element
	structureT alphabet = 
		filterStructure (okType alphabet) $ addTypeRels (structureFromRels (relationsFromAlphabet alphabet))
		where
			addTypeRels :: Structure RName Element -> Structure RName Element
			addTypeRels str =
				addRelations (map (\(t, s) -> Relation (EType t, Arity 1, Set.map (\e -> Tuple [e]) s)) $ Map.toList $ typeMap str) str
				
			typeMap str =
				foldl 
					(\m e -> Map.insertWith Set.union (elemType e) (Set.singleton e) m) 
					Map.empty 
					(Set.toList $ structureElems str)
	
	structureTu :: Alphabet -> Structure RName Element
	structureTu alphabet = 
		addRelations 
			(map (\e -> Relation (Unary e, Arity 1, Set.singleton (Tuple [e]))) $ Set.toList $ structureElems t)
			t
		where
			t = structureT alphabet
			
	structureT3u :: Alphabet -> Structure RName (Tuple Element)
	structureT3u alphabet =
		addRelations (map u elems) t3
		where
			t = structureT alphabet
			elems = Set.toList $ structureElems t
			t3 = structPower t 3
			u e = 
				Relation 
					(Unary e, 
					 Arity 1, 
					 Set.fromList $ concatMap (\a -> map (\x -> Tuple [x]) [Tuple [a, e, e], Tuple [e, a, e], Tuple [e, e, a]]) elems)
		
	structureM :: Alphabet -> Structure RName (Tuple Element)
	structureM alphabet =
		filterStructure (\e -> elemType e /= ErrorType) (structureT3u alphabet)
	
	okType :: (Typed e) => Alphabet -> e -> Bool
	okType alphabet e = 
		case elemType e of
			CorrectType t -> (t < dimension alphabet - 1)
			ErrorType     -> False	
			 
	structureV :: Alphabet -> Structure RName Element
	structureV alphabet =
		filterStructure (okType alphabet) (structureTu alphabet)
		
	structureM' :: Alphabet -> Structure RName (Tuple Element)
	structureM' alphabet =
		filterStructure (okType alphabet) (structureM alphabet)
		
	structureM'' :: Alphabet -> Structure RName (Tuple Element)
	structureM'' alphabet =
		filterStructure (\(Tuple [x,_,_]) -> isNeutral x) (structureM' alphabet)
		
	structureD :: Alphabet -> Structure RName (Tuple Element)
	structureD alphabet =
		mapStructure (\(Tuple [_,y,z]) -> (Tuple [y, z])) (structureM'' alphabet)
		
	structureDo :: Alphabet -> Structure RName (Tuple Element)
	structureDo alphabet =
		filterStructure (\(Tuple [x,_]) -> isConjClassRep x) (structureD alphabet)
		
	structureDDirect :: Alphabet -> Structure RName (Tuple Element)
	structureDDirect alphabet =
			addRelations (map u elems) t2
		where
			t = filterStructure (okType alphabet) $ structureT alphabet
			elems = Set.toList $ structureElems t
			t2 = filterStructure (okType alphabet) $ structPower t 2
			u e =
				if isNeutral e
				then
					Relation 
						(Unary e, 
						 Arity 1, 
						 Set.fromList 
						 	(concatMap (\a -> [Tuple[Tuple [a, e]], Tuple[Tuple [e, a]]]) elems))
				else
					Relation (Unary e, Arity 1, Set.fromList [Tuple[Tuple [e, e]]])
					
	structureDoDirect :: Alphabet -> Structure RName (Tuple Element)
	structureDoDirect alphabet =
		filterStructure (\(Tuple [x,_]) -> isConjClassRep x) (structureDDirect alphabet)		
	
	checkMajorityAutomorphisms :: Alphabet -> Bool
	checkMajorityAutomorphisms alphabet =
		if structureSig strDo == structureSig strV
		then findSolutionFast strDo strV /= Nothing
		else error "Signature mismatch"
		where
			strDo = structureDoDirect alphabet
			strV = structureV alphabet
			
	checkMajorityLetter :: Letter -> Bool
	checkMajorityLetter letter =	
		checkMajorityAutomorphisms [letterAutomorphisms letter]
	
	isConjClassRep :: Element -> Bool
	isConjClassRep (Element (i, p)) =
		conjClassRep (Set.fromList [0..i-1]) p == p

	relationsFromAutomorphisms 
		:: AutomorphismGroup
		-> Map Partition (Arity, Set (Tuple Element))

	relationsFromAutomorphisms (atoms, perms) =
		removeDup
		$ Map.fromList
		$ map
			(\part -> 
				(part, 
				(Arity $ length $ filter (\l -> length l > 1) part,
				 Set.fromList (Maybe.mapMaybe (translateAutomorphism part) perms)))
			)
		$ Set.toList (allPermPartPreserveOrbits perms atoms)
		where
			translateAutomorphism :: Partition -> Permutation Atom -> Maybe (Tuple Element)
			translateAutomorphism part f = 
				case allJust (map permute part) of
					Just t  -> Just $ Tuple $ filter (\(Element (i, _)) -> i > 1) t
					Nothing -> Nothing
				where
					permute :: [Atom] -> Maybe Element
					permute p =
						case allJust (map (\e -> List.elemIndex e pp) p) of
							Just l  -> Just (Element (List.length l, PG.fromList l))
							Nothing -> Nothing
						where
							pp = map (\a -> a .^ f) p



