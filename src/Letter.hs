-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module Letter where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.List as List
	import qualified Data.Maybe as Maybe
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PermutationGroup

	import RelationalStructure (Arity)
	import Utils
	
	type Atom = Int
	
	data Letter = LSet (Set Letter) | LAtom Atom deriving (Show, Ord, Eq)
	
	
	setL :: [Letter] -> Letter
	setL letters = LSet (Set.fromList letters)
	
	setA :: [Atom] -> Letter
	setA ats = setL (map LAtom ats)
	
	letterAtoms :: Letter -> Set Atom
	letterAtoms (LAtom a) = Set.singleton a
	letterAtoms (LSet set) = Set.unions (map letterAtoms (Set.toList set))
	
	isAutomorphism :: Letter -> Permutation Atom -> Bool
	isAutomorphism letter f =
		applyAutomorphism f letter == letter
		where
			applyAutomorphism f' (LAtom a) = LAtom (a .^ f')
			applyAutomorphism f' (LSet set) = LSet (Set.map (applyAutomorphism f') set)
	
	letterAutomorphisms :: Letter -> [Permutation Atom]
	letterAutomorphisms letter =
		filter (isAutomorphism letter) allPermutations
		where
			ats = Set.toList (letterAtoms letter)
			allPermutations =
				map 
					(\perm -> PermutationGroup.fromPairs (zip ats perm)) 
					(List.permutations ats)
				
			
	automorphismPreservesPartition :: [[Atom]] -> Permutation Atom -> Bool
	automorphismPreservesPartition part f =
		all (\set -> set == Set.map (\a -> a .^ f) set) partSets
		where
			partSets = map Set.fromList part	
	
	translateAutomorphism :: [[Atom]] -> Permutation Atom -> Maybe (Tuple (Int, Permutation Int))
	translateAutomorphism part f = 
		case allJust (map permute part) of
			Just t  -> Just (filter (\(ar, _) -> ar > 1) t)
			Nothing -> Nothing
		where
			permute :: [Atom] -> Maybe (Int, Permutation Int)
			permute p =
				case allJust (map (\e -> List.elemIndex e pp) p) of
					Just l  -> Just (List.length l, PermutationGroup.fromList l)
					Nothing -> Nothing
				where
					pp = map (\a -> a .^ f) p

					
	letterRelations :: Letter -> Map [[Atom]] (Arity, Set (Tuple (Int, Permutation Int)))
	letterRelations letter =
		relationsFromAutomorphisms (Set.toList (letterAtoms letter)) (letterAutomorphisms letter)
					
	relationsFromAutomorphisms 
		:: [Atom] 
		-> [Permutation Atom] 
		-> Map [[Atom]] (Arity, Set (Tuple (Int, Permutation Int)))

	relationsFromAutomorphisms atoms automorphisms =
		removeDup
		$ Map.fromList
		$ map
			(\part -> 
				(part, 
				(length $ filter (\l -> length l > 1) part,
				 Set.fromList (Maybe.mapMaybe (translateAutomorphism part) automorphisms)))
			)
			partitions
		where
			partitions = Set.toList (allPermPart atoms)

