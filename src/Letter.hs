-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module Letter where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import qualified Data.Maybe as Maybe
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PermutationGroup
	
	import Utils
	
	newtype Atom = Atom Int deriving (Ord, Eq)
	
	instance Show Atom where
		show (Atom a) = show a
		
	type Partition = [[Atom]]
	
	type Automorphisms = ([Atom], [Permutation Atom])

	type Alphabet = [Automorphisms]
	
	data Letter = LSet (Set Letter) | LAtom Atom deriving (Show, Ord, Eq)
	
	newtype Element = Element (Int, Permutation Int) deriving (Show, Ord, Eq)
	
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
	
	letterAutomorphisms :: Letter -> Automorphisms
	letterAutomorphisms letter =
		(atoms, filter (isAutomorphism letter) allPermutations)
		where
			atoms = Set.toList (letterAtoms letter)
			allPermutations =
				map 
					(\perm -> PermutationGroup.fromPairs (zip atoms perm)) 
					(List.permutations atoms)
					
	letterAutomorphismGroup :: Letter -> Automorphisms
	letterAutomorphismGroup letter =
		(atoms, filter (isAutomorphism letter) allPermutations)
		where
			atoms = Set.toList (letterAtoms letter)
			allPermutations =
				map 
					(\perm -> PermutationGroup.fromPairs (zip atoms perm)) 
					(List.permutations atoms)
					
	mapAtoms :: (Atom -> Atom) -> Letter -> Letter
	mapAtoms f (LAtom a) = LAtom (f a)
	mapAtoms f (LSet set) = LSet (Set.map (mapAtoms f) set)
	
	resetAtoms :: Letter -> Letter
	resetAtoms letter = 
		mapAtoms (\a -> atomMap!a) letter
		where
			atomList = Set.toList $ letterAtoms letter
			atomMap = Map.fromList $ zip atomList (map Atom [1..List.length atomList])
			
	alphabetFromLetters :: [Letter] -> Alphabet
	alphabetFromLetters letters = 
		map letterAutomorphismGroup letters
			
			
	dimension :: Alphabet -> Int
	dimension alph =
		maximum $ map (\(atoms, _) -> List.length atoms) alph
				
			
	automorphismPreservesPartition :: Partition -> Permutation Atom -> Bool
	automorphismPreservesPartition part f =
		all (\set -> set == Set.map (\a -> a .^ f) set) partSets
		where
			partSets = map Set.fromList part	
	
	translateAutomorphism :: Partition -> Permutation Atom -> Maybe (Tuple Element)
	translateAutomorphism part f = 
		case allJust (map permute part) of
			Just t  -> Just $ Tuple $ filter (\(Element (i, _)) -> i > 1) t
			Nothing -> Nothing
		where
			permute :: [Atom] -> Maybe Element
			permute p =
				case allJust (map (\e -> List.elemIndex e pp) p) of
					Just l  -> Just (Element (List.length l, PermutationGroup.fromList l))
					Nothing -> Nothing
				where
					pp = map (\a -> a .^ f) p

					
	letterRelations :: Letter -> Map Partition (Arity, Set (Tuple Element))
	letterRelations letter =
		relationsFromAutomorphisms (letterAutomorphisms letter)
			
					
	relationsFromAutomorphisms 
		:: Automorphisms
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



