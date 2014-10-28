-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module Letter where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map ((!))
	import qualified Data.Map as Map
	import qualified Data.List as List
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PermutationGroup
	
	newtype Atom = Atom Int deriving (Ord, Eq)
	
	instance Show Atom where
		show (Atom a) = show a
		
	type Partition = [[Atom]]
	
	type AutomorphismGroup = ([Atom], [Permutation Atom])

	type Alphabet = [AutomorphismGroup]
	
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
	
	letterAutomorphisms :: Letter -> AutomorphismGroup
	letterAutomorphisms letter =
		(atoms, filter (isAutomorphism letter) allPermutations)
		where
			atoms = Set.toList (letterAtoms letter)
			allPermutations =
				map 
					(\perm -> PermutationGroup.fromPairs (zip atoms perm)) 
					(List.permutations atoms)
					
	letterAutomorphismGroup :: Letter -> AutomorphismGroup
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


