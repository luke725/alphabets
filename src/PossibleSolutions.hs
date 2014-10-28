-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module PossibleSolutions where
	import Prelude hiding (map)
	import qualified Data.List as List
	import Data.Set (Set)
	import qualified Data.Set as Set
	import Data.Map (Map, (!))
	import qualified Data.Map as Map
	
	newtype PossibleSolutions a b = PossibleSolutions (Map a (Set b)) deriving (Eq)
	
	toMap :: PossibleSolutions a b -> Map a (Set b)
	toMap (PossibleSolutions m) = m
	
	fromMap :: Map a (Set b) -> PossibleSolutions a b
	fromMap m = PossibleSolutions m
	
	-- every possible solution of a mapping from set a to set b
	full :: (Ord a) => Set a -> Set b -> PossibleSolutions a b
	full sa sb = 
		PossibleSolutions $ Map.fromList (List.map (\a -> (a, sb)) (Set.toList sa))

	notEmpty :: PossibleSolutions a b -> Bool
	notEmpty (PossibleSolutions m) =
		all (\set -> Set.size set > 0) (Map.elems m)

	-- is the number of possible solutions equal to one
	isUnique :: PossibleSolutions a b -> Bool
	isUnique (PossibleSolutions m) =
		all (\set -> Set.size set == 1) (Map.elems m)

	domain :: (Ord a) => PossibleSolutions a b -> a -> Set b
	domain (PossibleSolutions m) a = m!a
	
	variables :: (Ord a) => PossibleSolutions a b -> Set a
	variables (PossibleSolutions m) = Map.keysSet m

	setDomain :: (Ord a) => a -> Set b -> PossibleSolutions a b -> PossibleSolutions a b
	setDomain a sb (PossibleSolutions m) =
		PossibleSolutions (Map.insert a sb m)

	-- sets a singleton as a domain for a variable
	setValue :: (Ord a) => a -> b -> PossibleSolutions a b -> PossibleSolutions a b
	setValue a b sol = setDomain a (Set.singleton b) sol

	removeFromDomain :: (Ord a, Ord b) => a -> b -> PossibleSolutions a b -> PossibleSolutions a b
	removeFromDomain a b (PossibleSolutions m) =
		PossibleSolutions (Map.update (\s -> Just $ Set.delete b s) a m)

	-- returns any solutions; assumes that a set of solutions is nonempty
	anySolution :: PossibleSolutions a b -> Map a b
	anySolution (PossibleSolutions m) = Map.map Set.findMin m

