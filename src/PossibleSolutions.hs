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
	
	full :: (Ord a) => Set a -> Set b -> PossibleSolutions a b
	full sa sb = 
		PossibleSolutions $ Map.fromList (List.map (\a -> (a, sb)) (Set.toList sa))

	notEmpty :: PossibleSolutions a b -> Bool
	notEmpty (PossibleSolutions m) =
		all (\set -> not (Set.null set)) (Map.elems m)

	isUnique :: PossibleSolutions a b -> Bool
	isUnique (PossibleSolutions m) =
		all (\set -> Set.size set == 1) (Map.elems m)

	domain :: (Ord a) => PossibleSolutions a b -> a -> Set b
	domain (PossibleSolutions m) a = m!a

	setDomain :: (Ord a) => a -> Set b -> PossibleSolutions a b -> PossibleSolutions a b
	setDomain a sb (PossibleSolutions m) =
		PossibleSolutions (Map.insert a sb m)

	setValue :: (Ord a) => a -> b -> PossibleSolutions a b -> PossibleSolutions a b
	setValue a b sol = setDomain a (Set.singleton b) sol

	removeFromDomain :: (Ord a, Ord b) => a -> b -> PossibleSolutions a b -> PossibleSolutions a b
	removeFromDomain a b (PossibleSolutions m) =
		PossibleSolutions (Map.update (\s -> Just $ Set.delete b s) a m)

	map :: (a -> Set b -> Set b) -> PossibleSolutions a b -> PossibleSolutions a b
	map f (PossibleSolutions m) = PossibleSolutions (Map.mapWithKey f m)

	anySolution :: PossibleSolutions a b -> Map a b
	anySolution (PossibleSolutions m) = Map.map Set.findMin m

	

