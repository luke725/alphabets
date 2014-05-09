-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

{-# LANGUAGE ScopedTypeVariables #-}

module AlphabetCSP where
	import Data.Set (Set)
	import qualified Data.Set as Set
	import qualified Data.List as List
	import Data.Map (Map)
	import qualified Data.Map as Map
	import qualified Data.Maybe as Maybe
	import qualified Control.Monad as Monad
	import Math.Algebra.Group.PermutationGroup(Permutation, (.^))
	import qualified Math.Algebra.Group.PermutationGroup as PG

	import RelationalStructure
	import Letter
	import ArcConsistency
	
	type Element = (Int, Permutation Int)

	type RName = Either [[Atom]] Element

	type AStructure a = Structure RName a

	one :: Int -> Element
	one r = (r, PG.p [])
	

	buildCSP :: Letter -> (AStructure (Tuple Element), AStructure Element)
	buildCSP letter =
		(tstr, str)
		where
			rels' :: [Relation RName Element]
			rels' = 
				map 
					(\(as, s) -> (Left as, List.length as, s)) 
					(Map.toList (letterRelations letter))
				
			elts :: Set Element
			elts = elementsFromRels rels'
			
			rels :: [Relation RName Element]
			rels = rels' ++ map (\e -> (Right e, 1, Set.singleton [e])) (Set.toList elts)
			
			sig :: Signature RName
			sig = sigFromRels rels
			
			str :: Structure RName Element
			str = createStructure sig elts rels
			
			tstr :: Structure RName (Tuple Element)
			tstr =
				resetElements 
				$ foldl 
					(\tstr e@(r, _) -> 
						addToRelation 
							(Right e) 1
							[[[e, e]]]
						$ addToRelation
							(Right (one r)) 1
							[[[e, one r]], [[one r, e]]] 
							tstr
					) 
					(structPower str 2) 
					(Set.toList elts)

