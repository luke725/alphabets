-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module GSAC where
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map, (!))
	import qualified Data.Map as Map
	import Control.Monad.State
	import Prelude hiding (last)

	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	import RelationalStructure
	import GAC2001
	import Utils

	findSolution :: forall v d rname. (Ord v, Ord d, Ord rname, Show v, Show d) 
		=> Structure rname v 
		-> Structure rname d
		-> Maybe (Map v d)
		
	findSolution vstr dstr =
		case runGsac vstr dstr (PS.full (strElems vstr) (strElems dstr)) of
			Left m -> Just m
			Right sol -> 
				if PS.notEmpty sol
				then 
					case foldM setValue sol (Set.toList $ strElems vstr) of
						Left (Just m) -> Just m
						Left Nothing  -> Nothing
						Right sol' -> Just (PS.anySolution sol')
				else Nothing
		
		where
			setValue :: PossibleSolutions v d -> v -> Either (Maybe (Map v d)) (PossibleSolutions v d)
			setValue sol v = setValue' sol v (Set.toList $ PS.domain sol v)
			
			setValue' _ _ [] = Left Nothing
			setValue' sol v (d:ds) =
				case runGsac vstr dstr (PS.setDomain v (Set.singleton d) sol) of
					Left m -> Left (Just m)
					Right sol' ->
						if PS.notEmpty sol'
						then Right sol'
						else setValue' sol v ds
				

	runGsac
		:: forall v d rname. (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> Either (Map v d) (PossibleSolutions v d)
		
	runGsac vstr dstr sol = do
		(_, sol') <- fixPointM gsacStep (emptyLast, runGac vstr dstr sol)
		return sol'
		where
			gsacStep :: (Last v d, PossibleSolutions v d) -> Either (Map v d) (Last v d, PossibleSolutions v d)
			gsacStep (last, dom) =
				case runState (buildBranch (PS.toMap dom)) (last, dom) of
					(Nothing, (last', dom')) -> Right (last', dom')
					(Just m, _)          -> Left m
				
			buildBranch :: Map v (Set d) -> GACState v d (Maybe (Map v d))
			buildBranch m =
				if Map.size m == 0
				then return Nothing
				else do
					(last, dom) <- get
					bb <- buildBranch' m (Map.keys m) (Map.empty)
					case bb of
						Left m'         -> return (Just m')
						Right (del, m') -> do
							put (last, dom)
							case del of
								Just (v, d) -> do
									dv <- getDomain v
									setDomain v (Set.delete d dv)
									gac vstr dstr
									return Nothing
								Nothing -> buildBranch m'
								
--			domSize m =
--				sum $ map (\(_, s) -> Set.size s) (Map.toList m)
	
			buildBranch' 
				:: Map v (Set d) 
				-> [v] 
				-> Map v d 
				-> GACState v d (Either (Map v d) (Maybe (v, d), Map v (Set d)))
				
			buildBranch' m [] br =
				if Map.size br == Set.size (strElems vstr) 
				then return (Left br) 
				else return (Right (Nothing, m))
				
			buildBranch' m (v:free) br =
				case Map.lookup v m of
					Nothing -> buildBranch' m free br
					Just mv ->
						if Set.size (m!v) == 0
						then buildBranch' (Map.delete v m) free br
						else do
							let d = Set.findMin mv
							let m' = 
								if Set.size mv > 1 
								then Map.insert v (Set.deleteMin (mv)) m 
								else Map.delete v m
							dv <- getDomain v
							if not (Set.member d dv) 
							then buildBranch' m' (v:free) br 
							else do
								setDomain v (Set.singleton d)
								gac vstr dstr
								(_, dom') <- get
								if PS.notEmpty dom'
								then
									buildBranch' m' free (Map.insert v d br)
								else do
									if Map.size br > 0
									then return (Right (Nothing, m))
									else return (Right (Just (v, d), m'))

