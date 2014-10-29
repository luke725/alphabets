-- author : Lukasz Wolochowski (l.wolochowski@students.mimuw.edu.pl)

module AC2001 where
	import Data.Set(Set)
	import qualified Data.Set as Set
	import Data.Map(Map, (!))
	import qualified Data.Map as Map
	import Control.Monad.State
	import Prelude hiding (last)

	import PossibleSolutions (PossibleSolutions)
	import qualified PossibleSolutions as PS
	import Utils
	import RelationalStructure
	import qualified Constraint
	import Constraint (Constraint (Constraint), CSPData)

	newtype Last v d = Last (Map ((v, d), Constraint v d) (Tuple d)) deriving (Show, Eq, Ord)
	type ACState v d = State (Last v d, PossibleSolutions v d)
	
	runAC :: (Ord v, Ord d, Ord rname) 
		=> Structure rname v 
		-> Structure rname d
		-> PossibleSolutions v d 
		-> PossibleSolutions v d
		
	runAC vstr dstr sol = runAC' (Constraint.createCspData vstr dstr) sol
	
	runAC' :: (Ord v, Ord d)
	    => CSPData v d
	    -> PossibleSolutions v d
	    -> PossibleSolutions v d
	    
	runAC' cspData sol = snd $ execState (ac cspData) (emptyLast, sol)
	
	ac :: forall v d. (Ord v, Ord d) 
		=> CSPData v d
		-> ACState v d ()
		
	ac (allCs, mapCs) =
		acStep allCs
		where
			acStep :: Set (v, Constraint v d) -> ACState v d ()
			acStep q =
				if Set.size q == 0
				then return ()
				else do
					let ((v, c), q') = Set.deleteFindMin q
					delete <- revise (v, c)
					let q'' = if delete then addNeighbors (v, c) q' else q'
					acStep q''
					
			addNeighbors :: (v, Constraint v d) -> Set (v, Constraint v d) -> Set (v, Constraint v d)
			addNeighbors (v, c) q =
				foldl (\q' e -> Set.insert e q') q 
				$ filter (\(v', c') -> v /= v' && c /= c' && elem v' (Constraint.vars c'))
				$ (mapCs!v)
			
	-- returns True is an element was deleted from the domain
	revise :: forall v d. (Ord v, Ord d) => (v, Constraint v d) -> ACState v d Bool
	revise (v, c) = do
		dom <- getDomain v
		deletedL <- (mapM reviseSingle $ Set.toList dom)
		let deleted = or deletedL
		return deleted
		where
			reviseSingle :: d -> ACState v d Bool
			reviseSingle d = do
				mt <- getLast ((v,d), c)
				ok <- case mt of
					Just t -> testTuple t
					Nothing -> return False
				if ok
				then return False
				else do
					dom <- getDomain v
					setDomain v (Set.singleton d)
					doms <- getDomains c
					case Constraint.nextTupleMeetingConstraint c doms mt of
						Just t' -> do
							setLast ((v,d), c) t'
							setDomain v dom
							return False
						Nothing -> do
							setDomain v (Set.delete d dom)
							return True
							
			testTuple (Tuple ts) = do 
				doms <- getDomains c
				return $ all (\(v', d') -> Set.member v' d') (zip ts doms)
				
			getDomains (Constraint (Tuple ts, _)) = do
				mapM getDomain ts
				
	
	-- auxiliary functions that operate on state
	
	getLast :: (Ord v, Ord d) => ((v, d), Constraint v d) -> ACState v d (Maybe (Tuple d))
	getLast k = do
		(Last m, _) <- get
		return $ Map.lookup k m
		
	setLast :: (Ord v, Ord d) => ((v, d), Constraint v d) -> Tuple d -> ACState v d ()
	setLast k t = do
		(Last m, sol) <- get
		put (Last $ Map.insert k t m, sol)
		
	getDomain :: (Ord v) => v -> ACState v d (Set d)
	getDomain v = do
		(_, sol) <- get
		return (PS.domain sol v)
		
	setDomain :: (Ord v) => v -> Set d -> ACState v d ()
	setDomain v ds = do
		(last, sol) <- get
		put (last, PS.setDomain v ds sol)
	
	emptyLast :: Last v d
	emptyLast = Last Map.empty

	
