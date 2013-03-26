{-# LANGUAGE NamedFieldPuns,ScopedTypeVariables #-}
-- Calls a function does
-- Looks at the core unfolding, or in an extra-supplied map
module HipSpec.Heuristics.Calls
    ( module VarSet
    , exprCalls
    , calls
    , transCalls
    , transFrom
    ) where

import Halo.Shared

import CoreSyn
import Id
import Var
import VarSet
import CoreFVs

import Debug.Trace

import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad

-- | The vars this expression calls
exprCalls :: CoreExpr -> VarSet
exprCalls = exprSomeFreeVars $
    \ v -> (isLocalId v || isGlobalId v) && not (isDataConId v)

-- | The unfolding of an Id
unfolding :: Id -> Maybe CoreExpr
unfolding v = case realIdUnfolding v of
    CoreUnfolding{uf_tmpl} -> Just uf_tmpl
    _ -> Nothing

-- | The functions this functions calls (not transitively)
calls :: Map Id CoreExpr -> Id -> VarSet
calls m v = case unfolding v `mplus` M.lookup v m of
    Just e ->
         trace ("Found unfolding for " ++ showOutputable v) (exprCalls e)
    _ -> trace ("No unfolding for " ++ showOutputable v) emptyVarSet

-- | The functions this function calls transitively
transCalls :: Map Id CoreExpr -> Id -> VarSet
transCalls m = transFrom m . unitVarSet

-- | The transitive closure of calls from this set
transFrom :: Map Id CoreExpr -> VarSet -> VarSet
transFrom m = go emptyVarSet
  where
    go visited queue
        | isEmptyVarSet to_visit = visited
        | otherwise = go (visited `unionVarSet` to_visit)
                         (foldVarSet (\ i vs -> calls m i `unionVarSet` vs)
                                     emptyVarSet
                                     to_visit)
      where to_visit = queue `minusVarSet` visited
