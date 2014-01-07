{-# LANGUAGE PatternGuards,ViewPatterns #-}
-- | Simplify pass over the rich language:
--
--  * Inlines local non-recursive definitions,
--  * Eliminates known-case:
--      - when the scrutinee expression is a constructor
--      - by inlining/eliminating the scrutinee variable
--  * Beta reduction
--
-- These passes destroy sharing and make the program less efficient.
-- However, they should preserve the semantics (even in presence of
-- non-terminating programs/bottoms)
--
-- TODO: Inline non-recursive global definitions
--       Polymorphic lets
module HipSpec.Lang.SimplifyRich where

import HipSpec.Lang.Rich
import HipSpec.Lang.Type

import qualified Data.Foldable as F

import HipSpec.Utils (inspect)
import Data.Maybe (mapMaybe)

-- GHC too often separates functions that are not supposed to be.
-- If we identify a function that is not recursive, and calls a function
-- no other function calls, it has probably been floated out in a silly way
-- and is let bound back in. The reason we do is is to kick in the
-- optimisation in simpFun.
--
-- More inlining can be done: non-recursive functions can always be
-- inlined. But this could be done at the simple level instead so no
-- new cases or lets or lambdas are inlined.
--
-- The new name needs to be brought in by the compiler, and not from the
-- source, otherwise QuickSpec might want to use it later. Hence the
-- eliglibility check.
simpFuns :: Eq a => (Typed a -> Bool) -> [Function (Typed a)] -> [Function (Typed a)]
simpFuns eliglible fns = case mapMaybe (uncurry try) (inspect fns) of
    ((g,f),rest):_ ->
        let (g',f') = makeLet g f
        in  simpFun g' : simpFuns eliglible (f' : rest)
    [] -> map simpFun fns
  where
    -- Is this function called from only one other function?
    try fn@(Function f _) other_fns
        | not (eliglible f) = Nothing
        | otherwise = case calls of
            [(other_fn,rest)] | not (recursive other_fn) -> Just ((fn,other_fn),rest) -- put fst int snd
            _                                            -> Nothing
      where
        calls = [ pair | pair@(Function _ b,_) <- inspect other_fns , f `F.elem` b ]

-- Put the first, g, into the second, f
makeLet :: Function (Typed a) -> Function (Typed a) -> (Function (Typed a),Function (Typed a))
makeLet gf (Function f fb) =
    ( gf -- Function g (Var f [])
    , Function f (Let [gf] fb)
    )

simpFun :: Eq a => Function (Typed a) -> Function (Typed a)
simpFun (Function f b) = Function f $ simpExpr $ case b of
    -- Sometimes functions look like this
    --    f = /\ fts -> \ xs -> let g = /\ gts -> K[g @gts] in g @ts,
    -- then, if ts only type variables and a subset of tsf and the gts are
    -- the same at every ocurence, we simply replace it to
    --    f = /\ fts -> \ xs -> K[f @fts xs]
    (collectBinders -> (xs,Let [Function g e] (Var g' ts)))
        | flip all ts $ \ t -> case t of TyVar (u ::: _) -> u `elem` fts
                                         _       -> False
        , all (check ==) checks -- all type applications of g are the same
        , and [ ty `elem` gtst | ty <- check ]  -- all type applications of g are of its type variables
        , g == g' -> makeLambda xs
                    $ tySubst g (\ _ -> Var f ftst `apply` map (`Var` []) xs)
                    $ tyVarSubsts ty_su e
      where
        ty_su = zip gts (map forget ts)
        ftst  = map (star . TyVar) fts
        fts   = fst . collectForalls . typed_type $ f
        gtst  = map (star . TyVar) gts
        gts   = fst . collectForalls . typed_type $ g
        check:checks = [ ts' | Var g'' ts' <- universeExpr e, g == g'' ]
    _ -> b

simpExpr :: Eq a => Expr (Typed a) -> Expr (Typed a)
simpExpr = transformExpr $ \ e0 -> case e0 of

    -- Beta reduction
    App (Lam x body) arg -> simpExpr ((arg // x) body)

    -- Known case on a constructor
    Case e mx alts
        | (Var u ts,args) <- collectArgs e
        , Just (ConPat _ _ bs,rhs) <- findAlt u ts alts
        -> simpExpr (substMany (maybe id (\ x -> ((x,e):)) mx (zip bs args)) rhs)

    Case (Let fns e) x alts -> simpExpr (Let fns (Case e x alts))

    Case e x alts -> Case e Nothing
                            [ (p,simpExpr (removeScrutinee e x alt))
                            | alt@(p,_) <- alts
                            ]

    -- Inlining local non-recursive functions
    -- TODO: Handle several functions, handle polymorphic functions (no examples yet)
    -- Cannot inline this to several occasions if e contains a let
    Let [Function f b] e
        | not (isForallTy (typed_type f))
        , not (f `occursIn` b)
        , letFree b || occurrences f e <= 1 -> simpExpr ((b // f) e)


    Let fns e -> Let (map simpFun fns) (simpExpr e)

    _ -> e0

-- | Removes the scrutinee variable (and also the expression if it is a variable),
--   by inlining the pattern or the expression again (if it is a Default alt)
removeScrutinee :: Eq a => Expr (Typed a) -> Maybe (Typed a) -> Alt (Typed a) -> Expr (Typed a)
removeScrutinee e mx (p,rhs) = subst rhs
  where
    subst_expr  = case p of
        Default        -> e
        LitPat l v     -> Lit l v
        ConPat u ts bs -> apply (Var u ts) (map (`Var` []) bs)

    -- If the scrutinee is just a variable, we inline it too.
    -- This can lead to triggering many known case.
    subst = substMany . (`zip` repeat subst_expr) . maybe id (:) mx $ case e of
        Var u [] -> [u]   -- The variable can only be locally bound by lambda
                          -- or case and thus is not applied to type args.
        _        -> []

