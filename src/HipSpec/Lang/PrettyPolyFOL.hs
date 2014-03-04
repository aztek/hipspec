{-# LANGUAGE OverloadedStrings,PatternGuards #-}
module HipSpec.Lang.PrettyPolyFOL where

import Text.PrettyPrint

import HipSpec.Lang.PolyFOL
import HipSpec.Lang.PrettyUtils

data PP a = PP
    { ppVar  :: a -> Doc
    , ppSymb :: a -> Doc
    }

ppClause :: PP a -> Clause a -> Doc
ppClause p cls = case cls of
    SortSig x n            -> tff [ppSymb p x,"type",ppTySig (ppSymb p) p x [] (replicate n TType) TType]
    TypeSig x tvs args res -> tff [ppSymb p x,"type",ppTySig (ppSymb p) p x tvs args res]
    Clause _ cl tvs phi    -> tff ["_",ppClType cl,ppTyQuant p tvs (ppForm p phi)]
    Comment s              -> vcat (map (\ l -> "%" <+> text l) (lines s))
  where
    tff xs = "tff" <> csv xs <> "."

ppClType :: ClType -> Doc
ppClType cl = case cl of
    Axiom -> "axiom"
    Goal  -> "conjecture"

ppTySig :: (a -> Doc) -> PP a -> a -> [a] -> [Type a] -> Type a -> Doc
ppTySig pp p x tvs args res = hang (pp x <+> ":") 2 (ppTopType p tvs args res)

ppTyQuant :: PP a -> [a] -> Doc -> Doc
ppTyQuant p xs = ppQuant p "!>" (zip xs (repeat TType))

ppQuant :: PP a -> Doc -> [(a,Type a)] -> Doc -> Doc
ppQuant p q xs d = case xs of
    [] -> d
    _  -> hang (q <> bsv [ ppTySig (ppVar p) p x [] [] t | (x,t) <- xs] <> ":") 2 d
  where
    bsv = inside "[" "," "]"

ppTopType :: PP a -> [a] -> [Type a] -> Type a -> Doc
ppTopType p tvs args res = ppTyQuant p tvs (pp_args (ppType p res))
  where
    pp_args = case args of
        []  -> id
        [x] -> hang (ppType p x <+> ">") 2
        xs  -> hang (csv (map (ppType p) xs) <+> ">") 2

ppType :: PP a -> Type a -> Doc
ppType p = go
  where
    go t0 = case t0 of
        TyCon tc ts -> ppSymb p tc <> csv (map go ts)
        TyVar x     -> ppVar p x
        TType       -> "$tType"
        Integer     -> "$int"

ppForm :: PP a -> Formula a -> Doc
ppForm p f0 = case f0 of
    _ | Just (op,fs) <- collectFOp f0 -> inside "(" (ppFOp op) ")" (map (ppForm p) fs)
      | Just (q,(bs,f)) <- collectQ f0 -> ppQuant p (ppQ q) bs (ppForm p f)
    TOp top t1 t2 -> sep [ppTerm p t1 <+> ppTOp top,ppTerm p t2]
    Neg f         -> "~" <+> ppForm p f
    Pred q fs     -> ppSymb p q <> csv (map (ppForm p) fs)
    FOp{} -> error "PrettyPolyFOL.ppForm FOp"
    Q{}   -> error "PrettyPolyFOL.ppForm Q"

ppQ :: Q -> Doc
ppQ q = case q of
    Forall -> "!"
    Exists -> "?"

ppFOp :: FOp -> Doc
ppFOp op = case op of
    And     -> " & "
    Or      -> " | "
    Implies -> " => "
    Equiv   -> " <=> "

ppTOp :: TOp -> Doc
ppTOp op = case op of
    Equal   -> "="
    Unequal -> "!="

ppTerm :: PP a -> Term a -> Doc
ppTerm p = go
  where
    go tm0 = case tm0 of
        Apply f ts as -> ppSymb p f <> csv (map (ppType p) ts ++ map go as)
        Var v         -> ppVar p v
        Lit x         -> integer x

