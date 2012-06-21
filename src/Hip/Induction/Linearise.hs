{-# LANGUAGE TypeOperators #-}
{-

   Linearises the parts defined in Hip.Induction.

   Used in comments in generated TPTP files, and for testing.

-}
module Hip.Induction.Linearise where

import Hip.Induction

import Text.PrettyPrint hiding (Style)

data Style c v t = Style
    { linc :: c -> Doc
    , linv :: v -> Doc
    , lint :: t -> Doc
    }

strStyle :: Style String String String
strStyle = Style
    { linc = text
    , linv = text
    , lint = text
    }

linTerm :: Style c v t -> Term c v -> Doc
linTerm st tm = case tm of
    Var v    -> linv st v
    Con c [] -> linc st c
    Con c ts -> linc st c <> parens (csv (map (linTerm st) ts))
    Fun v ts -> linv st v <> parens (csv (map (linTerm st) ts))

linTypedVar :: Style c v t -> v -> t -> Doc
linTypedVar st v t = linv st v <+> colon <+> lint st t

linForall :: Style c v t -> (Doc -> Doc) -> [v ::: t] -> Doc
linForall _  par [] = empty
linForall st _   qs = bang
                   <+> brackets (csv (map (uncurry (linTypedVar st)) qs))
                   <+> colon

linPred :: Style c v t -> [Term c v] -> Doc
linPred st xs = char 'P' <> parens (csv (map (linTerm st) xs))

linHyp :: Style c v t -> Hypothesis c v t -> Doc
linHyp st (qs,hyp) = (if null qs then id else parens)
                   $ linForall st parens qs <+> linPred st hyp

linPart :: Style c v t -> IndPart c v t -> Doc
linPart st (IndPart skolem hyps concl) = hang
     (linForall st id skolem)
     4
     $ parens $ cat $ parList (punctuate (fluff ampersand) (map (linHyp st) hyps)
                ++ [(if null hyps then id else (darrow <+>)) (linPred st concl)])

csv :: [Doc] -> Doc
csv = hcat . punctuate comma

parList :: [Doc] -> [Doc]
parList []     = [parens empty]
parList [x]    = [x]
parList (x:xs) = (lparen <> x) : init xs ++ [last xs <> rparen]

ampersand :: Doc
ampersand = char '&'

bang :: Doc
bang = char '!'

fluff :: Doc -> Doc
fluff d = space <> d <> space

darrow :: Doc
darrow = text "=>"
