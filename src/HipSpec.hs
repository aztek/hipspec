{-# LANGUAGE RecordWildCards,NamedFieldPuns #-}
module HipSpec (hipSpec, module Test.QuickSpec, fileName) where

import Test.QuickSpec

import Test.QuickSpec.Main (prune)
import Test.QuickSpec.Term (totalGen,Term)
import Test.QuickSpec.Equation (Equation(..), equations)
import Test.QuickSpec.Generate
import Test.QuickSpec.Signature
import Test.QuickSpec.Utils.Typed
import Test.QuickSpec.TestTotality

import Test.QuickSpec.Reasoning.PartialEquationalReasoning
    (PEquation(..), {- evalPEQ, -} showPEquation)

import qualified Test.QuickSpec.Reasoning.NaiveEquationalReasoning as NER
import qualified Test.QuickSpec.Reasoning.PartialEquationalReasoning as PER

import HipSpec.Reasoning
import HipSpec.Void

import HipSpec.Trans.Obligation
import HipSpec.Trans.Property
import HipSpec.Trans.QSTerm
import HipSpec.Init
import HipSpec.Monad hiding (equations)
import HipSpec.MainLoop
import HipSpec.Heuristics.Associativity
import HipSpec.Trans.DefinitionalEquations
import HipSpec.StringMarshal (maybeLookupSym)

import Prelude hiding (read)

import Halo.Util

import Data.List
import Data.Ord

import Language.Haskell.TH

import Data.Monoid (mappend)

import Data.Aeson (encode)
import qualified Data.ByteString.Lazy as B

fileName :: ExpQ
fileName = location >>= \(Loc f _ _ _ _) -> stringE f

hipSpec :: Signature a => FilePath -> a -> IO ()
hipSpec file sig0 = runHS (signature sig0 `mappend` withTests 100) $ do

    writeMsg Started

    processFile file $ \ user_props -> do

        writeMsg FileProcessed

        Info{str_marsh,sig} <- getInfo

        Params{bottoms} <- getParams

        (eqs,univ) <- runQuickSpec

        if bottoms then do

                let qsconjs = map (peqToProp (showPEquation sig) str_marsh)
                                  (map totalise eqs)

                (ctx_init,tot_thms,tot_conjs) <- proveTotality univ

                runMainLoop
                    ctx_init
                    (qsconjs ++ map (fmap absurd) (tot_conjs ++ user_props))
                    (map (fmap absurd) tot_thms)

            else do

                let qsconjs = map (eqToProp (showEquation sig) str_marsh) eqs

                    ctx_init = NER.initial (maxDepth sig) (symbols sig) univ

                runMainLoop ctx_init (qsconjs ++ map (fmap absurd) user_props) []

        Params{json} <- getParams

        case json of
            Just json_file -> do
                msgs <- getMsgs
                liftIO $ B.writeFile json_file (encode msgs)
            Nothing -> return ()

runMainLoop :: (MakeEquation eq,EQR eq ctx cc)
            => ctx -> [Property eq] -> [Theorem eq] -> HS ()
runMainLoop ctx_init initial_props initial_thms = do

    ctx <- pruneWithDefEqs ctx_init

    (theorems,conjectures,_ctx) <- mainLoop ctx initial_props initial_thms

    let showProperties = map propName
        notQS  = filter (not . isFromQS)
        fromQS = filter isFromQS

    writeMsg $ Finished
        (showProperties $ notQS $ map thm_prop theorems)
        (showProperties $ notQS conjectures)
        (showProperties $ fromQS $ map thm_prop theorems)
        (showProperties $ fromQS conjectures)

runQuickSpec :: HS ([Equation],[Tagged Term])
runQuickSpec = do

    Info{..} <- getInfo
    let Params{..} = params

    classes <- liftIO $ fmap eraseClasses (generate (const totalGen) sig)

    let eq_order eq = (assoc_important && not (eqIsAssoc eq), eq)
        swapEq (t :=: u) = u :=: t

        classToEqs :: [[Tagged Term]] -> [Equation]
        classToEqs = sortBy (comparing (eq_order . (swap_repr ? swapEq)))
                   . if quadratic
                          then sort . map (uncurry (:=:)) .
                               concatMap (uniqueCartesian . map erase)
                          else equations

        univ      = map head classes
        ctx_init  = NER.initial (maxDepth sig) (symbols sig) univ

        reps      = map (erase . head) classes

        pruner    = prune ctx_init reps  -- this one or similar for explore theory
        prunedEqs = pruner (equations classes)
        eqs       = prepend_pruned ? (prunedEqs ++) $ classToEqs classes


    writeMsg $ QuickSpecDone (length classes) (length eqs)

    return (eqs,univ)

proveTotality :: [Tagged Term] -> HS (PER.Context,[Theorem Void],[Property Void])
proveTotality univ = do

    Info{..} <- getInfo

    tot_list <- liftIO $ testTotality sig

    let tot_props
            = [ tot_prop
              | (sym,totality) <- tot_list
              , Just (v,True) <- [maybeLookupSym str_marsh sym]
              , Just tot_prop <- [totalityProperty v totality]
              ]

    (proved_tot,unproved_tot,NoCC) <- mainLoop NoCC tot_props []

    let ctx_init = PER.initial (maxDepth sig) tot_list univ

    return (ctx_init,proved_tot,unproved_tot)

totalise :: Equation -> PEquation
totalise eq = [] :\/: eq

{-
        let qsprops = {- filter (not . definition . propQSTerms) $ -}
                       map (peqToProp (showPEquation sig) str_marsh) (map totalise eqs)
                       -}

{-
pprune :: PER.Context -> [PEquation] -> [PEquation]
pprune ctx = evalPEQ ctx . filterM (fmap not . PER.unify)
-}

-- add these definitional equalities
--        ctx0       = execPEQ ctx_init (mapM_ unify def_eqs)

--        pruner     = pprune ctx0 -- this one for explore theory

-- assert this in the initial context....
-- for peqs

{-
    let definition (t :=: u) = evalEQ ctx0 (t =?= u)

        qsprops   = filter (not . definition . propQSTerms)
                  $ map (eqToProp str_marsh) eqs
                  -}

