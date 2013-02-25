{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns #-}
module HipSpec.ATP.Invoke (invokeATPs, Env(..), LinTheory(..), TheoryType(..)) where
import Prelude hiding (mapM)
import Control.Concurrent
import Control.Concurrent.STM
import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Workers
import Control.Concurrent.STM.Promise.Tree
import Control.Monad hiding (mapM)
import Data.Traversable (mapM)
import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State hiding (mapM)

import Halo.Util

import Control.Arrow ((***),first,second)

import Data.List
import Data.Maybe

import qualified Data.Map as M
import Data.Map (Map)

import HipSpec.Trans.Obligation
import HipSpec.Trans.Property
import HipSpec.ATP.Provers
import HipSpec.ATP.Results

import Halo.Util ((?))

import System.IO.Unsafe (unsafeInterleaveIO)
import System.Directory (createDirectoryIfMissing,doesFileExist)
import System.FilePath ((</>),(<.>))

import Control.Concurrent.STM.Promise
import Control.Concurrent.STM.Promise.Process

data LinTheory = LinTheory (TheoryType -> String)

data Env = Env
    { timeout         :: Double
    , lemma_lookup    :: Int -> Maybe String
    , store           :: Maybe FilePath
    , provers         :: [Prover]
    , processes       :: Int
    , z_encode        :: Bool
    }

type ProveM = ReaderT Env IO

type Result = (ProverName,ProverResult)

interpretResult :: Env  -> Prover -> ProcessResult -> ProverResult
interpretResult Env{lemma_lookup} Prover{..} pr@ProcessResult{..} = excode `seq`
    case proverProcessOutput stdout of
        s@Success{} -> case proverParseLemmas of
            Just lemma_parser -> s
                { successLemmas = Just . mapMaybe lemma_lookup . lemma_parser $ stdout }
            Nothing -> s
        Failure -> Failure
        Unknown _ -> Unknown (show pr)

filename :: Env -> Obligation (Proof a) -> (FilePath,FilePath)
filename Env{z_encode} (Obligation Property{propName} p) = case p of
    Induction coords ix _ _ ->
        ((z_encode ? escape) propName
        ,usv coords ++ "__" ++ show ix)
  where
    usv = intercalate "_" . map show

promiseProof :: Env -> Obligation (Proof LinTheory) -> Double -> Prover
             -> IO (Promise [Obligation (Proof Result)])
promiseProof env@Env{store} ob@(Obligation prop proof) timelimit prover@Prover{..} = do

    let LinTheory f = proof_content proof
        theory      = f proverTheoryType

    filepath <- case store of
        Nothing  -> return Nothing
        Just dir -> do
            let (path,file) = filename env ob
                ext = case proverTheoryType of
                        TPTP         -> "tptp"
                        SMT          -> "smt"
                        SMTUnsatCore -> "unsat-core" <.> "smt"
                d = dir </> path
                f = d </> file <.> ext
            exists <- doesFileExist f
            unless exists $ do
                createDirectoryIfMissing True d
                writeFile f theory
            return (Just f)

    when (proverCannotStdin && isNothing filepath) $
        putStrLn $
            "*** " ++ show proverName ++
            " must read its input from a file, run with --output ***"

    let filepath' | proverCannotStdin = case filepath of
                                            Just k  -> k
                                            Nothing -> error "Run with --output"
                  | otherwise = error $
                       "Prover " ++ show proverName ++
                       " should not open a file, but it did!"

        inputStr | proverCannotStdin = ""
                 | otherwise         = theory

    promise <- length inputStr `seq`
        processPromise proverCmd (proverArgs filepath' timelimit) inputStr

    let update :: ProcessResult -> [Obligation (Proof Result)]
        update r = [fmap (fmap (const $ res)) ob]
          where res = (proverName,interpretResult env prover r)

    return Promise
        { spawn = do
            -- putStrLn $ "Spawning " ++ propName p ++ ": "
            -- putStrLn inputStr
            spawn promise
        , cancel = do
            -- putStrLn $ "Cancelling " ++ propName p ++ "!"
            cancel promise
        , result = fmap update <$> result promise
        }

invokeATPs :: Tree (Obligation (Proof LinTheory)) -> Env -> IO [Obligation (Proof Result)]
invokeATPs tree env@Env{..} = do

    {- putStrLn (showTree $ fmap (propName . prop_prop) tree)

    void $ flip mapM tree $ \ (Obligation prop s) -> do
        putStrLn $ propName prop ++ ": " ++ "\n" ++ s
        putStrLn "\n"
        -}

    let make_promises :: Obligation (Proof LinTheory)
                      -> IO (Tree (Promise [Obligation (Proof Result)]))
        make_promises p = requireAny . map Leaf <$> mapM (promiseProof env p timeout) provers

    promise_tree <- join <$> mapM make_promises tree
        -- ^ mapM over trees, but we get a tree of trees, so we need to use join

    workers (Just (round $ timeout * 1000 * 1000)) processes (interleave promise_tree)

    res <- evalTree (any unknown . map (snd . proof_content . ob_content)) promise_tree

    -- print res

    return $ case res of
        Nothing    -> []
        Just props -> props

escape :: String -> String
escape = concatMap (\c -> fromMaybe [c] (M.lookup c escapes))

escapes :: Map Char String
escapes = M.fromList $ map (uncurry (flip (,)))
    [ ("za",'@')
    , ("z1",'(')
    , ("z2",')')
    , ("zB",'}')
    , ("zC",'%')
    , ("zG",'>')
    , ("zH",'#')
    , ("zL",'<')
    , ("zR",'{')
    , ("zT",'^')
    , ("zV",'\\')
    , ("z_",'\'')
    , ("zb",'!')
    , ("zc",':')
    , ("zd",'$')
    , ("zh",'-')
    , ("zi",'|')
    , ("zl",']')
    , ("zm",',')
    , ("zn",'&')
    , ("zo",'.')
    , ("zp",'+')
    , ("zq",'?')
    , ("zr",'[')
    , ("zs",'*')
    , ("zt",'~')
    , ("zv",'/')

    , ("zz",'z')

    , ("_equals_",'=')

    , ("_",' ')
    ]
