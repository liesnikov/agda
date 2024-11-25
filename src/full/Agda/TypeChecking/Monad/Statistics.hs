{-# OPTIONS_GHC -Wunused-imports #-}

-- | Collect statistics.

module Agda.TypeChecking.Monad.Statistics
    ( MonadStatistics(..)
    , tick, tickN, tickMax, getStatistics, modifyStatistics, printStatistics
    , getCacheEntryR, getCacheEntry, getCacheOpts
    , tickCM, tickC, tickCN
    , untickC
    , catchConstraintC, catchConstraintCC
    , getConstraintsCache, modifyConstraintsCache, printCacheCounter, printCacheCounterCSV
    ) where

import Data.List (sortOn)
import Data.Ord (Down(..))

import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Trans.Maybe

import qualified Data.Map as Map
import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
--import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Substitute ()

import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty
import qualified Agda.Utils.ProfileOptions as Profile
import Agda.Utils.String

class ReadTCState m => MonadStatistics m where
  modifyCounter :: String -> (Integer -> Integer) -> m ()

  default modifyCounter
    :: (MonadStatistics n, MonadTrans t, t n ~ m)
    =>  String -> (Integer -> Integer) -> m ()
  modifyCounter x = lift . modifyCounter x

  modifyCacheCounter :: ZeroVars -> CacheEntry -> (Integer -> Integer) -> m ()

  default modifyCacheCounter
    :: (MonadStatistics n, MonadTrans t, t n ~ m)
    => ZeroVars -> CacheEntry -> (Integer -> Integer) -> m ()
  modifyCacheCounter z x = lift . modifyCacheCounter z x

instance MonadStatistics m => MonadStatistics (ExceptT e m)
instance MonadStatistics m => MonadStatistics (MaybeT m)
instance MonadStatistics m => MonadStatistics (ReaderT r m)
instance MonadStatistics m => MonadStatistics (StateT  s m)
instance (MonadStatistics m, Monoid w) => MonadStatistics (WriterT w m)

instance MonadStatistics TCM where
  modifyCounter x f = modifyStatistics $ force . update
    where
      -- We need to be strict in the map.
      -- Andreas, 2014-03-22:  Could we take Data.Map.Strict instead of this hack?
      -- Or force the map by looking up the very element we inserted?
      -- force m = Map.lookup x m `seq` m
      -- Or use insertLookupWithKey?
      -- update m = old `seq` m' where
      --   (old, m') = Map.insertLookupWithKey (\ _ new old -> f old) x dummy m
      -- Ulf, 2018-04-10: Neither of these approaches are strict enough in the
      -- map (nor are they less hacky). It's not enough to be strict in the
      -- values stored in the map, we also need to be strict in the *structure*
      -- of the map. A less hacky solution is to deepseq the map.
      force m = rnf m `seq` m
      update  = Map.insertWith (\ new old -> f old) x dummy
      dummy   = f 0

  modifyCacheCounter z (mctx, cnstr) f = do
    ncnstr <- if z then (all2zero cnstr) else return cnstr
    modifyConstraintsCache $ force . (update (mctx, ncnstr))
   where
      force m = rnf m `seq` m
      update x = Map.insertWith (\ new old -> f old) x dummy
      dummy   = f 0

-- | Get the statistics.
getStatistics :: ReadTCState m => m Statistics
getStatistics = useR stStatistics

-- | Modify the statistics via given function.
modifyStatistics :: (Statistics -> Statistics) -> TCM ()
modifyStatistics f = stStatistics `modifyTCLens` f

-- | Increase specified counter by @1@.
tick :: MonadStatistics m => String -> m ()
tick x = tickN x 1

-- | Increase specified counter by @n@.
tickN :: MonadStatistics m => String -> Integer -> m ()
tickN s n = modifyCounter s (n +)

-- | Set the specified counter to the maximum of its current value and @n@.
tickMax :: MonadStatistics m => String -> Integer -> m ()
tickMax s n = modifyCounter s (max n)

-- | Print the given statistics.
printStatistics
  :: (MonadDebug m, MonadTCEnv m, HasOptions m)
  => Maybe TopLevelModuleName -> Statistics -> m ()
printStatistics mmname stats = do
  unlessNull (Map.toList stats) $ \ stats -> do
    let -- First column (left aligned) is accounts.
        col1 = Boxes.vcat Boxes.left  $ map (Boxes.text . fst) stats
        -- Second column (right aligned) is numbers.
        col2 = Boxes.vcat Boxes.right $ map (Boxes.text . showThousandSep . snd) stats
        table = Boxes.hsep 1 Boxes.left [col1, col2]
    alwaysReportSLn "" 1 $ caseMaybe mmname "Accumulated statistics" $ \ mname ->
      "Statistics for " ++ prettyShow mname
    alwaysReportSLn "" 1 $ Boxes.render table

getConstraintsCache :: ReadTCState m => m ConstraintsCache
getConstraintsCache = useR stConstraintsCache

modifyConstraintsCache :: (ConstraintsCache -> ConstraintsCache) -> TCM ()
modifyConstraintsCache f = stConstraintsCache `modifyTCLens` f

getCacheEntryR :: (MonadTCEnv m, MonadDebug m) => Constraint -> m CacheEntry
getCacheEntryR = getCacheEntry . RegularConstraint

getCacheEntry :: (MonadTCEnv m, MonadDebug m) => CacheConstraint -> m CacheEntry
getCacheEntry c = do
  (_,k) <- getCacheOpts
  env <- askTC
  let mctx = boolToMaybe k (envContext env)
  return (mctx, c)

tickCM :: (MonadStatistics m, MonadTCEnv m, MonadDebug m) => Constraint -> m ()
tickCM c = do
  co <- getCacheOpts
  tickCMO co c

tickCMO :: (MonadStatistics m, MonadTCEnv m) => CacheOpts -> Constraint -> m ()
tickCMO (z, k) c = do
  env <- askTC
  let mctx = boolToMaybe k (envContext env)
  tickCO z (mctx, RegularConstraint c)

tickC :: (MonadStatistics m, MonadDebug m) => CacheEntry -> m ()
tickC c = do
  (z,_) <- getCacheOpts
  tickCO z c

tickCO :: MonadStatistics m => ZeroVars -> CacheEntry -> m ()
tickCO z c = tickCN z c 1

tickCN :: MonadStatistics m => ZeroVars -> CacheEntry -> Integer -> m ()
tickCN z c n = modifyCacheCounter z c (n +)

untickCM :: (MonadStatistics m, MonadTCEnv m, MonadDebug m) => Constraint -> m ()
untickCM c = do
  co <- getCacheOpts
  untickCMO co c

untickCMO :: (MonadStatistics m, MonadTCEnv m) => CacheOpts -> Constraint -> m ()
untickCMO (z, k) c = do
  env <- askTC
  let mctx = boolToMaybe k (envContext env)
  untickCN z (mctx, RegularConstraint c) 1

untickCO :: MonadStatistics m => ZeroVars -> CacheEntry -> m ()
untickCO z c = untickCN z c 1

untickC :: (MonadStatistics m, MonadDebug m) => CacheEntry -> m ()
untickC c = do
  (z,_) <- getCacheOpts
  untickCO z c

untickCN :: MonadStatistics m => ZeroVars -> CacheEntry -> Integer -> m ()
untickCN z c n = modifyCacheCounter z c (-n +)

catchConstraintC :: (MonadStatistics m, MonadConstraint m)
  => Constraint -> m () -> m ()
catchConstraintC c m = do
  whenProfile Profile.Caching (tickCM c)
  catchPatternErr (\ unblock -> do
                      whenProfile Profile.Caching (untickCM c)
                      addConstraint unblock c)
                  m

catchConstraintCC :: (MonadStatistics m, MonadConstraint m)
  => Constraint -> Constraint -> m () -> m ()
catchConstraintCC ce c m = do
  whenProfile Profile.Caching (tickCM ce)
  catchPatternErr (\ unblock -> do
                      whenProfile Profile.Caching (untickCM ce)
                      addConstraint unblock c)
                  m

printCacheCounter :: (MonadDebug m, MonadTCEnv m, HasOptions m)
  => (CacheEntry -> m Doc) -> Integer -> Maybe TopLevelModuleName -> ConstraintsCache -> m ()
printCacheCounter prettyp n mmname stats = do
  unlessNull (Map.toList stats) $ \ stats -> do
    let stats' = sortOn (Down . snd) . filter ((> n) . snd) $ stats
    showcol1 <- traverse (prettyp . fst) stats'
    let -- First column (left aligned) is accounts.
        col1 = Boxes.vcat Boxes.left  $ map (Boxes.text . prettyShow) $ showcol1
        -- Second column (right aligned) is numbers.
        col2 = Boxes.vcat Boxes.right $ map (Boxes.text . showThousandSep . snd) stats'
        table = Boxes.hsep 1 Boxes.left [col1, col2]
    alwaysReportSLn "" 1 $ caseMaybe mmname "Accumulated cache statistics" $ \ mname ->
      "Cache statistics for " ++ prettyShow mname
    alwaysReportSLn "" 1 $ Boxes.render table


--print as a CSV file
printCacheCounterCSV ::
  forall m. (MonadDebug m, MonadTCEnv m, HasOptions m) =>
  (CacheEntry -> m Doc) -> Integer -> Maybe TopLevelModuleName -> ConstraintsCache -> m ()
printCacheCounterCSV prettyp n mmname stats = do
  unlessNull (Map.toList stats) $ \ stats -> do
    let stats' = sortOn (Down . snd) . filter ((> n) . snd) $ stats
    showcol1 <- traverse (uncurry cachePrinter) stats'
    alwaysReportSLn "" 1 $ caseMaybe mmname "Accumulated csv statistics" $ \ mname ->
      "Statistics for " ++ prettyShow mname
    reportSLn "" 1 ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>"
    alwaysReportSLn "" 1 $ renderStyle (Style LeftMode 100 0.1) $ vsep showcol1
    reportSLn "" 1 "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<"
  where
    cachePrinter :: CacheEntry -> Integer -> m Doc
    cachePrinter (mctx, cnstr) i = do
      let tagR c = case c of
            ValueCmp _ _ _ _ -> "ValueCmp"
            ValueCmpOnFace _ _ _ _ _ -> "ValueCmpOnFace"
            ElimCmp _ _ _ _ _ _ -> "ElimCmp"
            SortCmp _ _ _ -> "SortCmp"
            LevelCmp _ _ _ -> "LevelCmp"
            HasBiggerSort _ -> "HasBiggerSort"
            HasPTSRule _ _ -> "HasPTSRule"
            CheckDataSort _ _ -> "CheckDataSort"
            CheckMetaInst _ -> "CheckMetaInst"
            CheckType _ -> "CheckType"
            UnBlock _ -> "UnBlock"
            IsEmpty _ _ -> "IsEmpty"
            CheckSizeLtSat _ -> "CheckSizeLtSat"
            FindInstance _ _ -> "FindInstance"
            ResolveInstanceHead _ -> "ResolveInstanceHead"
            CheckFunDef _ _ _ _ -> "CheckFunDef"
            UnquoteTactic _ _ _ -> "UnquoteTactic"
            CheckLockedVars _ _ _ _ -> "CheckLockedVars"
            UsableAtModality _ _ _ _ -> "UsableAtModality"
          tag = case cnstr of
            RegularConstraint c -> tagR c
            InstanceConstraint t -> "InstanceSearch"
          pcnstr = pretty cnstr
          pctx = maybe "No context" pretty mctx
          name = maybe [] (return . pretty) mmname
      return . hsep $ punctuate (text ",") $ name ++ [ tag, pretty i, doubleQuotes pcnstr, doubleQuotes pctx]


-- utils

-- | substitute all variables that are currently in the context to zero
all2zero :: (Subst a, MonadTCEnv m) => a -> m a
all2zero t = do
  n <- getContextSize
  let s = parallelS . replicate n $ deBruijnVar 0
  return $ applySubst s t

type ZeroVars = Bool
type KeepContext = Bool
type CacheOpts = (ZeroVars, KeepContext)

getCacheOpts :: (MonadDebug m) => m CacheOpts
getCacheOpts = do
  z <- hasProfileOption Profile.CacheZeroVar
  k <- hasProfileOption Profile.CacheNoContx
  return (z, not k)
