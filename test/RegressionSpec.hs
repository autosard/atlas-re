{-# LANGUAGE OverloadedStrings #-}

-- | Regression tests that run the analysis on the modules in test/regression
-- in check mode, i.e. against the annotated signatures.
module RegressionSpec (spec) where

import Test.Hspec
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.List (isInfixOf)
import System.Directory (getTemporaryDirectory, createDirectoryIfMissing)
import System.FilePath ((</>))
import System.IO.Error (isUserError, ioeGetErrorString)
import System.Exit (ExitCode(..))

import Loading (loadProgram)
import Syntax.Program (Program(..), ProgramConfig(..))
import CostAnalysis.Analysis (analyzeProgram, AnalysisResult(..))
import CostAnalysis.ProveMonad (ProofEnv(..), AnalysisMode(..))

data Outcome = Proved | Rejected
  deriving (Eq, Show)

analyze :: Text -> IO Outcome
analyze modName = do
  prog <- loadProgram (Just "test/regression") modName Nothing
  tmp <- getTemporaryDirectory
  let out = tmp </> "atlas-re-tests" </> T.unpack modName
  createDirectoryIfMissing True out
  let env = ProofEnv
        { _tactics = M.empty
        , _analysisMode = Check
        , _incremental = False
        , _costModes = analysisModes (_pConfig prog)
        , _inferPotential = False
        , _outputDir = out
        , _axioms = _pAxioms prog
        }
  result <- analyzeProgram env prog
  return $ either (const Rejected) (const Proved) (_arResult result)

errorContaining :: String -> IOError -> Bool
errorContaining msg e = isUserError e && msg `isInfixOf` ioeGetErrorString e

spec :: Spec
spec = do
  describe "result binders" $ do
    it "do not capture pattern variables of the same name" $
      analyze "Pairing.CaptureUnsound" `shouldReturn` Rejected
    it "still allow the sound bound" $
      analyze "Pairing.CaptureSound" `shouldReturn` Proved

  describe "measure lookup" $ do
    it "uses the most specific matching measure" $
      analyze "Measure.Specific" `shouldReturn` Proved
    it "takes a missing measure from the most specific more general type" $
      analyze "Measure.Inherit" `shouldReturn` Proved
    it "reports overlapping measures without a most specific one" $
      analyze "Measure.Ambiguous" `shouldThrow` errorContaining "Ambiguous measures"

  describe "conditionals" $ do
    it "account for the cost of a call in the condition" $
      analyze "Ite.CondCallUnsound" `shouldReturn` Rejected
    it "still allow the sound bound for a call in the condition" $
      analyze "Ite.CondCallSound" `shouldReturn` Proved
    it "account for the cost of a let-bound condition" $
      analyze "Ite.LetBoundCallUnsound" `shouldReturn` Rejected
    it "account for the cost of a call in a condition in the body of a let" $
      analyze "Ite.LetBodyCondCallUnsound" `shouldReturn` Rejected

  describe "built-in functions" $ do
    it "comparisons cost nothing outside of conditions" $
      analyze "Builtin.Ops" `shouldReturn` Proved
    -- type errors are reported by loadProgram, which exits
    it "arithmetic is not allowed in programs" $
      analyze "Builtin.ArithmeticInProgram" `shouldThrow` (== ExitFailure 1)
