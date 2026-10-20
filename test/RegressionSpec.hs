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
    it "reports overlapping measures without a most specific one" $
      analyze "Measure.Ambiguous" `shouldThrow` errorContaining "Ambiguous measures"
