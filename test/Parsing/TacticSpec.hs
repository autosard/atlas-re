module Parsing.TacticSpec(spec) where

import Test.Hspec
import Data.Text.IO as TextIO

import Parsing.Tactic
import CostAnalysis.Tactic
import Control.Monad (void)
import Control.Exception (evaluate)

spec = do
  describe "Tactic parser" $ do
    context "given a the tactic for splay" $ do
      it "does not produce a parse error" $ do
        let file = "tactics/RandSplayTree/splay.txt"
        contents <- TextIO.readFile file
        let tactic = parse file contents
        True `shouldBe` True
