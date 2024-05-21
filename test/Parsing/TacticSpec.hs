{-# LANGUAGE BangPatterns #-}
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
    context "given the wauto tactic" $ do
      it "does not produce a parse error" $ do
        let file = "tactics/wauto.txt"
        contents <- TextIO.readFile file
        let tactic = parse file contents
        tactic `shouldBe` (Weaken [L2xy] Auto)
    context "given a hole tactic" $ do
      it "does not produce a parse error" $ do
        let file = "tactics/hole.txt"
        contents <- TextIO.readFile file
        let tactic = parse file contents
        tactic `shouldBe` Hole          
