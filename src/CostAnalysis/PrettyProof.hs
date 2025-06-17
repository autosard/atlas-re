{-# LANGUAGE QuasiQuotes #-}
module CostAnalysis.PrettyProof where

import Data.Text.Lazy(Text)
import Data.Set(Set)
import Text.Blaze.Html.Renderer.Text(renderHtml)
import Text.Blaze.Html(Html, toHtml)
import Text.Hamlet (shamlet)
import Text.Lucius 
import qualified Data.Tree as T
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Text as Text
import Text.Julius
import Data.Char(toLower)
import Data.List(intersperse)
import Data.Ratio


import Primitive(Id)
import Typing.Type(Type)
import Ast
    ( printExprHead, FunDef(FunDef), TypedFunAnn(tfFqn), printFqn, ExprSrc(..), peSrc, getAnn, printPos )
import CostAnalysis.Constraint
import CostAnalysis.ProveMonad
import CostAnalysis.Rules
    ( Rule, RuleApp(ExprRuleApp, FunRuleApp) )
import CostAnalysis.Template(FreeTemplate(..))
import CostAnalysis.Annotation(FreeAnn)
import qualified CostAnalysis.Predicate as P
import CostAnalysis.Coeff

css = renderCss ([lucius|

p.tree,
ul.tree,
ul.tree ul {
  list-style: none;
  margin: 0;
  padding: 0;
}

ul.tree ul {
  margin-left: 1.0em;
}

ul.tree li {
  position: relative;
  
  margin-left: 0;
  padding-left: 1em;
  margin-top: 0;
  margin-bottom: 0;
  
  border-left: thin solid #000;
}

ul.tree li:before {
    position: absolute;
    top: 0;
    left: 0;

    width: 0.9em;
    height: 0.7em;
    margin-right: 0.1em;
    vertical-align: top;
    border-bottom: thin solid #000;
    content: "";
    display: inline-block;
}

ul.tree li:last-child {
    border-left: none;
}

ul.tree li:last-child:before {
    border-left: thin solid #000;
}


.toggle {
  padding: 10px;
  padding-left: 0;
  cursor: pointer;
}

.toggle::before {
  display: inline-block;
  width: 15px;
  content: "+";
}

.toggle.show::before {
  content: "-";
}

.collapse ul {
  display: none;
}

.toggle.show ~ ul {
  display: block;
}

.fn:has(.unsat) > .toggle {
  color: #{colorRed}
}

.app:has(.unsat) > .toggle {
  color: #{colorRed}
}

.unsat {
  color: #{colorRed};
}

.constraints.hideSat .sat {
  display: none;
}

.constraints {
  margin-left: 3em;
  display: grid;
  justify-content: start;
}

.constraintsBlock {
  display: none
}


.constraints::before {
  display: block;
  content: "+constraints";
}

.constraints:has(.unsat)::before {
  color: #{colorRed}
}

.constraints.show::before {
  content: "-";
}

.constraints.show .constraintsBlock {
  display: block;
}

|] undefined)

js = renderJavascript ([julius|
window.addEventListener("load", () => {
  for (let ul of document.querySelectorAll(".collapse ul")) {
    let tog = document.createElement("span");
    tog.appendChild(ul.parentElement.querySelector(".listHead"));
    tog.className = "toggle";
    tog.onclick = () => tog.classList.toggle("show");
    ul.parentElement.insertBefore(tog, ul.parentElement.firstChild);
  };
  for (let cs of document.querySelectorAll(".constraints")) {
    cs.onclick = () => cs.classList.toggle("show");
  };
  let onlyUnsatCheck = document.querySelector("#onlyUnsat");
  onlyUnsat.onclick = (function () {
    for (let cs of document.querySelectorAll(".constraints")) {
       cs.classList.toggle("hideSat");
    }; 
  });
});
|] undefined)

renderProof :: Maybe (Set Constraint) -> Derivation -> [Constraint] -> Text
renderProof unsat deriv sigCs = renderHtml [shamlet|
$doctype 5
<html>
    <link rel="stylesheet" href="style.css">
    <script src="proof.js">
    <head>
        <title>Atlas
    <body>
        <h2>Result
        $maybe core <- unsat
           <p class="unsat">unsat
        $nothing
           <p> sat
        <h2>Signature Constraints
        ^{hamCsList sigCs (inCore unsat)}
        <h2>Derivation
        <div class="deriv-flags">
            <input type=checkbox id="onlyUnsat">show only unsat constraints
        <br>
        ^{hamDeriv unsat deriv}
|]
          
inCore unsat c = case unsat of
                   Just core -> S.member c core
                   Nothing -> False
          
hamDeriv :: Maybe (Set Constraint) -> Derivation -> Html
hamDeriv unsat (T.Node mod fns) = [shamlet|
<p class="tree">mod
<ul class="collapse tree">
    $forall fn <- fns
        <li class="fn">^{hamDeriv' unsat fn}
|]

hamDeriv' :: Maybe (Set Constraint) -> Derivation -> Html
hamDeriv' unsat (T.Node appl []) = [shamlet|#{hamRuleApp unsat appl}|]  
hamDeriv' unsat (T.Node appl children) = [shamlet|
#{hamRuleApp unsat appl}
<ul class="tree">
    $forall child <- children
        <li .app>^{hamDeriv' unsat child}
|]
  

hamRuleApp :: Maybe (Set Constraint) -> RuleApp -> Html
hamRuleApp unsat (FunRuleApp (FunDef ann id args body)) = [shamlet|
<span class="listHead">#{printFqn (tfFqn ann)}|]
hamRuleApp unsat (ExprRuleApp rule cf (q, qe, preds) q' cs e) = [shamlet|
<span .listHead :((not . null) cs'):.unsat>
  <math display="inline">
    <mrow>
      <mo form="prefix" stretchy="false">(
      <mtext>#{printRule cf rule}
      <mo form="postfix" stretchy="false">)
      <mspace width="1em">
      ^{hamAnn qe}
      <mtext>, 
      ^{hamAnn q}
      <mo form="prefix" stretchy="false">[
      ^{hamPredicates preds}
      <mo form="postfix" stretchy="false">]
      <mo>⊢
      <mtext>
          <code>#{printExprHead e}
          (#{printPos srcPos})  
      <mo lspace="0.22em" rspace="0.22em" stretchy="false">|
      ^{hamAnn q'}
      ^{hamCsList cs (inCore unsat)}
|]
  where srcPos = case peSrc $ getAnn e of
          Loc pos -> pos
          DerivedFrom pos -> pos
        cs' = case unsat of
          Just core -> S.toList $ S.intersection (S.fromList cs) core
          Nothing -> []

printRule :: Bool -> Rule -> String
printRule cf rule = map toLower (show rule)
  ++ if cf then ", cf" else ""

hamCsList :: [Constraint] -> (Constraint -> Bool) -> Html
hamCsList cs inCore = [shamlet|
<div class="constraints">
    <math class="constraintsBlock" display="block">
        <mtable columnalign="left">
            $forall c <- cs
                <mtr>
                    $with unsat <- inCore c
                      <mrow :(unsat):class="unsat" :(not unsat):class="sat">
                          ^{hamConstraint c}
|]

hamPredOp :: P.PredOp -> Html
hamPredOp P.Le = [shamlet|<mo>≤|]
hamPredOp P.Lt = [shamlet|<mo><|]
hamPredOp P.Eq = [shamlet|<mo>=|]
hamPredOp P.Neq = [shamlet|<mo>≠|]

hamPredicates :: Set P.Predicate -> Html
hamPredicates preds = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map hamPredicate (S.toAscList preds))
  
hamPredicate :: P.Predicate -> Html
hamPredicate (P.Predicate m op x y) =
  [shamlet|
<apply>
  <apply>
    #{m}
    <ci>#{x}
  ^{hamPredOp op}
  <apply>
    #{m}
    <ci>#{y}|]
  
hamAnn :: FreeAnn -> Html
hamAnn ctx = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map hamTemplType (M.toAscList ctx))
  

hamTemplType :: (Type, FreeTemplate) -> Html
hamTemplType (t, q) = [shamlet|
^{hamArgs (_ftArgs q)}
<mo>:
<mtext> #{show t}
<mo>|
^{hamTempl q}|]

hamArgs :: [Id] -> Html
hamArgs [] = [shamlet|<mi>∅|]
hamArgs args = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map hamArg args)
  where hamArg arg = [shamlet|<mi>#{Text.unpack arg}|]
        
  
hamTempl :: FreeTemplate -> Html
hamTempl q = [shamlet|
<msubsup>
    <mi>q
    <mn>#{_ftId q}
    <mtext>#{_ftLabel q}
|]

hamCoeffIdx (Pure x) = [shamlet|
<mo form="prefix" stretchy="false">(
<mi>#{x}
<mo form="postfix" stretchy="false">)
|]
hamCoeffIdx (Mixed factors) = [shamlet|
<mo form="prefix" stretchy="false">(
^{hamFactors factors}
<mo form="postfix" stretchy="false">)
|]
        
hamFactors :: Set Factor -> Html
hamFactors factors = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map hamFactor (S.toList factors))

hamFactor :: Factor -> Html
hamFactor (Const c)= [shamlet|
<mn>#{c}
|]
hamFactor (Arg x [a])= [shamlet|
<msup>
   <mi>#{x}
   <mn>#{a}
|]  
hamFactor (Arg x a) = [shamlet|
<msup>
   <mi>#{x}
   <mrow>
     <mo form="prefix" stretchy="false">(
     ^{hamListInt a}
     <mo form="postfix" stretchy="false">)
|]  

hamListInt :: [Int] -> Html
hamListInt xs = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map (\x -> [shamlet|<mn>#{x}|]) xs)
  
hamCoeff :: Coeff -> Html
hamCoeff (Coeff id label comment idx) = [shamlet|
<msubsup>
   <mi>q
   <mn>#{id}
   <mtext>#{label}
^{hamCoeffIdx idx}
|]
  
hamTerm :: Term -> Html
hamTerm (VarTerm k) = [shamlet|
<msub>
  <mi>k
  <mn>#{k}
|]
hamTerm (CoeffTerm q) = hamCoeff q
hamTerm (Sum terms) = hamOpTerm [shamlet|<mo>+|] terms
hamTerm (Diff terms) = hamOpTerm [shamlet|<mo>-|] terms
hamTerm (Minus term) = [shamlet|
<mo form="prefix" stretchy="false">(
<mo>-
#{hamTerm term}
<mo form="postfix" stretchy="false">)
|]
hamTerm (Prod terms) = hamOpTerm [shamlet|<mo lspace="0em" rspace="0em">⋅|] terms
hamTerm (ConstTerm c) = hamRat c

hamRat :: Rational -> Html
hamRat 0 = [shamlet|<mn>0|]
hamRat 1 = [shamlet|<mn>1|]
hamRat r = [shamlet|
<mfrac>
   <mn>#{numerator r}
   <mn>#{denominator r}
|]
  
hamOpTerm :: Html -> [Term] -> Html
hamOpTerm op [] = [shamlet|
<mn>0
|]
hamOpTerm op [t] = hamTerm t
hamOpTerm op terms = toHtml $ intersperse op (map hamTerm terms)

hamConstraint :: Constraint -> Html
hamConstraint (Eq t1 t2) = [shamlet|
#{hamTerm t1}
<mo>=
#{hamTerm t2}
|]
hamConstraint (Le t1 t2) = [shamlet|
#{hamTerm t1}
<mo lspace="0em" rspace="0em">≤
#{hamTerm t2}
|]
hamConstraint (Ge t1 t2) = [shamlet|
#{hamTerm t1}
<mo lspace="0em" rspace="0em">≥
#{hamTerm t2}
|]
hamConstraint (Impl c1 c2) = [shamlet|
<mo form="prefix" stretchy="false">(
#{hamConstraint c1}
<mo form="postfix" stretchy="false">)
<mo stretchy="false" lspace="0em" rspace="0em">→
<mo form="prefix" stretchy="false">(
#{hamConstraint c2}
<mo form="postfix" stretchy="false">)
|]  
hamConstraint (Not c) = [shamlet|
<mo form="prefix" stretchy="false" lspace="0em" rspace="0em">¬
<mo form="prefix" stretchy="false">(
#{hamConstraint c}
<mo form="postfix" stretchy="false">)
|]
hamConstraint (Or cs) = hamConstraintList "∨" cs
hamConstraint (And cs) = hamConstraintList "∧" cs

hamConstraintList op cs = [shamlet|
<mtable rowalign="top" columnalign="center left">
  <mtr>
    <mtd>
      <mo form="prefix">#{op}
    <mtd>
      <mtable columnalign="left">
        $forall c <- cs
          <mtr>
            <mrow>
              ^{hamConstraint c}
|]  
