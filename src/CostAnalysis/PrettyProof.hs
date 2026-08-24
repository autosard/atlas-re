{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}

module CostAnalysis.PrettyProof
  ( renderProof
  , css
  , js
  ) where

import Data.Text.Lazy(Text)
import Data.Set(Set)
import Data.Map(Map)
import qualified Data.Map as M
import Text.Blaze.Html.Renderer.Text(renderHtml)
import Text.Blaze.Html(Html, toHtml)
import Text.Hamlet (shamlet)
import Text.Lucius 
import qualified Data.Tree as T
import qualified Data.Set as S
import qualified Data.Text as Text
import Text.Julius hiding (js)
import Data.Char(toLower)
import Data.List(intersperse)
import Data.Ratio
import qualified Data.MultiSet as MSet


import Syntax (Id)
import Syntax.Annotation
import Syntax.PrettyPrint
import Syntax.Program
import Syntax.Expression
import Syntax.Pattern
import CostAnalysis.Constraint
import CostAnalysis.ProveMonad
import CostAnalysis.Rules
import CostAnalysis.Template(FreeTemplate(..), BoundTemplate (BoundTemplate), bindTemplate)
import CostAnalysis.Coeff
import Syntax.ResourceExpression
import Syntax.ResourceExpression.Size hiding (ConstTerm, VarTerm)
import CostAnalysis.Analysis (AnalysisResult (..))
import Syntax.Measure (SizeTransform (SizeTransform), ConstPat(..))
import Syntax.Types.Scheme (Scheme)
import qualified Syntax.Measure(Relation(..))

css = renderCss ([lucius|

body {
  background: #2E3440;
  color: #D8DEE9;
}

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
  
  border-left: thin solid #D8DEE9;
}

ul.tree li:before {
    position: absolute;
    top: 0;
    left: 0;

    width: 0.9em;
    height: 0.7em;
    margin-right: 0.1em;
    vertical-align: top;
    border-bottom: thin solid #D8DEE9;
    content: "";
    display: inline-block;
}

ul.tree li:last-child {
    border-left: none;
}

ul.tree li:last-child:before {
    border-left: thin solid #D8DEE9;
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
  color: #BF616A;
}

.app:has(.unsat) > .toggle {
  color: #BF616A;
}

.unsat {
  color: #BF616A;
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
  color: #BF616A;
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
    let head = ul.parentElement.querySelector(".listHead")
    tog.appendChild(head);
    tog.className = "toggle";
    head.firstChild.onclick = () => tog.classList.toggle("show");
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

type Result = Either (Set Formula) (Map Coeff Rational)

renderProof :: AnalysisResult -> Text
renderProof result = renderHtml [shamlet|
$doctype 5
<html>
    <link rel="stylesheet" href="style.css">
    <script src="proof.js">
    <head>
        <title>Atlas
    <body>
        <h2>Result
        $if sat
          <p> sat
        $else
          <p class="unsat">unsat
        <h2>Size Signature
        ^{hamSizeSig (_arSizeSig result)}
        <h2>Potential Functions
        ^{hamPotentialFunctions result' (_arPotSig result)}
        <h2>Signature Constraints
        ^{hamCsList (_arSigCs result) (inCore result')}
        <h2>Derivation
        <div class="deriv-flags">
            <input type=checkbox id="onlyUnsat">show only unsat constraints
        <br>
        ^{hamDerivs result' (_arDerivs result)}
|]
  where (result', sat) = case _arResult result of
          Left core -> (Left $ S.fromList core, False)
          Right sol -> (Right (fst sol), True)
        
  
          
inCore result c = case result of
                   Left core -> S.member c core
                   Right _ -> False

hamSizeSig :: Map Id SizeTransform -> Html
hamSizeSig sig = [shamlet|
<span class="listHead">
    <span> Size Signature
<ul class="collapse tree">
    $forall (fn, trans) <- sigs
        <li class="fn">
          <math display="inline">
            <mrow>
              <mi>#{fn}
              <mo form="infix">:
              ^{hamSizeTransform fn trans}
|]
  where sigs = M.toList sig

hamPotentialFunctions :: Result -> Map Scheme [(ConstPat, FreeTemplate)] -> Html
hamPotentialFunctions result env = [shamlet|
<ul>
    $forall (t, e) <- pots
        <li>
          <math display="inline">
          <mrow>
          <mi>#{show t}
          ^{hamPotentialFunction result e}
|]
  where pots = M.toList env

hamPotentialFunction :: Result -> [(ConstPat, FreeTemplate)] -> Html
hamPotentialFunction result clauses = [shamlet|
<ul class="fn">
   $forall (lhs, rhs) <- clauses
     <li class="fn">
       <math display="inline">
         <mrow>
           <mi>𝜙
           <mo form="prefix" stretchy="false">(
           <mi>^{hamConstPattern lhs}
           <mo form="postfix" stretchy="false">)
           <mo form="infix">=
           ^{hamTemplUnderResult result rhs}
|]

hamConstPattern :: ConstPat -> Html
hamConstPattern (ConstPat name args) = [shamlet|
<mi>#{name}
$forall arg <- args
  <mo>&ApplyFunction;
  <mi>#{arg}
|]

hamSizeTransform :: Id -> SizeTransform -> Html
hamSizeTransform fn (SizeTransform lhs rhs rel) = [shamlet|
<mo rspace=0>|
<mo lspace=0>#{fn}
$forall arg <- lhs
  <mo>&ApplyFunction;
  <mi>#{arg}
<mo lspace=0 rspace=0>|  
$case rel
  $of Syntax.Measure.Ge
     <mo>≤
  $of Syntax.Measure.Eq
     <mo>=
^{hamSizeSum rhs}
|]
                  
hamDerivs :: Result -> Map Id [Derivation] -> Html
hamDerivs result derivs = let fnDerivs = M.toList derivs in
  [shamlet|
<ul class="collapse tree">
    $forall fnDeriv <- fnDerivs
        <li class="fn">^{hamFnDerivs result fnDeriv}
|]

hamFnDerivs :: Result -> (Id, [Derivation]) -> Html
hamFnDerivs result (fn, derivs) =  [shamlet|
<span class="listHead">
    <span> #{fn}
<ul class="collapse tree">      
    $forall deriv <- derivs
        <li class="fn">^{hamDeriv result deriv}
|]

hamDeriv :: Result -> Derivation -> Html
hamDeriv result (T.Node appl []) = [shamlet|#{hamRuleApp result appl}|]  
hamDeriv result (T.Node appl children) = [shamlet|
#{hamRuleApp result appl}
<ul class="collapse tree">
    $forall child <- children
        <li .app>^{hamDeriv result child}
|]
  

hamRuleApp :: Result -> RuleApp -> Html
hamRuleApp result (MatchArmApp pat RuleAppInfo{_raJt=jt
                                               ,_raQ=q
                                               ,_raQ'=q'
                                               ,_raCs=cs
                                               ,_raExpr=e})
  = [shamlet|
<span .listHead :((not . null) cs'):.unsat>
  <math display="inline">
    <mrow>
      <mtext>case
      <mo>: 
      ^{hamPattern pat}
      ^{hamCsList cs (inCore result)}|]
  where cs' = case result of
          Left core -> S.toList $ S.intersection (S.fromList cs) core
          Right _ -> []
  
hamRuleApp result (ExprRuleApp rule RuleAppInfo{_raJt=jt
                                               ,_raQ=q
                                               ,_raQ'=q'
                                               ,_raCs=cs
                                               ,_raExpr=e})
  = [shamlet|
<span .listHead :((not . null) cs'):.unsat>
  <math display="inline">
    <mrow>
      <mo form="prefix" stretchy="false">(
      <mtext>#{printRule jt rule}
      <mo form="postfix" stretchy="false">)
      <mspace width="1em">
      ^{hamTemplUnderResult result q}
      <mo>⊢
      <mtext>
          <code>#{prettyPrint e}
          (#{printPos srcPos})  
      <mo lspace="0.22em" rspace="0.22em" stretchy="false">|
      ^{hamTemplUnderResult result q'}
      ^{hamCsList cs (inCore result)}
|]
  where srcPos = case peSrc $ getAnn e of
          Loc pos -> pos
          DerivedFrom pos -> pos
        cs' = case result of
          Left core -> S.toList $ S.intersection (S.fromList cs) core
          Right _ -> []

hamTemplUnderResult :: Result -> FreeTemplate -> Html 
hamTemplUnderResult result q = [shamlet|
$case result
  $of Left _ 
    ^{hamTempl q}
  $of Right sol
    ^{hamTempl q}
    <mo>:
    ^{hamBoundTempl (bindTemplate q sol)}
|]
  
printRule :: JudgementType -> Rule -> String
printRule jt rule = map toLower (show rule)
  ++ "(" ++ show jt ++ ")"

hamCsList :: [Formula] -> (Formula -> Bool) -> Html
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

hamPattern :: Pattern a -> Html
hamPattern (PVar _ x) = [shamlet|
  <mi>#{Text.unpack x}</mi>
|]
hamPattern (PWildcard _) = [shamlet|
  <mo>_</mo>
|]
hamPattern (PConst _ constructor args) = [shamlet|
  <mrow>
    <mi>#{Text.unpack constructor}</mi>
    $if not (null args)
      <mo>⁡</mo>
      <mfenced>
        ^{hamPatterns args}
|]

-- Helper to join pattern arguments with commas
hamPatterns :: [Pattern a] -> Html
hamPatterns [] = [shamlet| |]
hamPatterns [p] = hamPattern p
hamPatterns patList = toHtml $ intersperse [shamlet|<mo separator="true">,</mo>|] (map hamPattern patList)  

hamArgs :: [Id] -> Html
hamArgs [] = [shamlet|<mi>∅|]
hamArgs args = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map hamArg args)
  where hamArg arg = [shamlet|<mi>#{Text.unpack arg}|]
        
hamBoundTempl :: BoundTemplate -> Html
hamBoundTempl (BoundTemplate coeffs) = 
  let activeTerms = filter (\(_, val) -> val /= 0) (M.toList coeffs)
  in case activeTerms of
    [] -> [shamlet|<mn>0</mn>|]
    (first : rest) -> [shamlet|
      <mrow>
        ^{hamFirstTerm first}
        $forall term <- rest
          ^{hamRestTerm term}
    |]
  where
    -- Renders the very first term (handling an implicit positive sign or explicit negative)
    hamFirstTerm (rt, val)
      | val == 1  = [shamlet|^{hamResourceTerm rt}|]
      | val == -1 = [shamlet|<mo>-</mo>^{hamResourceTerm rt}|]
      | otherwise = [shamlet|^{hamRat val}<mo>⋅</mo>^{hamResourceTerm rt}|]

    -- Renders subsequent terms with correct sign operators
    hamRestTerm (RTId, val) 
      | val == 1  = [shamlet|<mo>+</mo><mn>1</mn>|]
      | val == -1 = [shamlet|<mo>-</mo><mn>1</mn>|]
      | val > 0   = [shamlet|<mo>+</mo>^{hamRat val}|]
      | otherwise = [shamlet|<mo>-</mo>^{hamRat (abs val)}|]
    hamRestTerm (rt, val)
      | val == 1  = [shamlet|<mo>+</mo>^{hamResourceTerm rt}|]
      | val == -1 = [shamlet|<mo>-</mo>^{hamResourceTerm rt}|]
      | val > 0   = [shamlet|<mo>+</mo>^{hamRat val}<mo>⋅</mo>^{hamResourceTerm rt}|]
      | otherwise = [shamlet|<mo>-</mo>^{hamRat (abs val)}<mo>⋅</mo>^{hamResourceTerm rt}|]
          
          
hamTempl :: FreeTemplate -> Html
hamTempl q = [shamlet|
<msubsup>
    <mi>Q
    <mn>#{_ftId q}
|]

hamListInt :: [Int] -> Html
hamListInt xs = toHtml $ intersperse
  [shamlet|<mo separator="true">,|]
  (map (\x -> [shamlet|<mn>#{x}|]) xs)
  
hamCoeff :: Coeff -> Html
hamCoeff (Coeff id term) = [shamlet|
<msub>
  <mi>Q
  <mn>#{id}
<mo form="prefix" stretchy="false">[
^{hamResourceTerm term}
<mo form="prefix" stretchy="false">]
|]
  
hamArithExpr :: ArithExpr -> Html
hamArithExpr (VarTerm k) = [shamlet|
<msub>
  <mi>k
  <mn>#{k}
|]
hamArithExpr (CoeffTerm q) = hamCoeff q
hamArithExpr (Sum terms) = hamOpTerm [shamlet|<mo>+|] terms
hamArithExpr (Diff terms) = hamOpTerm [shamlet|<mo>-|] terms
hamArithExpr (Minus term) = [shamlet|
<mo form="prefix" stretchy="false">(
<mo>-
#{hamArithExpr term}
<mo form="postfix" stretchy="false">)
|]
hamArithExpr (Prod terms) = hamOpTerm [shamlet|<mo lspace="0em" rspace="0em">⋅|] terms
hamArithExpr (ConstTerm c) = hamRat c

hamRat :: Rational -> Html
hamRat 0 = [shamlet|<mn>0|]
hamRat 1 = [shamlet|<mn>1|]
hamRat r | denominator r == 1
  = [shamlet|<mn>#{numerator r}|]
hamRat r = [shamlet|
<mfrac>
   <mn>#{numerator r}
   <mn>#{denominator r}
|]
  
hamOpTerm :: Html -> [ArithExpr] -> Html
hamOpTerm op [] = [shamlet|
<mn>0
|]
hamOpTerm op [t] = hamArithExpr t
hamOpTerm op terms = toHtml $ intersperse op (map hamArithExpr terms)

hamConstraint :: Formula -> Html
hamConstraint (Eq t1 t2) = [shamlet|
#{hamArithExpr t1}
<mo>=
#{hamArithExpr t2}
|]
hamConstraint (Le t1 t2) = [shamlet|
#{hamArithExpr t1}
<mo lspace="0em" rspace="0em">≤
#{hamArithExpr t2}
|]
hamConstraint (Ge t1 t2) = [shamlet|
#{hamArithExpr t1}
<mo lspace="0em" rspace="0em">≥
#{hamArithExpr t2}
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
hamConstraint (Iff c1 c2) = [shamlet|
<mo form="prefix" stretchy="false">(
#{hamConstraint c1}
<mo form="postfix" stretchy="false">)
<mo stretchy="false" lspace="0em" rspace="0em">↔
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
hamConstraint (Atom v) = [shamlet|
<msub>
  <mi>b
  <mn>#{v}
|]
hamConstraint Bot = [shamlet|⊥|]

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

hamSize :: Id -> Html
hamSize x = [shamlet|
<mo form="prefix" stretchy="false">|
<mi>#{Text.unpack x}
<mo form="postfix" stretchy="false">|
|]


hamResourceTerm :: ResourceTerm -> Html
hamResourceTerm (RTSize s) = hamSize s

hamResourceTerm (RTBinom ss k) = [shamlet|
  <mo form="prefix" stretchy="true">(
  <mfrac linethickness="0">
    <mrow>
      ^{hamSizeSum ss}
    <mn>#{k}
  <mo form="postfix" stretchy="true">)    
|]
hamResourceTerm (RTProd ts) = toHtml $ intersperse [shamlet|<mo>⋅|]
  (map hamResourceTerm (MSet.toList ts))
      
hamResourceTerm (RTLog sizes) = [shamlet|
<mi>log
<mo form="prefix" stretchy="false">(
^{hamSizeSum sizes}
<mo form="postfix" stretchy="false">)  
|]

-- Potential function: e.g., Φ(x)
hamResourceTerm (RTPhi x) = [shamlet|
<mi>𝜙
<mo form="prefix" stretchy="false">(
<mi>#{Text.unpack x}
<mo form="postfix" stretchy="false">)
|]

-- Constant 1 term
hamResourceTerm RTId = [shamlet|<mn>1</mn>|]

-- Scaled resource terms: e.g., 3/2 * RT
hamResourceTerm (RTScale r term) = [shamlet|
^{hamRat r}
<mo>⋅
<mo form="prefix" stretchy="false">(
^{hamResourceTerm term}
<mo form="postfix" stretchy="false">)
|]


hamSizeSum :: SizeSum -> Html
hamSizeSum (SizeSum cs k) = case (M.toList cs, k) of
  ([], 0) -> [shamlet|<mn>0|]
  ([], k) -> [shamlet|<mn>#{k}|]
  (s:ss, k) -> [shamlet|
  ^{hamSizeTermSigned False s}
  $forall term <- ss
    ^{hamSizeTermSigned True term}
  $if k > 0
    <mo>+
    <mn>#{k}
  $if k < 0
    <mo>-
    <mn>#{abs k}
|]
    
hamSizeTermSigned :: Bool -> (Id, Int) -> Html
hamSizeTermSigned showLeadingPlus (varId, coeff) = [shamlet|
$if coeff < 0
  <mo>-
  $if coeff > 1
    <mn>#{abs coeff}
  <mi>^{hamSize varId}
$else
    $if coeff > 0
      $if showLeadingPlus
        <mo>+
      $if coeff > 1  
        <mn>#{abs coeff}  
      <mi>^{hamSize varId}
|]
