{-# LANGUAGE OverloadedStrings #-}

-- | Interactive HTML rendering of a proof. The page embeds the proof as JSON
-- ("CostAnalysis.PrettyProof.Data"), which @proof.js@
-- ("CostAnalysis.PrettyProof.Assets") renders in the browser.
module CostAnalysis.PrettyProof
  ( renderProof
  , renderProofWithSources
  , proofSourceFiles
  , css
  , js
  ) where

import Data.Aeson.Text (encodeToLazyText)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text.Lazy as TL

import CostAnalysis.Analysis (AnalysisResult)
import CostAnalysis.PrettyProof.Assets (css, js)
import CostAnalysis.PrettyProof.Data (proofData, proofSourceFiles)

renderProof :: AnalysisResult -> TL.Text
renderProof = renderProofWithSources M.empty

-- | Like 'renderProof', but embeds the given source files (as lines) so the
-- viewer can show the code each rule was applied to. The files a proof refers
-- to are given by 'proofSourceFiles'.
renderProofWithSources :: Map FilePath [Text] -> AnalysisResult -> TL.Text
renderProofWithSources sources result = TL.concat
  [ "<!doctype html>\n"
  , "<html lang=\"en\">\n"
  , "<head>\n"
  , "<meta charset=\"utf-8\">\n"
  , "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n"
  , "<title>Atlas proof</title>\n"
  , "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n"
  , "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500&family=IBM+Plex+Sans:wght@400;500;600&display=swap\">\n"
  , "<link rel=\"stylesheet\" href=\"style.css\">\n"
  , "</head>\n"
  , "<body>\n"
  , "<div id=\"app\">\n"
  , "<header id=\"hdr\"></header>\n"
  , "<div class=\"cols\">\n"
  , "<aside id=\"left\" aria-label=\"Overview\"></aside>\n"
  , "<main id=\"mid\"><div id=\"treebar\"></div><div id=\"tree\" role=\"tree\" aria-label=\"Derivation\"></div></main>\n"
  , "<aside id=\"detail\" aria-label=\"Selected rule\"></aside>\n"
  , "</div>\n"
  , "</div>\n"
  , "<script id=\"proof-data\" type=\"application/json\">"
  , TL.replace "</" "<\\/" (encodeToLazyText (proofData sources result))
  , "</script>\n"
  , "<script src=\"proof.js\"></script>\n"
  , "</body>\n"
  , "</html>\n"
  ]
