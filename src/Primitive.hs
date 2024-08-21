module Primitive where

import Data.Text(Text)
import qualified Data.Text as T

type Id = Text

enumId :: Int -> Id
enumId n = T.pack $ "?" ++ show n

