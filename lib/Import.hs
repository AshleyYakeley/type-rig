{-# OPTIONS -fno-warn-orphans #-}
module Import (module I) where

import Control.Applicative as I
import Control.Arrow as I
import Control.Category as I
import Data.Foldable as I
import Data.Functor.Invariant as I
import Data.Kind as I
import Data.List.NonEmpty as I (NonEmpty (..))
import Data.Monoid as I hiding (First (..), Last (..))
import Data.Semigroup as I
import Data.Void as I
import Prelude as I hiding (id, (.))

instance Invariant f => Invariant (Ap f)
