module Data.TypeRig.Invariant
    ( Invariant(..)
    , module Data.TypeRig.Invariant
    ) where

import Data.Functor.Invariant
import Data.Int
import Prelude hiding ((.), id)

enumMap :: (Invariant f, Enum a) => f Int -> f a
enumMap = invmap toEnum fromEnum
