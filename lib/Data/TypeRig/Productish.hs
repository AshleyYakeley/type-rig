module Data.TypeRig.Productish where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Kind
import Data.Semigroup
import Data.TypeRig.Invariant
import Prelude hiding ((.), id)
import qualified Text.ParserCombinators.ReadPrec as ReadPrec

infixr 3 <***>, ***>, <***

type Productish :: (Type -> Type) -> Constraint
class Invariant f => Productish f where
    pUnit :: f ()
    default pUnit :: Applicative f => f ()
    pUnit = pure ()
    (<***>) :: f a -> f b -> f (a, b)
    default (<***>) :: Applicative f => f a -> f b -> f (a, b)
    (<***>) = liftA2 (,)
    (***>) :: f () -> f a -> f a
    fu ***> fa = invmap (\((), a) -> a) (\a -> ((), a)) $ fu <***> fa
    (<***) :: f a -> f () -> f a
    fa <*** fu = invmap (\(a, ()) -> a) (\a -> (a, ())) $ fa <***> fu

instance Productish Endo where
    pUnit = Endo id
    Endo p <***> Endo q = Endo $ \(a, b) -> (p a, q b)

instance Productish m => Productish (Kleisli m a) where
    pUnit = Kleisli $ \_ -> pUnit
    Kleisli p <***> Kleisli q = Kleisli $ \a -> p a <***> q a

instance Productish ReadPrec.ReadPrec
