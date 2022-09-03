module Data.TypeRig.Summable where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Either
import Data.Functor
import Data.Functor.Invariant
import Data.Kind
import Data.Semigroup
import Data.Void
import Prelude hiding ((.), id)
import qualified Text.ParserCombinators.ReadPrec as ReadPrec

infixr 2 <+++>

type Summable :: (Type -> Type) -> Constraint
class Invariant f => Summable f where
    pNone :: f Void
    default pNone :: Alternative f => f Void
    pNone = empty
    (<+++>) :: f a -> f b -> f (Either a b)
    default (<+++>) :: Alternative f => f a -> f b -> f (Either a b)
    fa <+++> fb = (fmap Left fa) <|> (fmap Right fb)

instance Summable Endo where
    pNone = Endo id
    Endo p <+++> Endo q =
        Endo $ \case
            Left a -> Left $ p a
            Right b -> Right $ q b

instance Summable m => Summable (Kleisli m a) where
    pNone = Kleisli $ \_ -> pNone
    Kleisli p <+++> Kleisli q = Kleisli $ \a -> p a <+++> q a

instance Summable ReadPrec.ReadPrec where
    ra <+++> rb = fmap Left ra ReadPrec.<++ fmap Right rb
