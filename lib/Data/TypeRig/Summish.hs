module Data.TypeRig.Summish where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Either
import Data.Functor
import Data.Kind
import Data.Semigroup
import Data.TypeRig.Invariant
import Data.Void
import Prelude hiding ((.), id)
import qualified Text.ParserCombinators.ReadPrec as ReadPrec

infixr 2 <+++>

type Summish :: (Type -> Type) -> Constraint
class Invariant f => Summish f where
    pNone :: f Void
    default pNone :: Alternative f => f Void
    pNone = empty
    (<+++>) :: f a -> f b -> f (Either a b)
    default (<+++>) :: Alternative f => f a -> f b -> f (Either a b)
    fa <+++> fb = (fmap Left fa) <|> (fmap Right fb)

pSumLeft :: Summish f => f a -> f a -> f a
pSumLeft fa fb = invmap (either id id) Left $ fa <+++> fb

instance Summish Endo where
    pNone = Endo id
    Endo p <+++> Endo q =
        Endo $ \case
            Left a -> Left $ p a
            Right b -> Right $ q b

instance Summish m => Summish (Kleisli m a) where
    pNone = Kleisli $ \_ -> pNone
    Kleisli p <+++> Kleisli q = Kleisli $ \a -> p a <+++> q a

instance Summish ReadPrec.ReadPrec where
    ra <+++> rb = fmap Left ra ReadPrec.<++ fmap Right rb
