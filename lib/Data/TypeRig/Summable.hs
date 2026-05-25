module Data.TypeRig.Summable where

import Text.ParserCombinators.ReadPrec qualified as ReadPrec

import Import

infixr 2 <+++>

-- | Composability via type sum 'Either' and empty type 'Void'.
type Summable :: (Type -> Type) -> Constraint
class Invariant f => Summable f where
    rVoid :: f Void
    default rVoid :: Alternative f => f Void
    rVoid = empty
    (<+++>) :: f a -> f b -> f (Either a b)
    default (<+++>) :: Alternative f => f a -> f b -> f (Either a b)
    fa <+++> fb = (fmap Left fa) <|> (fmap Right fb)

instance Summable (Const ()) where
    rVoid = Const ()
    Const () <+++> Const () = Const ()

instance Summable Equivalence where
    rVoid = Equivalence $ \p -> absurd p
    Equivalence a <+++> Equivalence b = let
        ab (Left p) (Left q) = a p q
        ab (Right p) (Right q) = b p q
        ab _ _ = False
        in Equivalence ab

instance Summable (Op t) where
    rVoid = Op absurd
    Op ap <+++> Op bp = Op $ \case
        Left a -> ap a
        Right b -> bp b

instance (Invariant f, Alternative f) => Summable (Ap f)

instance Summable Endo where
    rVoid = Endo id
    Endo p <+++> Endo q =
        Endo $ \case
            Left a -> Left $ p a
            Right b -> Right $ q b

instance Summable m => Summable (Kleisli m a) where
    rVoid = Kleisli $ \_ -> rVoid
    Kleisli p <+++> Kleisli q = Kleisli $ \a -> p a <+++> q a

instance Summable ReadPrec.ReadPrec where
    ra <+++> rb = fmap Left ra ReadPrec.<++ fmap Right rb
