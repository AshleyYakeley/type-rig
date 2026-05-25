module Data.TypeRig.Riggable where

import Text.ParserCombinators.ReadP qualified as ReadP
import Text.ParserCombinators.ReadPrec qualified as ReadPrec

import Data.TypeRig.Productable
import Data.TypeRig.Summable
import Import

-- | Composability via a [rig](https://ncatlab.org/nlab/show/rig) of types.
type Riggable :: (Type -> Type) -> Constraint
class (Productable f, Summable f) => Riggable f where
    rOptional :: forall a. f a -> f (Maybe a)
    rOptional fa = let
        eitherToMaybe :: Either a () -> Maybe a
        eitherToMaybe (Left a) = Just a
        eitherToMaybe (Right ()) = Nothing
        maybeToEither :: Maybe a -> Either a ()
        maybeToEither (Just a) = Left a
        maybeToEither Nothing = Right ()
        in invmap eitherToMaybe maybeToEither $ fa <+++> rUnit
    rList1 :: f a -> f (NonEmpty a)
    rList1 fa = let
        pairToNonEmpty :: (a, [a]) -> NonEmpty a
        pairToNonEmpty (a, as) = a :| as
        nonEmptyToPair :: NonEmpty a -> (a, [a])
        nonEmptyToPair (a :| as) = (a, as)
        in invmap pairToNonEmpty nonEmptyToPair $ fa <***> rList fa
    rList :: f a -> f [a]
    rList fa = let
        eitherToList :: Either (NonEmpty a) () -> [a]
        eitherToList (Left (a :| aa)) = a : aa
        eitherToList (Right ()) = []
        listToEither :: [a] -> Either (NonEmpty a) ()
        listToEither (a : aa) = Left $ a :| aa
        listToEither [] = Right ()
        in invmap eitherToList listToEither $ rList1 fa <+++> rUnit

instance Riggable (Const ()) where
    rOptional (Const ()) = Const ()
    rList1 (Const ()) = Const ()
    rList (Const ()) = Const ()

instance Monoid t => Riggable (Op t) where
    rOptional (Op p) = let
        mp = \case
            Just a -> p a
            Nothing -> mempty
        in Op mp
    rList1 fa@(Op p) = Op $ let
        Op lp = rList fa
        in \(a :| aa) -> p a <> lp aa
    rList fa = Op $ let
        Op np = rList1 fa
        in \case
            a : aa -> np $ a :| aa
            [] -> mempty

instance (Invariant f, Alternative f) => Riggable (Ap f) where
    rOptional (Ap f) = Ap $ fmap Just f <|> pure Nothing
    rList1 fa@(Ap f) = let
        Ap lf = rList fa
        in Ap $ liftA2 (:|) f lf
    rList fa = let
        Ap nf = rList1 fa
        in Ap $ fmap toList nf <|> pure []

instance Riggable Endo where
    rOptional (Endo f) = Endo $ fmap f
    rList1 (Endo f) = Endo $ fmap f
    rList (Endo f) = Endo $ fmap f

instance Riggable m => Riggable (Kleisli m a) where
    rOptional (Kleisli f) = Kleisli $ \a -> rOptional $ f a
    rList1 (Kleisli f) = Kleisli $ \a -> rList1 $ f a
    rList (Kleisli f) = Kleisli $ \a -> rList $ f a

instance Riggable ReadPrec.ReadPrec where
    rOptional ra = ReadPrec.readP_to_Prec $ \prec -> ReadP.option Nothing $ fmap Just $ ReadPrec.readPrec_to_P ra prec
    rList ra = ReadPrec.readP_to_Prec $ \prec -> ReadP.many $ ReadPrec.readPrec_to_P ra prec
