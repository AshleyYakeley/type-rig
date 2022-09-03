module Data.TypeRig.Riggable where

import Control.Arrow
import Data.Either
import Data.Functor
import Data.Functor.Invariant
import Data.Kind
import Data.List.NonEmpty
import Data.Maybe
import Data.Semigroup
import Data.TypeRig.Productable
import Data.TypeRig.Summable
import Prelude hiding ((.), id)
import qualified Text.ParserCombinators.ReadP as ReadP
import qualified Text.ParserCombinators.ReadPrec as ReadPrec

type Riggable :: (Type -> Type) -> Constraint
class (Productable f, Summable f) => Riggable f where
    pOptional :: forall a. f a -> f (Maybe a)
    pOptional fa = let
        eitherToMaybe :: Either a () -> Maybe a
        eitherToMaybe (Left a) = Just a
        eitherToMaybe (Right ()) = Nothing
        maybeToEither :: Maybe a -> Either a ()
        maybeToEither (Just a) = Left a
        maybeToEither Nothing = Right ()
        in invmap eitherToMaybe maybeToEither $ fa <+++> pUnit
    pList1 :: f a -> f (NonEmpty a)
    pList1 fa = let
        pairToNonEmpty :: (a, [a]) -> NonEmpty a
        pairToNonEmpty (a, as) = a :| as
        nonEmptyToPair :: NonEmpty a -> (a, [a])
        nonEmptyToPair (a :| as) = (a, as)
        in invmap pairToNonEmpty nonEmptyToPair $ fa <***> pList fa
    pList :: f a -> f [a]
    pList fa = let
        eitherToList :: Either (NonEmpty a) () -> [a]
        eitherToList (Left (a :| aa)) = a : aa
        eitherToList (Right ()) = []
        listToEither :: [a] -> Either (NonEmpty a) ()
        listToEither (a:aa) = Left $ a :| aa
        listToEither [] = Right ()
        in invmap eitherToList listToEither $ pList1 fa <+++> pUnit

instance Riggable Endo where
    pOptional (Endo f) = Endo $ fmap f
    pList1 (Endo f) = Endo $ fmap f
    pList (Endo f) = Endo $ fmap f

instance Riggable m => Riggable (Kleisli m a) where
    pOptional (Kleisli f) = Kleisli $ \a -> pOptional $ f a
    pList1 (Kleisli f) = Kleisli $ \a -> pList1 $ f a
    pList (Kleisli f) = Kleisli $ \a -> pList $ f a

instance Riggable ReadPrec.ReadPrec where
    pOptional ra = ReadPrec.readP_to_Prec $ \prec -> ReadP.option Nothing $ fmap Just $ ReadPrec.readPrec_to_P ra prec
    pList ra = ReadPrec.readP_to_Prec $ \prec -> ReadP.many $ ReadPrec.readPrec_to_P ra prec
