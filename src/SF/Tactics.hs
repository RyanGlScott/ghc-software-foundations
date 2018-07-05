{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.Tactics where

import Data.Kind
import Data.Nat
import Data.Singletons.Prelude
import Data.Singletons.Prelude.List (Filter)
import Data.Singletons.TH (singletons)
import Data.Type.Equality ((:~:)(..))
import SF.Basics
import SF.Induction
import SF.Poly

sillyEx :: (forall (n :: Nat). Sing n -> Evenb n :~: True -> Oddb (S n) :~: True)
        -> Evenb (Lit 3) :~: True
        -> Oddb  (Lit 4) :~: True
sillyEx f r = f (sLit @3) r

revExercise1 :: forall (l :: [Nat]) (l' :: [Nat]).
                Sing l -> Sing l'
             -> l  :~: Rev l'
             -> l' :~: Rev l -- l' :~: Rev (Rev l')
revExercise1 _ sl' Refl | Refl <-  revInvolutive sl'
                        = Refl

transEqExercise :: forall (n :: Nat) (m :: Nat) (o :: Nat) (p :: Nat).
                   Sing n -> Sing m -> Sing o -> Sing p
                -> m :~: Minustwo o
                -> (n + p) :~: m
                -> (n + p) :~: Minustwo o
transEqExercise _ _ _ _ Refl Refl = Refl

inversionEx3 :: forall (x :: Type) (xx :: x) (yy :: x) (zz :: x)
                       (l :: [x]) (j :: [x]).
                (xx:yy:l) :~: (zz:j)
             -> (yy:l) :~: (xx:j)
             -> xx :~: yy
inversionEx3 _ Refl = Refl

inversionEx6 :: forall (x :: Type) (xx :: x) (yy :: x) (zz :: x)
                       (l :: [x]) (j :: [x]).
                (xx:yy:l) :~: '[]
             -> (yy:l) :~: (zz:j)
             -> xx :~: zz
inversionEx6 x _ = case x of {}

plusNNInjective :: forall (n :: Nat) (m :: Nat).
                   Sing n -> Sing m
                -> n + n :~: m + m
                -> n :~: m
plusNNInjective SZ sm Refl =
  case sm of
    SZ -> Refl
plusNNInjective (SS sn') sm Refl =
  case sm of
    SS sm'
      | Refl <- plusNSm sn' sn'
      , Refl <- plusNSm sm' sm'
      , Refl <- plusNNInjective sn' sm' Refl
      -> Refl

beqNatTrue :: forall (n :: Nat) (m :: Nat).
              Sing n -> Sing m
           -> (n == m) :~: True
           -> n :~: m
beqNatTrue SZ sm Refl =
  case sm of
    SZ -> Refl
beqNatTrue (SS sn') sm Refl =
  case sm of
    SS sm' | Refl <- beqNatTrue sn' sm' Refl
           -> Refl

nthErrorAfterLast :: forall (n :: Nat) (x :: Type) (l :: [x]).
                     Sing l
                  -> Length l :~: n
                  -> NthError l n :~: None
nthErrorAfterLast SNil Refl = Refl
nthErrorAfterLast (SCons _ sxs) Refl | Refl <- nthErrorAfterLast sxs Refl
                                     = Refl

-- TODO RGS

{-
combineSplit :: forall (x :: Type) (y :: Type) (l :: [(x,y)])
                       (l1 :: [x]) (l2 :: [y]).
                Sing l -> Sing l1 -> Sing l2
             -> Split l :~: '(l1, l2)
             -> Combine l1 l2 :~: l
combineSplit SNil sl1 sl2 Refl =
  case (sl1, sl2) of
    (SNil, SNil) -> Refl
combineSplit sl@(SCons _ sls) sl1 sl2 Refl =
  case sSplit sls of
    STuple2 _sl1 _sl2 ->
      case sSplit sl of
        STuple2 SCons{} SCons{} ->
          case (sl1, sl2) of
            (SCons{}, SCons{}) -> undefined
-}

boolFnAppliedThrice :: forall (f :: Bool ~> Bool) (b :: Bool).
                       Sing f -> Sing b
                    -> f @@ (f @@ (f @@ b)) :~: f @@ b
boolFnAppliedThrice sf sb@STrue
  = case sf @@ sb of
      SFalse ->
        case sf @@ SFalse of
          SFalse -> Refl
          STrue  -> Refl
      STrue -> Refl
boolFnAppliedThrice sf sb@SFalse
  = case sf @@ sb of
      SFalse -> Refl
      STrue ->
        case sf @@ STrue of
          SFalse -> Refl
          STrue  -> Refl

beqNatSym :: forall (n :: Nat) (m :: Nat).
             Sing n -> Sing m
          -> (n == m) :~: (m == n)
beqNatSym SZ SZ = Refl
beqNatSym SZ (SS _) = Refl
beqNatSym (SS _) SZ = Refl
beqNatSym (SS sn') (SS sm')
  | Refl <- beqNatSym sn' sm'
  = Refl

beqNatTrans :: forall (n :: Nat) (m :: Nat) (p :: Nat).
               Sing n -> Sing m -> Sing p
            -> (n == m) :~: True
            -> (m == p) :~: True
            -> (n == p) :~: True
beqNatTrans SZ       SZ       _        Refl Refl = Refl
beqNatTrans SZ       (SS _)   _        r    _    = case r of {}
beqNatTrans (SS _)   SZ       SZ       r    Refl = case r of {}
beqNatTrans (SS _)   SZ       (SS _)   r    _    = case r of {}
beqNatTrans (SS _)   (SS _)   SZ       Refl r    = case r of {}
beqNatTrans (SS sn') (SS sm') (SS sp') Refl Refl
  | Refl <- beqNatTrans sn' sm' sp' Refl Refl
  = Refl

{-
-- TODO RGS

splitCombineStatement ::
-}

filterExercise :: forall (x :: Type) (test :: x ~> Bool)
                         (xx :: x) (l :: [x]) (lf :: [x]).
                  Sing test -> Sing l
               -> Filter test l :~: (xx:lf)
               -> test @@ xx :~: True
filterExercise _     SNil           x    = case x of {}
filterExercise sTest (SCons sx sxs) Refl =
  case sTest @@ sx of
    STrue  -> Refl
    SFalse -> filterExercise sTest sxs Refl

$(singletons [d|
  forallb :: (a -> Bool) -> [a] -> Bool
  forallb _ []     = True
  forallb p (x:xs) = p x && forallb p xs

  existsb, existsb' :: (a -> Bool) -> [a] -> Bool
  existsb _ []     = False
  existsb p (x:xs) = p x || existsb p xs

  existsb' p = not . forallb (not . p)
  |])

existsbExistsb' :: forall (a :: Type) (p :: a ~> Bool) (l :: [a]).
                   Sing p -> Sing l
                -> Existsb' p l :~: Existsb p l
existsbExistsb' _  SNil = Refl
existsbExistsb' sp (SCons sx sls)
  = case sp @@ sx of
      STrue -> Refl
      SFalse
        | Refl <- existsbExistsb' sp sls
        -> Refl
