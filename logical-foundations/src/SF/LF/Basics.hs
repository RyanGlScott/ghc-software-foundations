{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.Basics where

import Data.Nat
import Data.Singletons.TH
import Prelude.Singletons

$(singletons [d|
  negb :: Bool -> Bool
  negb = not

  andb :: Bool -> Bool -> Bool
  andb = (&&)

  orb :: Bool -> Bool -> Bool
  orb = (||)

  nandb :: Bool -> Bool -> Bool
  nandb True  x = not x
  nandb False _ = True
  |])

testNandb1 :: Nandb True False :~: True
testNandb1 = Refl

testNandb2 :: Nandb False False :~: True
testNandb2 = Refl

testNandb3 :: Nandb False True :~: True
testNandb3 = Refl

testNandb4 :: Nandb True True :~: False
testNandb4 = Refl

$(singletons [d|
  andb3 :: Bool -> Bool -> Bool -> Bool
  andb3 True  x y = x && y
  andb3 False _ _ = False
  |])

testAndb31 :: Andb3 True True True :~: True
testAndb31 = Refl

testAndb32 :: Andb3 False True True :~: False
testAndb32 = Refl

testAndb33 :: Andb3 True False True :~: False
testAndb33 = Refl

testAndb34 :: Andb3 True True False :~: False
testAndb34 = Refl

$(singletons [d|
  minustwo :: Nat -> Nat
  minustwo Z         = Z
  minustwo (S Z)     = Z
  minustwo (S (S n)) = n

  factorial :: Nat -> Nat
  factorial Z        = S Z
  factorial sn@(S n) = sn * factorial n
  |])

testFactorial1 :: Factorial (Lit 3) :~: Lit 6
testFactorial1 = Refl

testFactorial2 :: Factorial (Lit 5) :~: Lit 10 * Lit 12
testFactorial2 = Refl

$(singletons [d|
  bltNat :: Nat -> Nat -> Bool
  bltNat = (<)
  |])

testBltNat1 :: BltNat (Lit 2) (Lit 2) :~: False
testBltNat1 = Refl

testBltNat2 :: BltNat (Lit 2) (Lit 4) :~: True
testBltNat2 = Refl

testBltNat3 :: BltNat (Lit 4) (Lit 2) :~: False
testBltNat3 = Refl

plusIdExercise
  :: forall (n :: Nat) (m :: Nat) (o :: Nat).
     Sing n -> Sing m -> Sing o
  -> n :~: m -> m :~: o
  -> n + m :~: m + o
plusIdExercise _ _ _ Refl Refl = Refl

multS1 :: forall (n :: Nat) (m :: Nat).
          Sing n -> Sing m
       -> m :~: S n
       -> m * (Lit 1 + n) :~: m * m
multS1 _ _ Refl = Refl

andbTrueElim2 :: forall (b :: Bool) (c :: Bool).
                 Sing b -> Sing c
              -> (b && c) :~: True
              -> c        :~: True
andbTrueElim2 STrue  _ Refl = Refl
andbTrueElim2 SFalse _ x    = case x of {}

zeroNbeqPlus1 :: forall (n :: Nat).
                 Sing n -> (Lit 0 == n + Lit 1) :~: False
zeroNbeqPlus1 SZ     = Refl
zeroNbeqPlus1 (SS _) = Refl

identityFnAppliedTwice
  :: forall (f :: Bool ~> Bool).
     (forall (x :: Bool). Sing x -> f @@ x :~: x)
  -> forall (b :: Bool). Sing b -> f @@ (f @@ b) :~: b
identityFnAppliedTwice f x | Refl <- f x = Refl

negationFnAppliedTwice
  :: forall (f :: Bool ~> Bool).
     (forall (x :: Bool). Sing x -> f @@ x :~: Not x)
  -> forall (b :: Bool). Sing b -> f @@ (f @@ b) :~: b
negationFnAppliedTwice f x
  | Refl <- doubleNegation x
  , Refl <- f x
  , Refl <- f (sNot x)
  = Refl
  where
    doubleNegation :: forall (z :: Bool). Sing z -> Not (Not z) :~: z
    doubleNegation STrue  = Refl
    doubleNegation SFalse = Refl

andbEqOrb :: forall (b :: Bool) (c :: Bool).
             Sing b -> Sing c
          -> (b && c) :~: (b || c)
          -> b :~: c
andbEqOrb STrue  _ Refl = Refl
andbEqOrb SFalse _ Refl = Refl

$(singletons [d|
  data Bin = Zero | Even Bin | Odd Bin

  incr :: Bin -> Bin
  incr Zero     = Odd Zero      -- 0 + 1 = (2*0) + 1
  incr (Even n) = Odd n         -- 2n + 1
  incr (Odd n)  = Even (incr n) -- (2n + 1) + 1 = 2*(n + 1)

  binToNat :: Bin -> Nat
  binToNat Zero     = Z
  binToNat (Even n) = binToNat n +  binToNat n
  binToNat (Odd  n) = S (binToNat n + binToNat n)
  |])

warble :: forall (b :: Bin). Sing b
       -> BinToNat (Incr b) :~: S (BinToNat b)
warble SZero = Refl
warble (SEven {}) = Refl
warble (SOdd  sb) | Refl <- warble sb
                  , Refl <- plusComm sbn (SS sbn)
                  = Refl
  where
    sbn = sBinToNat sb

    plus0R :: forall (n :: Nat).
              Sing n -> n + Lit 0 :~: n
    plus0R SZ = Refl
    plus0R (SS sn) | Refl <- plus0R sn = Refl

    plusSnR :: forall (n :: Nat) (m :: Nat).
               Sing n -> Sing m
            -> n + S m :~: S (n + m)
    plusSnR SZ _ = Refl
    plusSnR (SS sn) sm | Refl <- plusSnR sn sm = Refl

    plusComm :: forall (n :: Nat) (m :: Nat).
                Sing n -> Sing m
             -> n + m :~: m + n
    plusComm SZ sm | Refl <- plus0R sm = Refl
    plusComm (SS sn) sm | Refl <- plusComm sn sm
                        , Refl <- plusSnR sm sn
                        = Refl

$(singletons [d|
  beqNat :: Nat -> Nat -> Bool
  beqNat = (==)

  leb :: Nat -> Nat -> Bool
  leb Z _ = True
  leb (S _) Z = False
  leb (S n') (S m') = leb n' m'
  |])
