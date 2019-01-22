{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.Induction where

import Data.Nat
import Data.Singletons.Prelude
import Data.Singletons.TH
import Prelude hiding (Double)

mult0R :: forall (n :: Nat). Sing n -> n * Lit 0 :~: Lit 0
mult0R SZ = Refl
mult0R (SS sn) | Refl <- mult0R sn = Refl

plusNSm :: forall (n :: Nat) (m :: Nat).
           Sing n -> Sing m
        -> S (n + m) :~: n + S m
plusNSm SZ      _  = Refl
plusNSm (SS sn) sm | Refl <- plusNSm sn sm = Refl

plus0R :: forall (n :: Nat).
          Sing n -> n + Lit 0 :~: n
plus0R SZ = Refl
plus0R (SS sn) | Refl <- plus0R sn = Refl

plusComm :: forall (n :: Nat) (m :: Nat).
            Sing n -> Sing m
         -> n + m :~: m + n
plusComm SZ sm | Refl <- plus0R sm = Refl
plusComm (SS sn) sm | Refl <- plusComm sn sm
                    , Refl <- plusNSm sm sn
                    = Refl

plusAssoc :: forall (n :: Nat) (m :: Nat) (p :: Nat).
             Sing n -> Sing m -> Sing p
          -> n + (m + p) :~: (n + m) + p
plusAssoc SZ _ _ = Refl
plusAssoc (SS sn) sm sp | Refl <- plusAssoc sn sm sp = Refl

$(singletons [d|
  double :: Nat -> Nat
  double Z = Z
  double (S n) = S (S (double n))
  |])

doublePlus :: forall (n :: Nat). Sing n
           -> Double n :~: n + n
doublePlus SZ = Refl
doublePlus ssn@(SS sn) | Refl <- doublePlus sn
                       , Refl <- plusComm sn ssn
                       = Refl

$(singletons [d|
  evenb :: Nat -> Bool
  evenb Z = True
  evenb (S Z) = False
  evenb (S (S n)) = evenb n

  oddb :: Nat -> Bool
  oddb Z         = False
  oddb (S Z)     = True
  oddb (S (S n)) = oddb n
  |])

evenbS :: forall (n :: Nat). Sing n
       -> Evenb (S n) :~: Not (Evenb n)
evenbS SZ = Refl
evenbS (SS SZ) = Refl
evenbS (SS (SS sn)) | Refl <- evenbS sn = Refl

beqNatRefl :: forall (n :: Nat). Sing n
           -> (n == n) :~: True
beqNatRefl SZ = Refl
beqNatRefl (SS sn) | Refl <- beqNatRefl sn = Refl
