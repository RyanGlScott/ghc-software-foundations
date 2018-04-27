{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.IndProp where

import Data.Nat
import Data.Singletons.Prelude hiding (POrd(..))
import Data.Singletons.TH (singletons)
import Data.Type.Equality
import Prelude hiding (Double)
import SF.Basics
import SF.Induction
import SF.Logic

data Ev :: Nat -> Prop where
  Ev0  :: Ev Z
  EvSS :: Ev n -> Ev (S (S n))

evDouble :: forall (n :: Nat). Sing n -> Ev (Double n)
evDouble SZ      = Ev0
evDouble (SS sn) = EvSS (evDouble sn)

ssssEvEven :: forall (n :: Nat). Ev (S (S (S (S n)))) -> Ev n
ssssEvEven (EvSS (EvSS en)) = en

even5Nonsense :: Ev (Lit 5) -> (Lit 2 + Lit 2 :~: Lit 9)
even5Nonsense (EvSS (EvSS e)) = case e of {}

evSum :: forall (n :: Nat) (m :: Nat).
         Ev n -> Ev m -> Ev (n + m)
evSum Ev0       em = em
evSum (EvSS en) em = EvSS (evSum en em)

data Ev' :: Nat -> Prop where
  Ev'0   :: Ev' (Lit 0)
  Ev'2   :: Ev' (Lit 2)
  Ev'Sum :: Ev' n -> Ev' m -> Ev' (n + m)

ev'Ev :: forall (n :: Nat). Ev' n <-> Ev n
ev'Ev = (nec, suf)
  where
    nec :: forall (nn :: Nat). Ev' nn -> Ev nn
    nec Ev'0           = Ev0
    nec Ev'2           = EvSS Ev0
    nec (Ev'Sum en em) = evSum (nec en) (nec em)

    suf :: forall (nn :: Nat). Ev nn -> Ev' nn
    suf Ev0       = Ev'0
    suf (EvSS en) = Ev'Sum Ev'2 (suf en)

evEvEv :: forall (n :: Nat) (m :: Nat).
          Ev (n + m) -> Ev n -> Ev m
evEvEv enm       Ev0       = enm
evEvEv (EvSS en) (EvSS em) = evEvEv en em

evPlusPlus :: forall (n :: Nat) (m :: Nat) (p :: Nat).
              Sing n -> Sing m -> Sing p
           -> Ev (n + m) -> Ev (n + p) -> Ev (m + p)
evPlusPlus sn sm sp enm enp            -- (n + m) + (n + p)
  | Refl <- plusAssoc sn sm (sn %+ sp) -- n + (m + (n + p))
  , Refl <- plusAssoc sm sn sp         -- n + ((m + n) + p)
  , Refl <- plusComm sm sn             -- n + ((n + m) + p)
  , Refl <- plusAssoc sn sm sp         -- n + (n + (m + p))
  , Refl <- plusAssoc sn sn (sm %+ sp) -- (n + n) + (m + p)
  , Refl <- doublePlus sn              -- Double n + (m + p)
  = evEvEv (evSum enm enp) (evDouble sn)

data TotalRelation :: Nat -> Nat -> Prop where
  TR :: TotalRelation n n

data EmptyRelation :: Nat -> Nat -> Prop

data Le :: Nat -> Nat -> Prop where
  LeN :: Le n n
  LeS :: Le n m -> Le n (S m)

type (<=) = Le
infix 4 <=

type (<) (n :: Nat) = Le (S n)
infix 4 <

leTrans :: forall (m :: Nat) (n :: Nat) (o :: Nat).
           m <= n -> n <= o -> m <= o
leTrans leMN LeN         = leMN
leTrans leMN (LeS leNO') = LeS (leTrans leMN leNO')

zeroLeN :: forall (n :: Nat). Sing n -> Lit 0 <= n
zeroLeN SZ      = LeN
zeroLeN (SS sn) = LeS (zeroLeN sn)

leLiftS :: forall (n :: Nat) (m :: Nat).
           n <= m -> S n <= S m
leLiftS LeN       = LeN
leLiftS (LeS les) = LeS (leLiftS les)

leLowerS :: forall (n :: Nat) (m :: Nat).
            S n <= S m -> n <= m
leLowerS LeN                = LeN
leLowerS (LeS LeN)          = LeS LeN
leLowerS (LeS les@(LeS {})) = LeS (leLowerS les)

lePlusL :: forall (a :: Nat) (b :: Nat).
           Sing a -> Sing b
        -> a <= a + b
lePlusL SZ sb      = zeroLeN sb
lePlusL (SS sa) sb = leLiftS (lePlusL sa sb)

lePlusR :: forall (a :: Nat) (b :: Nat).
           Sing a -> Sing b
        -> b <= a + b
lePlusR sa SZ | Refl <- plus0R sa
              = zeroLeN sa
lePlusR sa (SS sb) | Refl <- plusNSm sa sb
                   = leLiftS (lePlusR sa sb)

plusLt :: forall (n1 :: Nat) (n2 :: Nat) (m :: Nat).
          Sing n1 -> Sing n2 -> Sing m
       -> n1 + n2 < m
       -> n1 < m /\ n2 < m
plusLt _ _ SZ x = case x of {}
plusLt sn1 sn2 (SS _) LeN
  | Refl <- plusNSm sn1 sn2
  = (lePlusL (SS sn1) sn2, lePlusR sn1 (SS sn2))
plusLt sn1 sn2 (SS sm) (LeS le)
  = case plusLt sn1 sn2 sm le of
      (n1LtM, n2LtM) -> (LeS n1LtM, LeS n2LtM)

ltS :: forall (n :: Nat) (m :: Nat).
       n < m -> n < S m
ltS LeN      = LeS LeN
ltS (LeS le) = LeS (ltS le)

lebComplete :: forall (n :: Nat) (m :: Nat).
               Sing n -> Sing m
            -> Leb n m :~: True -> n <= m
lebComplete SZ      sm      Refl = zeroLeN sm
lebComplete (SS _)  SZ      x    = case x of {}
lebComplete (SS sn) (SS sm) Refl = leLiftS $ lebComplete sn sm Refl

lebCorrect :: forall (n :: Nat) (m :: Nat).
              Sing n -> Sing m
           -> n <= m
           -> Leb n m :~: True
lebCorrect _  SZ      LeN = Refl
lebCorrect _  (SS sm) LeN = lemma sm
  where
    lemma :: forall (a :: Nat). Sing a
          -> Leb a a :~: True
    lemma SZ      = Refl
    lemma (SS sz) = lemma sz
lebCorrect sn sm' (LeS le) =
    case sm' of
      SS sm -> lemma sn sm (lebCorrect sn sm le)
  where
    lemma :: forall (a :: Nat) (b :: Nat).
             Sing a -> Sing b
          -> Leb a b :~: True -> Leb a (S b) :~: True
    lemma SZ      _       Refl = Refl
    lemma (SS _)  SZ      x    = case x of {}
    lemma (SS sa) (SS sb) Refl = lemma sa sb Refl

lebTrueTrans :: forall (n :: Nat) (m :: Nat) (o :: Nat).
                Sing n -> Sing m -> Sing o
             -> Leb n m :~: True
             -> Leb m o :~: True
             -> Leb n o :~: True
lebTrueTrans sn sm so nLeM mLeO
  = lebCorrect sn so $
    leTrans (lebComplete sn sm nLeM) (lebComplete sm so mLeO)

lebIff :: forall (n :: Nat) (m :: Nat).
          Sing n -> Sing m
       -> Leb n m :~: True <-> n <= m
lebIff sn sm = (nec, suf)
  where
    nec :: Leb n m :~: True -> n <= m
    nec = lebComplete sn sm

    suf :: n <= m -> Leb n m :~: True
    suf = lebCorrect sn sm

data R :: Nat -> Nat -> Nat -> Prop where
  C1 :: R Z Z Z
  C2 :: R m n o -> R (S m) n (S o)
  C3 :: R m n o -> R m (S n) (S o)
  C4 :: R (S m) (S n) (S (S o)) -> R m n o
  C5 :: R m n o -> R n m o

r112 :: R (Lit 1) (Lit 1) (Lit 2)
r112 = C3 $ C2 C1

$(singletons [d|
  fR :: Nat -> Nat -> Nat
  fR = (+)
  |])

{-
rEquivFR :: forall (m :: Nat) (n :: Nat) (o :: Nat).
            Sing m -> Sing n -> Sing o
         -> R m n o <-> FR m n :~: o
rEquivFR sm sn so = (nec sm sn so, suf sm sn so)
  where
    nec :: forall (mm :: Nat) (nn :: Nat) (oo :: Nat).
           Sing mm -> Sing nn -> Sing oo
        -> R mm nn oo -> FR mm nn :~: oo
    nec _ _ _ C1 = Refl
    nec (SS smm) snn (SS soo) (C2 c) | Refl <- nec smm snn soo c = Refl
    -- nec smm (SS snn) (SS soo) (C3 c) | Refl <- nec smm snn soo c = _
    {-
    nec (SS smm) (SS snn) (SS (SS soo)) (C4 c)
      | Refl <- nec smm snn soo c
      = _
    -}
    nec smm snn soo (C5 c) | Refl <- nec snn smm soo c
                           , Refl <- plusComm smm snn
                           = Refl

    suf :: forall (mm :: Nat) (nn :: Nat) (oo :: Nat).
           Sing mm -> Sing nn -> Sing oo
        -> FR mm nn :~: oo -> R mm nn oo
    suf SZ SZ SZ Refl = C1
    suf (SS smm) snn (SS soo) Refl = C2 $ suf smm snn soo Refl
    -- suf smm (SS snn) (SS soo) Refl = _ $ suf smm snn soo Refl
    -- suf (SS smm) (SS snn) (SS (SS soo)) Refl = _ $ suf smm snn soo Refl
    -- suf smm snn soo Refl
-}

-- TODO RGS
