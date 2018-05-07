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
module SF.ProofObjects where

import Data.Kind
import Data.Nat
import Data.Singletons.Prelude
import Data.Singletons.Sigma
import Data.Type.Equality
import SF.IndProp
import SF.Logic

ev8' :: Ev (Lit 8)
ev8' = EvSS $ EvSS $ EvSS $ EvSS Ev0

conjFact :: forall (p :: Prop) (q :: Prop) (r :: Prop).
            p /\ q -> q /\ r -> p /\ r
conjFact (p, _) (_, r) = (p, r)

orComm :: forall (p :: Prop) (q :: Prop).
          p \/ q -> q \/ p
orComm = either Right Left

type Ex s (t :: s ~> Type) = Sigma s t

exEvSn :: Ex Nat (TyCon1 Ev .@#@$$$ TyCon1 S)
exEvSn = SS SZ :&: EvSS Ev0

equalityLeibnizEquality
  :: forall (x :: Type) (xx :: x) (yy :: x).
     xx :~: yy -> (forall (p :: x ~> Prop). p @@ xx -> p @@ yy)
equalityLeibnizEquality Refl = id

leibnizEqualityEquality
  :: forall (x :: Type) (xx :: x) (yy :: x).
     (forall (p :: x ~> Prop). p @@ xx -> p @@ yy) -> xx :~: yy
leibnizEqualityEquality f = f @(TyCon1 ((:~:) xx)) Refl
