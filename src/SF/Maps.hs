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
module SF.Maps where

import Data.Kind
import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Text (Text)
import Data.Type.Equality (gcastWith)
import Data.Void
import GHC.TypeLits (CmpSymbol)
import SF.Axiom
import SF.Logic

type TotalMap' (p :: Type ~> Type ~> Type) (sym :: Type) (a :: Type) = p @@ sym @@ a
type TotalMap  a = TotalMap' (TyCon2 (->)) Text   a
type PTotalMap a = TotalMap' (~>@#@$)      Symbol a

tEmpty :: a -> TotalMap a
tEmpty v _ = v

type family TEmpty (v :: a) :: PTotalMap a where
  TEmpty v = ConstSym1 v

tUpdate :: TotalMap a -> Text -> a -> Text -> a
tUpdate m x v x' = if (x `compare` x' == EQ) then v else m x'

type family TUpdateAux (m :: PTotalMap a) (x :: Symbol) (v :: a) (x' :: Symbol) :: a where
  TUpdateAux m x v x' = If (x `CmpSymbol` x' == EQ) v (m @@ x')
$(genDefunSymbols [''TUpdateAux])
type family TUpdate (m :: PTotalMap a) (x :: Symbol) (v :: a) :: PTotalMap a where
  TUpdate m x v = TUpdateAuxSym3 m x v

data KV a b = a :-> b
infixr 0 :->

type family (m :: PTotalMap a) & (l :: [KV Symbol a]) where
  m & '[]               = m
  m & ((k :-> v) : kvs) = TUpdate m k v & kvs
infixl 9 &

tApplyEmpty :: forall (a :: Type) (x :: Symbol) (v :: a).
               TEmpty v @@ x :~: v
tApplyEmpty = Refl

tUpdateEq :: forall (a :: Type) (m :: PTotalMap a) (x :: Symbol) (v :: a).
             m & '[x :-> v] @@ x :~: v
tUpdateEq = Refl

-- Alas, given constraints (Compare s1 s2 ~ EQ) don't imply that (s1 ~ s2), so
-- we have to graft this proof together.
sCompare' :: forall (s1 :: Symbol) (s2 :: Symbol) r.
             Sing s1 -> Sing s2
          -> (s1 ~ s2 => r)
          -> (CmpSymbol s1 s2 ~ LT => r)
          -> (CmpSymbol s1 s2 ~ GT => r)
          -> r
sCompare' s1 s2 eqCase ltCase gtCase =
  case sCompare s1 s2 of
    SLT -> ltCase
    SGT -> gtCase
    SEQ -> gcastWith (axiom @s1 @s2) eqCase

tUpdateNeq :: forall (a :: Type) (v :: a) (x1 :: Symbol) (x2 :: Symbol) (m :: PTotalMap a).
              Sing x1 -> Sing x2
           -> x1 :/: x2 -> (m & '[x1 :-> v]) @@ x2 :~: m @@ x2
tUpdateNeq sx1 sx2 ne12
  = sCompare' sx1 sx2 (absurd $ ne12 Refl) Refl Refl

tUpdateShadow :: forall (a :: Type) (m :: PTotalMap a) (v1 :: a) (v2 :: a) (x :: Symbol).
                 Sing x
              -> m & '[x :-> v1, x :-> v2] :~: m & '[x :-> v2]
tUpdateShadow sx = funExt go
  where
    go :: forall (x2 :: Symbol).
          Sing x2
       -> (m & '[x :-> v1, x :-> v2]) @@ x2 :~: (m & '[x :-> v2]) @@ x2
    go sx2 = case sx `sCompare` sx2 of
               SEQ -> Refl
               SLT -> Refl
               SGT -> Refl

-- TODO RGS
