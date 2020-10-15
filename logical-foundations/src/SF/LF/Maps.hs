{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.Maps where

import Data.Kind
import Data.Singletons.TH
import Data.Text (Text)
import Data.Tuple
import Data.Void
import GHC.TypeLits (CmpSymbol)
import Prelude.Singletons
import SF.LF.Axiom
import SF.LF.FunExt
import SF.LF.IndProp
import SF.LF.Logic

type TotalMap' (p :: Type ~> Type ~> Type) sym a = p @@ sym @@ a
type TotalMap  a = TotalMap' (TyCon2 (->)) Text   a
type PTotalMap a = TotalMap' (~>@#@$)      Symbol a

tEmpty :: a -> TotalMap a
tEmpty v _ = v

type family TEmpty (v :: a) :: PTotalMap a where
  TEmpty v = ConstSym1 v
$(genDefunSymbols [''TEmpty])

sTEmpty :: forall a (v :: a). Sing v -> Sing (TEmpty v)
sTEmpty sv = singFun1 @(ConstSym1 v) (sConst sv)

beqSymbol :: Text -> Text -> Bool
beqSymbol s1 s2 = (s1 `compare` s2) == EQ

type BeqSymbol s1 s2 = s1 `CmpSymbol` s2 == EQ
$(genDefunSymbols [''BeqSymbol])

sBeqSymbol :: forall (s1 :: Symbol) (s2 :: Symbol).
              Sing s1 -> Sing s2
           -> Sing (s1 `CmpSymbol` s2 == EQ)
sBeqSymbol s1 s2 = (s1 `sCompare` s2) %== SEQ

tUpdate :: TotalMap a -> Text -> a -> Text -> a
tUpdate m x v x' = if (x `compare` x' == EQ) then v else m x'

type family TUpdateAux (m :: PTotalMap a) (x :: Symbol) (v :: a) (x' :: Symbol) :: a where
  TUpdateAux m x v x' = If (BeqSymbol x x') v (m @@ x')
$(genDefunSymbols [''TUpdateAux])
type family TUpdate (m :: PTotalMap a) (x :: Symbol) (v :: a) :: PTotalMap a where
  TUpdate m x v = TUpdateAuxSym3 m x v

sTUpdate :: forall m x v. Sing m -> Sing x -> Sing v -> Sing (TUpdate m x v)
sTUpdate sm sx sv = singFun1 @(TUpdateAuxSym3 m x v) $ \sx' ->
  sIf (sCompare sx sx' %== SEQ)
      sv (sm @@ sx')

$(singletons [d|
  data KV a b = a :-> b
  infixr 0 :->
  |])

(&) :: TotalMap a -> [KV Text a] -> TotalMap a
m & [] = m
m & ((k :-> v) : kvs) = tUpdate m k v & kvs

type family (m :: PTotalMap a) & (l :: [KV Symbol a]) where
  m & '[]               = m
  m & ((k :-> v) : kvs) = TUpdate m k v & kvs
infixl 9 &
$(genDefunSymbols [''(&)])

(%&) :: Sing m -> Sing l -> Sing (m & l)
sm %& SNil = sm
sm %& (SCons (sk :%-> sv) skvs) = sTUpdate sm sk sv %& skvs
infixl 9 %&

tApplyEmpty :: forall a (x :: Symbol) (v :: a).
               TEmpty v @@ x :~: v
tApplyEmpty = Refl

tUpdateEq :: forall a (m :: PTotalMap a) (x :: Symbol) (v :: a).
             m & '[x :-> v] @@ x :~: v
tUpdateEq = Refl

-- Alas, given constraints (Compare s1 s2 ~ EQ) don't imply that (s1 ~ s2), so
-- we have to graft this proof together.
sCompare' :: forall (s1 :: Symbol) (s2 :: Symbol) r.
             Sing s1 -> Sing s2
          -> (s1 :~: s2              -> r)
          -> (CmpSymbol s1 s2 :~: LT -> r)
          -> (CmpSymbol s1 s2 :~: GT -> r)
          -> r
sCompare' s1 s2 eqCase ltCase gtCase =
  case sCompare s1 s2 of
    SLT -> ltCase Refl
    SGT -> gtCase Refl
    SEQ -> eqCase (axiom @s1 @s2)

tUpdateNeq :: forall a (v :: a) (x1 :: Symbol) (x2 :: Symbol) (m :: PTotalMap a).
              Sing x1 -> Sing x2
           -> x1 :/: x2 -> (m & '[x1 :-> v]) @@ x2 :~: m @@ x2
tUpdateNeq sx1 sx2 ne12
  = sCompare' sx1 sx2 (absurd . ne12) (\Refl -> Refl) (\Refl -> Refl)

tUpdateShadow :: forall a (m :: PTotalMap a) (v1 :: a) (v2 :: a) (x :: Symbol).
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

beqSymbolTrueIff :: forall (x :: Symbol) (y :: Symbol).
                    Sing x -> Sing y
                 -> BeqSymbol x y :~: True <-> x :~: y
beqSymbolTrueIff sx sy = (nec, suf)
  where
    nec :: BeqSymbol x y :~: True -> x :~: y
    nec r = sCompare' sx sy id (\Refl -> case r of {}) (\Refl -> case r of {})

    suf :: x :~: y -> BeqSymbol x y :~: True
    suf Refl = Refl

beqSymbolP :: forall (x :: Symbol) (y :: Symbol).
              Sing x -> Sing y
           -> Reflect (x :~: y) (BeqSymbol x y)
beqSymbolP sx sy = iffReflect (sx `sBeqSymbol` sy) $ swap $ beqSymbolTrueIff sx sy

tUpdateSame :: forall a (x :: Symbol) (m :: PTotalMap a).
               Sing x
            -> m & '[x :-> m @@ x] :~: m
tUpdateSame sx1 = funExt go
  where
    go :: forall (x2 :: Symbol). Sing x2
       -> (m & '[x :-> m @@ x]) @@ x2 :~: m @@ x2
    go sx2 = case beqSymbolP sx1 sx2 of
               ReflectT Refl -> Refl
               ReflectF _    -> Refl

tUpdatePermute :: forall a (v1 :: a) (v2 :: a)
                         (x1 :: Symbol) (x2 :: Symbol) (m :: PTotalMap a).
                  Sing x1 -> Sing x2
               -> x2 :/: x1
               -> m & '[x2 :-> v2, x1 :-> v1] :~: m & '[x1 :-> v1, x2 :-> v2]
tUpdatePermute sx1 sx2 ne21 = funExt go
  where
    go :: forall (x3 :: Symbol). Sing x3
       -> (m & '[x2 :-> v2, x1 :-> v1]) @@ x3 :~: (m & '[x1 :-> v1, x2 :-> v2]) @@ x3
    go sx3 = case beqSymbolP sx2 sx3 of
               ReflectF _    -> Refl
               ReflectT Refl ->
                 case beqSymbolP sx1 sx3 of
                   ReflectF _    -> Refl
                   ReflectT Refl -> absurd $ ne21 Refl
