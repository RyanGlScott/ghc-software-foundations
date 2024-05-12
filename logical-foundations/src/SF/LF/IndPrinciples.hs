{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.IndPrinciples where

import Data.Eliminator
import Data.Eliminator.TH
import Data.Kind
import Data.Nat
import Data.Singletons.TH
import Prelude.Singletons
import SF.LF.Logic

type PlusOneR'Aux (n :: Nat) = n + Lit 1 :~: S n
$(genDefunSymbols [''PlusOneR'Aux])

plusOneR' :: forall (n :: Nat). Sing n
          -> n + Lit 1 :~: S n
plusOneR' sn = elimNat @PlusOneR'AuxSym0 sn base step
  where
    base :: Z + Lit 1 :~: S Z
    base = Refl

    step :: forall (n' :: Nat). Sing n'
         ->   n' + Lit 1 :~: S n'
         -> S n' + Lit 1 :~: S (S n')
    step _ Refl = Refl

$(singletons [d| data YesNo = Yes | No |])
$(deriveElim     ''YesNo)
$(deriveTypeElim ''YesNo)

$(singletons [d| data RGB = Red | Green | Blue |])
$(deriveElim     ''RGB)
$(deriveTypeElim ''RGB)

$(singletons [d| data NatList1 = NNil1 | NSnoc1 NatList1 Nat |])
$(deriveElim ''NatList1)

$(singletons [d| data BynTree = BEmpty | BLeaf YesNo | NBranch YesNo BynTree BynTree |])
$(deriveElim ''BynTree)

$(singletons [d| data ExSet = Con1 Bool | Con2 Nat ExSet |])
$(deriveElim     ''ExSet)
$(deriveTypeElim ''ExSet)

$(singletons [d| data Tree x = Leaf x | Node (Tree x) (Tree x) |])
$(deriveElim ''Tree)

$(singletons [d| data MyType x = Constr1 x | Constr2 Nat | Constr3 (MyType x) Nat |])
$(deriveElim ''MyType)

data Foo_ (p :: Type ~> Type ~> Type) x y
  = Bar x
  | Baz y
  | Quux (p @@ Nat @@ Foo_ p x y)
type Foo  = Foo_ (TyCon2 (->))
type PFoo = Foo_ (~>@#@$)
data SFoo :: forall a b. PFoo a b -> Type where
  SBar  :: Sing x -> SFoo (Bar x)
  SBaz  :: Sing y -> SFoo (Baz y)
  SQuux :: Sing f -> SFoo (Quux f)
type instance Sing = SFoo
fooInd :: forall x y (p :: PFoo x y ~> Prop) (f :: PFoo x y).
          Sing f
       -> (forall (xx :: x). Sing xx -> p @@ Bar xx)
       -> (forall (yy :: y). Sing yy -> p @@ Baz yy)
       -> (forall (f1 :: Nat ~> PFoo x y).
               Sing f1
            -> (forall (n :: Nat). Sing n -> p @@ (f1 @@ n))
            -> p @@ Quux f1)
       -> p @@ f
fooInd (SBar sx)  pBar _    _ = pBar sx
fooInd (SBaz sy)  _    pBaz _ = pBaz sy
fooInd (SQuux (sf :: Sing f1)) pBar pBaz pQuux =
  pQuux sf $ \(sn :: Sing n) -> fooInd @x @y @p @(f1 @@ n) (sf @@ sn) pBar pBaz pQuux

$(singletons [d| data Foo' x = C1 [x] (Foo' x) | C2 (Foo' x) |])
$(deriveElim     ''Foo')
$(deriveTypeElim ''Foo')

type PlusAssoc'Aux (m :: Nat) (p :: Nat) (n :: Nat) = n + (m + p) :~: (n + m) + p
$(genDefunSymbols [''PlusAssoc'Aux])

plusAssoc' :: forall (n :: Nat) (m :: Nat) (p :: Nat).
              Sing n -> Sing m -> Sing p
           -> n + (m + p) :~: (n + m) + p
plusAssoc' sn _ _ = elimNat @(PlusAssoc'AuxSym2 m p) sn base step
  where
    base :: Z + (m + p) :~: (Z + m) + p
    base = Refl

    step :: forall (n' :: Nat). Sing n'
         ->   n' + (m + p) :~:   (n' + m) + p
         -> S n' + (m + p) :~: (S n' + m) + p
    step _ Refl = Refl

type Plus0RAux (n :: Nat) = n + Z :~: n
$(genDefunSymbols [''Plus0RAux])

plus0R :: forall (n :: Nat). Sing n
       -> n + Z :~: n
plus0R sn = elimNat @Plus0RAuxSym0 sn base step
  where
    base :: Z + Z :~: Z
    base = Refl

    step :: forall (n' :: Nat). Sing n'
         ->   n' + Z :~:   n'
         -> S n' + Z :~: S n'
    step _ Refl = Refl

type PlusSRAux (m :: Nat) (n :: Nat) = S (n + m) :~: n + S m
$(genDefunSymbols [''PlusSRAux])

plusSR :: forall (n :: Nat) (m :: Nat).
          Sing n -> Sing m
       -> S (n + m) :~: n + S m
plusSR sn _ = elimNat @(PlusSRAuxSym1 m) sn base step
  where
    base :: S (Z + m) :~: Z + S m
    base = Refl

    step :: forall (n' :: Nat). Sing n'
         -> S   (n' + m) :~:   n' + S m
         -> S (S n' + m) :~: S n' + S m
    step _ Refl = Refl

type PlusComm'Aux (m :: Nat) (n :: Nat) = n + m :~: m + n
$(genDefunSymbols [''PlusComm'Aux])

plusComm' :: forall (n :: Nat) (m :: Nat).
             Sing n -> Sing m
          -> n + m :~: m + n
plusComm' sn sm = elimNat @(PlusComm'AuxSym1 m) sn base step
  where
    base :: Z + m :~: m + Z
    base | Refl <- plus0R sm = Refl

    step :: forall (n' :: Nat). Sing n'
         ->   n' + m :~: m +   n'
         -> S n' + m :~: m + S n'
    step sn' Refl = plusSR sm sn'
