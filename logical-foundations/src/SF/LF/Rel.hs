{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.Rel where

import Data.Kind
import Data.Nat
import Data.Singletons
import Data.Type.Equality
import SF.LF.IndProp
import SF.LF.Logic

type Relation' (p :: Type ~> Type ~> Type) (x :: Type) = p @@ x @@ (p @@ x @@ Prop)
type Relation  x = Relation' (TyCon2 (->)) x
type PRelation x = Relation' (~>@#@$)      x

newtype PartialFunction (r :: PRelation x) =
  MkPartialFunction { runPartialFunction ::
       forall (a :: x) (b1 :: x) (b2 :: x).
       Sing a -> Sing b1 -> Sing b2
    -> r @@ a @@ b1 -> r @@ a @@ b2 -> b1 :~: b2
  }

totalRelationNotPartial :: Not (PartialFunction (TyCon2 TotalRelation))
totalRelationNotPartial tr
  = case runPartialFunction tr SZ SZ (SS SZ) TR TR of {}

emptyRelationPartial :: PartialFunction (TyCon2 EmptyRelation)
emptyRelationPartial = MkPartialFunction $ \_ _ _ er _ -> case er of {}

newtype Reflexive (r :: PRelation x) =
  MkReflexive { runReflexive :: forall (a :: x). Sing a -> r @@ a @@ a }

newtype Transitive (r :: PRelation x) =
  MkTransitive { runTransitive ::
       forall (a :: x) (b :: x) (c :: x).
       Sing a -> Sing b -> Sing c
    -> (r @@ a @@ b) -> (r @@ b @@ c) -> (r @@ a @@ c)
  }

leReflexive :: Reflexive (TyCon2 Le)
leReflexive = MkReflexive $ const LeN

leTrans' :: Transitive (TyCon2 Le)
leTrans' = MkTransitive $ \_ _ _ -> leTrans

ltTrans', ltTrans'' :: Transitive LtSym0
ltTrans' = MkTransitive go
  where
    go :: forall (a :: Nat) (b :: Nat) (c :: Nat).
          Sing a -> Sing b -> Sing c
       -> Lt a b -> Lt b c -> Lt a c
    go _  _  _  l LeN        = LeS l
    go sa sb sc l (LeS leBC) =
      case sc of
        SS sc' -> LeS $ go sa sb sc' l leBC
ltTrans'' = MkTransitive go
  where
    go :: forall (a :: Nat) (b :: Nat) (c :: Nat).
          Sing a -> Sing b -> Sing c
       -> Lt a b -> Lt b c -> Lt a c
    go _  _  SZ       _    l    = case l of {}
    go sa sb (SS sc') leAB leBC =
      case leBC of
        LeN       -> LeS leAB
        LeS leBC' -> LeS $ go sa sb sc' leAB leBC'

leSN :: forall (n :: Nat) (m :: Nat).
        Sing n -> Sing m
     -> S n <= S m -> n <= m
leSN _  _  LeN        = LeN
leSN sn sm (LeS leMN) =
  case (sn, sm) of
    (SZ,   SZ)     -> LeN
    (SS _, SZ)     -> case leMN of {}
    (_,    SS sm') -> LeS $ leSN sn sm' leMN

leSnLe :: forall (n :: Nat) (m :: Nat).
          Sing n -> Sing m
       -> S n <= S m -> n <= m
leSnLe _ _ LeN = LeN
leSnLe sn sm (LeS le) =
  case (sn, sm) of
    (SZ,   SZ)     -> LeN
    (SS _, SZ)     -> case le of {}
    (_,    SS sm') -> LeS $ leSnLe sn sm' le

leSnN :: forall (n :: Nat). Sing n
      -> Not (S n <= n)
leSnN SZ le = case le of {}
leSnN sn@(SS sn') l@(LeS _) = leSnN sn' (leSnLe sn sn' l)

newtype Symmetric (r :: PRelation x) =
  MkSymmetric { runSymmetric ::
       forall (a :: x) (b :: x).
       Sing a -> Sing b
    -> (r @@ a @@ b) -> (r @@ b @@ a)
  }

leNotSymmetric :: Not (Symmetric (TyCon2 Le))
leNotSymmetric s = case runSymmetric s SZ (SS SZ) (LeS LeN) of

newtype Antisymmetric (r :: PRelation x) =
  MkAntisymmetric { runAntisymmetric ::
       forall (a :: x) (b :: x).
       Sing a -> Sing b
    -> (r @@ a @@ b) -> (r @@ b @@ a)
    -> a :~: b
  }

leAntisymmetric :: Antisymmetric (TyCon2 Le)
leAntisymmetric = MkAntisymmetric go
  where
    go :: forall (a :: Nat) (b :: Nat).
          Sing a -> Sing b
       -> Le a b -> Le b a
       -> a :~: b
    go _ SZ     LeN LeN = Refl
    go _ (SS _) _   LeN = Refl
    go _ (SS _) LeN (LeS _) = Refl
    go sa@(SS sa') sb@(SS sb') (LeS leAB') (LeS leBA')
      | Refl <- go sa' sb' (runTransitive leTrans' sa' sa sb' (LeS LeN) leAB')
                           (runTransitive leTrans' sb' sb sa' (LeS LeN) leBA')
      = Refl

leStep :: forall (n :: Nat) (m :: Nat) (p :: Nat).
          Sing n -> Sing m -> Sing p
       -> n < m
       -> m <= S p
       -> n <= p
leStep sn sm sp LeN leSnSp =
  case sm of
    SS _ -> leSN sn sp leSnSp
leStep sn (SS sm') sp (LeS leNM') leMSP =
  leStep sn sm' sp leNM' (leTrans (LeS LeN) leMSP)

type Equivalence (r :: PRelation x) =
  Reflexive r /\ Symmetric r /\ Transitive r
type Order (r :: PRelation x) =
  Reflexive r /\ Antisymmetric r /\ Transitive r
type Preorder (r :: PRelation x) =
  Reflexive r /\ Transitive r

data ClosReflTrans :: forall (a :: Type). PRelation a -> a -> a -> Prop where
  RTStep  :: r @@ x @@ y -> ClosReflTrans r x y
  RTRefl  :: ClosReflTrans r x x
  RTTrans :: ClosReflTrans r x y
          -> ClosReflTrans r y z
          -> ClosReflTrans r x z

data ClosReflTrans1n :: forall (a :: Type). PRelation a -> a -> a -> Prop where
  RT1nRefl  :: ClosReflTrans1n r x x
  RT1nTrans :: r @@ x @@ y -> ClosReflTrans1n r y z
            -> ClosReflTrans1n r x z

rscR :: forall (a :: Type) (r :: PRelation a) (x :: a) (y :: a).
        r @@ x @@ y -> ClosReflTrans1n r x y
rscR = flip RT1nTrans RT1nRefl

rscTrans :: forall (a :: Type) (r :: PRelation a) (x :: a) (y :: a) (z :: a).
            ClosReflTrans1n r x y
         -> ClosReflTrans1n r y z
         -> ClosReflTrans1n r x z
rscTrans RT1nRefl             crxz = crxz
rscTrans (RT1nTrans rxw crwy) cryz = RT1nTrans rxw (rscTrans crwy cryz)

rtcRscCoincide :: forall (a :: Type) (r :: PRelation a) (x :: a) (y :: a).
                  ClosReflTrans r x y <-> ClosReflTrans1n r x y
rtcRscCoincide = (nec, suf)
  where
    nec :: forall (xx :: a) (yy :: a).
           ClosReflTrans r xx yy -> ClosReflTrans1n r xx yy
    nec (RTStep rxy)        = rscR rxy
    nec RTRefl              = RT1nRefl
    nec (RTTrans crxy cryz) = rscTrans (nec crxy) (nec cryz)

    suf :: forall (xx :: a) (yy :: a).
           ClosReflTrans1n r xx yy -> ClosReflTrans r xx yy
    suf RT1nRefl             = RTRefl
    suf (RT1nTrans rxw crwy) = RTTrans (RTStep rxw) (suf crwy)
