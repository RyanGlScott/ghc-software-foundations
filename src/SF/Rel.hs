{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.Rel where

import Data.Kind
import Data.Singletons
import Data.Type.Equality
import SF.Logic

type Relation' (p :: Type ~> Type ~> Type) (x :: Type) = p @@ x @@ (p @@ x @@ Prop)
type Relation  x = Relation' (TyCon2 (->)) x
type PRelation x = Relation' (~>@#@$)      x

newtype PartialFunction (r :: PRelation x) =
  MkPartialFunction { runPartialFunction
    :: forall (a :: x) (b1 :: x) (b2 :: x).
       Sing a -> Sing b1 -> Sing b2
    -> r @@ a @@ b1 -> r @@ a @@ b2 -> b1 :~: b2
  }

-- Now we need to get some things from IndProp...

-- TODO RGS
