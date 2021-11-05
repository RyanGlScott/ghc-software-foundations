{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.FunExt where

import Data.Singletons.Base.TH
import SF.LF.Axiom

-- | A witness to the principle of function extensionality; that is, two
-- (partially applied) functions are equal if their results are equal
-- when applied to every possible argument.
--
-- This is a strange version of function extensionality that works over
-- defunctionalization symbols. In a strict sense, every defunctionalization
-- symbol is a distinct type, but we can be fast-and-loose and say things
-- like @Id1 :~: Id2@ as long as @Id1 x :~: Id2 x@ for all @x@.
funExt :: forall a b (f :: a ~> b) (g :: a ~> b).
          (forall (x :: a). Sing x
                         -> f @@ x :~: g @@ x)
       -> f :~: g
funExt _ = axiom

type family FunExt2Aux (f :: a1 ~> a2 ~> b) (x :: (a1, a2)) :: b where
  FunExt2Aux f '(x1, x2) = f @@ x1 @@ x2
$(genDefunSymbols [''FunExt2Aux])

-- | A variant of 'funExt' that works on functions with two arguments.
funExt2 :: forall a1 a2 b (f :: a1 ~> a2 ~> b) (g :: a1 ~> a2 ~> b).
           (forall (x1 :: a1) (x2 :: a2). Sing x1 -> Sing x2
                                       -> f @@ x1 @@ x2 :~: g @@ x1 @@ x2)
        -> f :~: g
funExt2 fun
  | Refl <- funExt @(a1, a2) @b @(FunExt2AuxSym1 f) @(FunExt2AuxSym1 g) fun'
  = Refl
  where
    fun' :: forall (x :: (a1, a2)). Sing x
         -> FunExt2AuxSym1 f @@ x :~: FunExt2AuxSym1 g @@ x
    fun' (STuple2 sx1 sx2) = fun sx1 sx2

type family FunExt3Aux (f :: a1 ~> a2 ~> a3 ~> b) (x :: (a1, a2, a3)) :: b where
  FunExt3Aux f '(x1, x2, x3) = f @@ x1 @@ x2 @@ x3
$(genDefunSymbols [''FunExt3Aux])

-- | A variant of 'funExt' that works on functions with three arguments.
funExt3 :: forall a1 a2 a3 b (f :: a1 ~> a2 ~> a3 ~> b) (g :: a1 ~> a2 ~> a3 ~> b).
           (forall (x1 :: a1) (x2 :: a2) (x3 :: a3). Sing x1 -> Sing x2 -> Sing x3
                                                  -> f @@ x1 @@ x2 @@ x3 :~: g @@ x1 @@ x2 @@ x3)
        -> f :~: g
funExt3 fun
  | Refl <- funExt @(a1, a2, a3) @b @(FunExt3AuxSym1 f) @(FunExt3AuxSym1 g) fun'
  = Refl
  where
    fun' :: forall (x :: (a1, a2, a3)). Sing x
         -> FunExt3AuxSym1 f @@ x :~: FunExt3AuxSym1 g @@ x
    fun' (STuple3 sx1 sx2 sx3) = fun sx1 sx2 sx3

-- | 'Apply' an equality between functions to an equality between arguments.
--
-- This can be useful in combination with 'funExt'. For example:
--
-- @
-- Refl \@Proxy
--   `apply` funExt \@Int \@Int
--                  \@Id1Sym0 \@Id2Sym0
--                  (const Refl)
--   :: Proxy Id1Sym0 :~: Proxy Id2Sym0
-- @
apply :: f :~: g -> a :~: b -> Apply f a :~: Apply g b
apply Refl Refl = Refl
{-# NOINLINE apply #-} -- #16310
