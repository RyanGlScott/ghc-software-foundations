{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module SF.LF.Axiom where

import Data.Kind
import Data.Singletons
import Data.Type.Equality
import Unsafe.Coerce

-- | Use with care.
axiom :: a :~: b
axiom = unsafeCoerce Refl

-- | Use with care.
funExt :: forall (a :: Type) (b :: Type)
                 (f :: a ~> b) (g :: a ~> b).
          (forall (x :: a). Sing x -> f @@ x :~: g @@ x)
       -> f :~: g
funExt _ = axiom
