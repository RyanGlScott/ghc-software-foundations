module SF.LF.Axiom where

import Data.Type.Equality
import Unsafe.Coerce

-- | Assert an equality to be true. Ideally, this wouldn't be necessary, but
-- alas, there are certain points in the code where GHC's typechecker isn't
-- quite smart enough to figure certain things out, so this is our escape
-- hatch.
--
-- This can break type safety if wielded improperly. Use with care.
axiom :: forall a b. a :~: b
axiom = unsafeCoerce (Refl @a)
