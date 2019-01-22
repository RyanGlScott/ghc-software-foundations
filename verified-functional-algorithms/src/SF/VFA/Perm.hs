{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module SF.VFA.Perm where

import Data.Singletons.Prelude
import Data.Type.Equality
import SF.LF.Logic
import SF.LF.Poly

data Permutation :: forall a. [a] -> [a] -> Prop where
  PermNil   :: Permutation '[] '[]
  PermSkip  :: forall a (x :: a) (l :: [a]) (l' :: [a]).
               Sing x -> Permutation l l' -> Permutation (x:l) (x:l')
  PermSwap  :: forall a (x :: a) (y :: a) (l :: [a]).
               Sing x -> Sing y -> Sing l -> Permutation (y:x:l) (x:y:l)
  PermTrans :: forall a (l :: [a]) (l' :: [a]) (l'' :: [a]).
               Permutation l l' -> Permutation l' l'' -> Permutation l l''

permutationRefl :: forall a (l :: [a]). Sing l -> Permutation l l
permutationRefl SNil           = PermNil
permutationRefl (SCons sx sxs) = PermSkip sx $ permutationRefl sxs

permutationConsAppend :: forall a (l :: [a]) (x :: a).
                         Sing l -> Sing x -> Permutation (x:l) (l ++ '[x])
permutationConsAppend SNil sx = permutationRefl (SCons sx SNil)
permutationConsAppend (SCons sl' sls') sx =
  PermTrans (PermSwap sl' sx sls')
            (PermSkip sl' (permutationConsAppend sls' sx))

permutationAppTail :: forall a (l :: [a]) (l' :: [a]) (tl :: [a]).
                      Sing tl -> Permutation l l' -> Permutation (l ++ tl) (l' ++ tl)
permutationAppTail stl PermNil = permutationRefl stl
permutationAppTail stl (PermSkip sx p) = PermSkip sx $ permutationAppTail stl p
permutationAppTail stl (PermSwap sx sy sl) = PermSwap sx sy (sl %++ stl)
permutationAppTail stl (PermTrans p1 p2) =
  permutationAppTail stl p1 `PermTrans` permutationAppTail stl p2

permutationAppComm :: forall a (l :: [a]) (l' :: [a]).
                      Sing l -> Sing l' -> Permutation (l ++ l') (l' ++ l)
permutationAppComm SNil sl'
  | Refl <- appNilR sl'
  = permutationRefl sl'
permutationAppComm sl@(SCons slx slxs) sl'
  | Refl <- appAssoc sl' (SCons slx SNil) slxs
  =             PermSkip slx (permutationAppComm slxs sl')
    `PermTrans` permutationAppTail slxs (permutationConsAppend sl' slx)
    `PermTrans` permutationRefl (sl' %++ sl)
