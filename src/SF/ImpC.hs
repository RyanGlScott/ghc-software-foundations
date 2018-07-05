{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.ImpC where

import Data.Kind (Type)
import Data.Nat
import Data.Singletons.Prelude
  hiding ( PEq(..), SEq(..), POrd(..), SOrd(..), type (&&), (%&&)
         , type (==@#@$), type (==@#@$$), type (==@#@$$$)
         , type (&&@#@$), type (&&@#@$$), type (&&@#@$$$)
         , type (<=@#@$), type (<=@#@$$), type (<=@#@$$$)
         )
import Data.Singletons.Prelude.IsString
import Data.Singletons.TH (genDefunSymbols, singletonsOnly)
import Data.String (IsString(..))
import Data.Text (Text)
import Data.Type.Equality ((:~:)(..))
import GHC.TypeLits (Symbol)
import Prelude hiding (Eq(..), Ord(..))
import SF.Basics
import SF.Maps

data AExp' (sym :: Type)
  = ANum Nat
  | AId sym
  | APlus  (AExp' sym) (AExp' sym)
  | AMinus (AExp' sym) (AExp' sym)
  | AMult  (AExp' sym) (AExp' sym)
type DAExp = AExp' Text
type AExp  = AExp' Symbol
data instance Sing :: AExp -> Type where
  SANum   :: Sing n -> Sing (ANum n :: AExp)
  SAId    :: Sing s -> Sing (AId s :: AExp)
  SAPlus  :: Sing a1 -> Sing a2 -> Sing (APlus a1 a2 :: AExp)
  SAMinus :: Sing a1 -> Sing a2 -> Sing (AMinus a1 a2 :: AExp)
  SAMult  :: Sing a1 -> Sing a2 -> Sing (AMult a1 a2 :: AExp)

data BExp' (sym :: Type)
  = BTrue
  | BFalse
  | BEq  (AExp' sym) (AExp' sym)
  | BLe  (AExp' sym) (AExp' sym)
  | BNot (BExp' sym)
  | BAnd (BExp' sym) (BExp' sym)
type DBExp = BExp' Text
type BExp  = BExp' Symbol
data instance Sing :: BExp -> Type where
  SBTrue  :: Sing (BTrue  :: BExp)
  SBFalse :: Sing (BFalse :: BExp)
  SBEq    :: Sing a1 -> Sing a2 -> Sing (BEq a1 a2 :: BExp)
  SBLe    :: Sing a1 -> Sing a2 -> Sing (BLe a1 a2 :: BExp)
  SBNot   :: Sing b1 -> Sing (BNot b1 :: BExp)
  SBAnd   :: Sing b1 -> Sing b2 -> Sing (BAnd b1 b2 :: BExp)

$(genDefunSymbols [''AExp', ''BExp'])

$(singletonsOnly [d|
  instance IsString AExp where
    fromString = AId
  instance Num AExp where
    (+) = APlus
    (-) = AMinus
    (*) = AMult
    fromInteger = ANum . fromInteger
    abs = undefined
    signum = undefined

  (<=), (==) :: AExp -> AExp -> BExp
  (<=) = BLe
  (==) = BEq
  infix 4 <=, ==

  (&&) :: BExp -> BExp -> BExp
  (&&) = BAnd
  infixr 3 &&
  |])

$(singletonsOnly [d|
  ex1 :: AExp
  ex1 = 3 + ("X" * 2)

  ex2 :: BExp
  ex2 = BTrue && BNot ("X" <= 4) -- Eh, close enough
  |])

type State = Symbol -> Nat

$(singletonsOnly [d|
  st0 :: State
  st0 = tEmpty 0

  aEval :: State -> AExp -> Nat
  aEval _  (ANum n)       = n
  aEval st (AId x)        = st x
  aEval st (APlus  a1 a2) = aEval st a1 + aEval st a2
  aEval st (AMinus a1 a2) = aEval st a1 - aEval st a2
  aEval st (AMult  a1 a2) = aEval st a1 * aEval st a2

  bEval :: State -> BExp -> Bool
  bEval _  BTrue        = True
  bEval _  BFalse       = False
  bEval st (BEq a1 a2)  = beqNat (aEval st a1) (aEval st a2)
  bEval st (BLe a1 a2)  = leb (aEval st a1) (aEval st a2)
  bEval st (BNot b1)    = negb (bEval st b1)
  bEval st (BAnd b1 b2) = andb (bEval st b1) (bEval st b2)
  |])

$(singletonsOnly [d|
  aEvalExp1 :: Nat
  aEvalExp1 = aEval (st0 & ["X" :-> 5]) ex1

  bEvalExp1 :: Bool
  bEvalExp1 = bEval (st0 & ["X" :-> 5]) ex2
  |])

aEvalTest1 :: AEvalExp1 :~: Lit 13
aEvalTest1 = Refl

bEvalTest1 :: BEvalExp1 :~: True
bEvalTest1 = Refl

-- TODO RGS
