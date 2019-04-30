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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.LF.ImpC where

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
import Prelude hiding (Eq(..), Ord(..))
import SF.LF.Basics
import SF.LF.Maps

data AExp' sym
  = ANum Nat
  | AId sym
  | APlus  (AExp' sym) (AExp' sym)
  | AMinus (AExp' sym) (AExp' sym)
  | AMult  (AExp' sym) (AExp' sym)
type DAExp = AExp' Text
type AExp  = AExp' Symbol
data SAExp :: AExp -> Type where
  SANum   :: Sing n -> SAExp (ANum n)
  SAId    :: Sing s -> SAExp (AId s)
  SAPlus  :: Sing a1 -> Sing a2 -> SAExp (APlus a1 a2)
  SAMinus :: Sing a1 -> Sing a2 -> SAExp (AMinus a1 a2)
  SAMult  :: Sing a1 -> Sing a2 -> SAExp (AMult a1 a2)
type instance Sing = SAExp

data BExp' sym
  = BTrue
  | BFalse
  | BEq  (AExp' sym) (AExp' sym)
  | BLe  (AExp' sym) (AExp' sym)
  | BNot (BExp' sym)
  | BAnd (BExp' sym) (BExp' sym)
type DBExp = BExp' Text
type BExp  = BExp' Symbol
data SBExp :: BExp -> Type where
  SBTrue  :: SBExp BTrue
  SBFalse :: SBExp BFalse
  SBEq    :: Sing a1 -> Sing a2 -> SBExp (BEq a1 a2)
  SBLe    :: Sing a1 -> Sing a2 -> SBExp (BLe a1 a2)
  SBNot   :: Sing b1 -> SBExp (BNot b1)
  SBAnd   :: Sing b1 -> Sing b2 -> SBExp (BAnd b1 b2)
type instance Sing = SBExp

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
