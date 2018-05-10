{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.Imp where

import Data.Nat
import Data.Singletons.Prelude
import Data.Singletons.TH
import SF.Basics
import SF.Logic hiding (Not, NotSym0)

$(singletons [d|
  data AExp
    = ANum Nat
    | APlus AExp AExp
    | AMinus AExp AExp
    | AMult AExp AExp

  data BExp
    = BTrue
    | BFalse
    | BEq AExp AExp
    | BLe AExp AExp
    | BNot BExp
    | BAnd BExp BExp
  |])

$(singletons [d|
  aEval :: AExp -> Nat
  aEval (ANum n)       = n
  aEval (APlus  a1 a2) = aEval a1 + aEval a2
  aEval (AMinus a1 a2) = aEval a1 - aEval a2
  aEval (AMult  a1 a2) = aEval a1 * aEval a2

  bEval :: BExp -> Bool
  bEval BTrue        = True
  bEval BFalse       = False
  bEval (BEq a1 a2)  = aEval a1 == aEval a2
  bEval (BLe a1 a2)  = leb (aEval a1) (aEval a2)
  bEval (BNot b1)    = not (bEval b1)
  bEval (BAnd b1 b2) = bEval b1 && bEval b2

  optimize0Plus :: AExp -> AExp
  optimize0Plus (ANum n)      = ANum n
  optimize0Plus (APlus e1 e2) =
    let def = APlus (optimize0Plus e1) (optimize0Plus e2)
    in case e1 of
         ANum Z     -> optimize0Plus e2
         ANum (S _) -> def
         APlus{}    -> def
         AMinus{}   -> def
         AMult{}    -> def
  optimize0Plus (AMinus e1 e2) = AMinus (optimize0Plus e1) (optimize0Plus e2)
  optimize0Plus (AMult  e1 e2) = AMult  (optimize0Plus e1) (optimize0Plus e2)
  |])

optimize0PlusSound :: forall (a :: AExp). Sing a
                   -> AEval (Optimize0Plus a) :~: AEval a
optimize0PlusSound SANum{} = Refl
optimize0PlusSound (SAPlus sa1 sa2)
  = case sa1 of
      SANum SZ   | Refl         <- sound2  -> Refl
      SANum SS{} | Refl         <- sound2  -> Refl
      SAPlus{}   | (Refl, Refl) <- sound12 -> Refl
      SAMinus{}  | (Refl, Refl) <- sound12 -> Refl
      SAMult{}   | (Refl, Refl) <- sound12 -> Refl
  where
    sound2  = optimize0PlusSound sa2
    sound12 = (optimize0PlusSound sa1, sound2)
optimize0PlusSound (SAMinus sa1 sa2)
  | Refl <- optimize0PlusSound sa1
  , Refl <- optimize0PlusSound sa2
  = Refl
optimize0PlusSound (SAMult sa1 sa2)
  | Refl <- optimize0PlusSound sa1
  , Refl <- optimize0PlusSound sa2
  = Refl

$(singletons [d|
  optimize0PlusB :: BExp -> BExp
  optimize0PlusB BTrue        = BTrue
  optimize0PlusB BFalse       = BFalse
  optimize0PlusB (BEq a1 a2)  = BEq (optimize0Plus a1) (optimize0Plus a2)
  optimize0PlusB (BLe a1 a2)  = BLe (optimize0Plus a1) (optimize0Plus a2)
  optimize0PlusB (BNot b1)    = BNot (optimize0PlusB b1)
  optimize0PlusB (BAnd b1 b2) = BAnd (optimize0PlusB b1) (optimize0PlusB b2)
  |])

optimize0PlusBSound :: forall (b :: BExp). Sing b
                    -> BEval (Optimize0PlusB b) :~: BEval b
optimize0PlusBSound SBTrue  = Refl
optimize0PlusBSound SBFalse = Refl
optimize0PlusBSound (SBEq sa1 sa2)
  | Refl <- optimize0PlusSound sa1
  , Refl <- optimize0PlusSound sa2
  = Refl
optimize0PlusBSound (SBLe sa1 sa2)
  | Refl <- optimize0PlusSound sa1
  , Refl <- optimize0PlusSound sa2
  = Refl
optimize0PlusBSound (SBNot sb1)
  | Refl <- optimize0PlusBSound sb1
  = Refl
optimize0PlusBSound (SBAnd sb1 sb2)
  | Refl <- optimize0PlusBSound sb1
  , Refl <- optimize0PlusBSound sb2
  = Refl

data AEvalR :: AExp -> Nat -> Prop where
  EANum   :: ANum n \\ n
  EAPlus  :: Sing a1 -> Sing a2
          -> a1 \\ n1
          -> a2 \\ n2
          -> APlus a1 a2 \\ n1 + n2
  EAMinus :: Sing a1 -> Sing a2
          -> a1 \\ n1
          -> a2 \\ n2
          -> AMinus a1 a2 \\ n1 - n2
  EAMult  :: Sing a1 -> Sing a2
          -> a1 \\ n1
          -> a2 \\ n2
          -> AMult a1 a2 \\ n1 * n2

type (\\) = AEvalR
infix 5 \\
$(genDefunSymbols [''(\\)])

aEvalIffAEvalR :: forall (a :: AExp) (n :: Nat).
                  Sing a
               -> (a \\ n) <-> AEval a :~: n
aEvalIffAEvalR sa = (nec, suf sa)
  where
    nec :: forall (aa :: AExp) (nn :: Nat).
           (aa \\ nn) -> AEval aa :~: nn
    nec EANum = Refl
    nec (EAPlus _ _ ea1 ea2)
      | Refl <- nec ea1
      , Refl <- nec ea2
      = Refl
    nec (EAMinus _ _ ea1 ea2)
      | Refl <- nec ea1
      , Refl <- nec ea2
      = Refl
    nec (EAMult _ _ ea1 ea2)
      | Refl <- nec ea1
      , Refl <- nec ea2
      = Refl

    suf :: forall (aa :: AExp) (nn :: Nat). Sing aa
        -> AEval aa :~: nn -> (aa \\ nn)
    suf SANum{} Refl = EANum
    suf (SAPlus sa1 sa2) Refl
      = EAPlus sa1 sa2 (suf sa1 Refl) (suf sa2 Refl)
    suf (SAMinus sa1 sa2) Refl
      = EAMinus sa1 sa2 (suf sa1 Refl) (suf sa2 Refl)
    suf (SAMult sa1 sa2) Refl
      = EAMult sa1 sa2 (suf sa1 Refl) (suf sa2 Refl)

data BEvalR :: BExp -> Bool -> Prop where
  EBTrue  :: BEvalR BTrue  True
  EBFalse :: BEvalR BFalse False
  EBEq    :: Sing a1 -> Sing a2
          -> AEvalR a1 n1
          -> AEvalR a2 n2
          -> BEvalR (BEq a1 a2) (n1 == n2)
  EBLe    :: Sing a1 -> Sing a2
          -> AEvalR a1 n1
          -> AEvalR a2 n2
          -> BEvalR (BLe a1 a2) (Leb n1 n2)
  EBNot   :: Sing b1
          -> BEvalR b1 bv1
          -> BEvalR (BNot b1) (Not bv1)
  EBAnd   :: Sing b1 -> Sing b2
          -> BEvalR b1 bv1
          -> BEvalR b2 bv2
          -> BEvalR (BAnd b1 b2) (bv1 && bv2)

bEvalIffBEvalR :: forall (b :: BExp) (bv :: Bool).
                  Sing b
               -> BEvalR b bv <-> BEval b :~: bv
bEvalIffBEvalR sb = (nec, suf sb)
  where
    nec :: forall (bb :: BExp) (bbv :: Bool).
           BEvalR bb bbv -> BEval bb :~: bbv
    nec EBTrue  = Refl
    nec EBFalse = Refl
    nec (EBEq sa1 sa2 ae1 ae2)
      | Refl <- fst (aEvalIffAEvalR sa1) ae1
      , Refl <- fst (aEvalIffAEvalR sa2) ae2
      = Refl
    nec (EBLe sa1 sa2 ae1 ae2)
      | Refl <- fst (aEvalIffAEvalR sa1) ae1
      , Refl <- fst (aEvalIffAEvalR sa2) ae2
      = Refl
    nec (EBNot _ be1)
      | Refl <- nec be1
      = Refl
    nec (EBAnd _ _ be1 be2)
      | Refl <- nec be1
      , Refl <- nec be2
      = Refl

    suf :: forall (bb :: BExp) (bbv :: Bool). Sing bb
        -> BEval bb :~: bbv -> BEvalR bb bbv
    suf SBTrue  Refl = EBTrue
    suf SBFalse Refl = EBFalse
    suf (SBEq sa1 sa2) Refl
      = EBEq sa1 sa2
             (snd (aEvalIffAEvalR sa1) Refl)
             (snd (aEvalIffAEvalR sa2) Refl)
    suf (SBLe sa1 sa2) Refl
      = EBLe sa1 sa2
             (snd (aEvalIffAEvalR sa1) Refl)
             (snd (aEvalIffAEvalR sa2) Refl)
    suf (SBNot sb1) Refl
      = EBNot sb1 (suf sb1 Refl)
    suf (SBAnd sb1 sb2) Refl
      = EBAnd sb1 sb2 (suf sb1 Refl) (suf sb2 Refl)
