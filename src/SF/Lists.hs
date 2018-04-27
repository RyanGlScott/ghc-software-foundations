{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module SF.Lists where

import Data.Nat
import Data.Singletons.Prelude hiding (Id, IdSym0, IdSym1)
import Data.Singletons.Prelude.Tuple
import Data.Singletons.TH
import SF.Basics
import SF.Induction

type NatProd = (Nat, Nat)

sndFstIsSwap :: forall (p :: NatProd). Sing p
             -> '(Snd p, Fst p) :~: Swap p
sndFstIsSwap (STuple2 {}) = Refl

fstSwapIsSnd :: forall (p :: NatProd). Sing p
             -> Fst (Swap p) :~: Snd p
fstSwapIsSnd (STuple2 {}) = Refl

type NatList = [Nat]

$(singletons [d|
  nonzeros :: NatList -> NatList
  nonzeros [] = []
  nonzeros (x:xs)
    = let xs' = nonzeros xs
      in case x of
           Z -> xs'
           S _ -> x:xs'
    {-
    = if x == Z
      then nonzeros xs
      else x:nonzeros xs
    -}
  |])

testNonzeroes :: Nonzeros (Map LitSym0 '[0,1,0,2,3,0,0]) :~: Map LitSym0 '[1,2,3]
testNonzeroes = Refl

$(singletons [d|
  oddmembers :: NatList -> NatList
  oddmembers [] = []
  oddmembers (x:xs)
    = let xs' = oddmembers xs
      in if odd' x
         then x:xs'
         else xs'

  odd' :: Nat -> Bool
  odd' = not . evenb
  |])

testOddmembers :: Oddmembers (Map LitSym0 '[0,1,0,2,3,0,0]) :~: Map LitSym0 '[1,3]
testOddmembers = Refl

$(singletons [d|
  countoddmembers :: NatList -> Nat
  countoddmembers [] = 0
  countoddmembers (x:xs)
    = let count = countoddmembers xs
      in if odd' x
         then S count
         else count
  |])

testCountoddmembers1 :: Countoddmembers (Map LitSym0 '[1,0,3,1,4,5]) :~: Lit 4
testCountoddmembers1 = Refl

testCountoddmembers2 :: Countoddmembers (Map LitSym0 '[0,2,4]) :~: Lit 0
testCountoddmembers2 = Refl

testCountoddmembers3 :: Countoddmembers (Map LitSym0 '[]) :~: Lit 0
testCountoddmembers3 = Refl

$(singletons [d|
  alternate :: NatList -> NatList -> NatList
  alternate (x:xs) (y:ys) = x:y:alternate xs ys
  alternate xs     []     = xs
  alternate []     ys     = ys
  |])

testAlternate1 :: Alternate (Map LitSym0 '[1,2,3]) (Map LitSym0 '[4,5,6])
                        :~: Map LitSym0 '[1,4,2,5,3,6]
testAlternate1 = Refl

testAlternate2 :: Alternate (Map LitSym0 '[1]) (Map LitSym0 '[4,5,6])
                        :~: Map LitSym0 '[1,4,5,6]
testAlternate2 = Refl

testAlternate3 :: Alternate (Map LitSym0 '[1,2,3]) (Map LitSym0 '[4])
                        :~: Map LitSym0 '[1,4,2,3]
testAlternate3 = Refl

testAlternate4 :: Alternate (Map LitSym0 '[]) (Map LitSym0 '[20,30])
                        :~: Map LitSym0 '[20,30]
testAlternate4 = Refl

type Bag = NatList

$(singletons [d|
  count :: Nat -> Bag -> Nat
  count _ [] = Z
  count v (x:xs)
    = let count' = count v xs
      in if v == x
         then 1 + count'
         else count'
  |])

testCount1 :: Count (Lit 1) (Map LitSym0 '[1,2,3,1,4,1]) :~: Lit 3
testCount1 = Refl

testCount2 :: Count (Lit 6) (Map LitSym0 '[1,2,3,1,4,1]) :~: Lit 0
testCount2 = Refl

$(singletons [d|
  removeOne :: Nat -> Bag -> Bag
  removeOne _ [] = []
  removeOne v (x:xs)
    = if v == x
      then xs
      else x:removeOne v xs
  |])

testRemove1 :: Count (Lit 5) (RemoveOne (Lit 5) (Map LitSym0 '[2,1,5,4,1])) :~: Lit 0
testRemove1 = Refl

testRemove2 :: Count (Lit 5) (RemoveOne (Lit 5) (Map LitSym0 '[2,1,4,1])) :~: Lit 0
testRemove2 = Refl

testRemove3 :: Count (Lit 4) (RemoveOne (Lit 5) (Map LitSym0 '[2,1,4,5,1,4])) :~: Lit 2
testRemove3 = Refl

testRemove4 :: Count (Lit 5) (RemoveOne (Lit 5) (Map LitSym0 '[2,1,5,4,5,1,4])) :~: Lit 1
testRemove4 = Refl

$(singletons [d|
  removeAll :: Nat -> Bag -> Bag
  removeAll _ [] = []
  removeAll v (x:xs)
    = let xs' = removeAll v xs
      in if v == x
         then xs'
         else x:xs'
  |])

testRemoveAll1 :: Count (Lit 5) (RemoveAll (Lit 5) (Map LitSym0 '[2,1,5,4,1])) :~: Lit 0
testRemoveAll1 = Refl

testRemoveAll2 :: Count (Lit 5) (RemoveAll (Lit 5) (Map LitSym0 '[2,1,4,1])) :~: Lit 0
testRemoveAll2 = Refl

testRemoveAll3 :: Count (Lit 4) (RemoveAll (Lit 5) (Map LitSym0 '[2,1,4,5,1,4])) :~: Lit 2
testRemoveAll3 = Refl

testRemoveAll4 :: Count (Lit 5) (RemoveAll (Lit 5) (Map LitSym0 '[2,1,5,4,5,1,4,5,1,4])) :~: Lit 0
testRemoveAll4 = Refl

$(singletons [d|
  subset :: Bag -> Bag -> Bool
  subset [] _ = True
  subset (x:xs) ys
    = if x `elem` ys
      then subset xs (removeOne x ys)
      else False
  |])

testSubset1 :: Subset (Map LitSym0 '[1,2]) (Map LitSym0 '[2,1,4,1]) :~: True
testSubset1 = Refl

testSubset2 :: Subset (Map LitSym0 '[1,2,2]) (Map LitSym0 '[2,1,4,1]) :~: False
testSubset2 = Refl

$(singletons [d|
  rev :: NatList -> NatList
  rev [] = []
  rev (h:t) = rev t ++ [h]
  |])

appNilR :: forall (l :: NatList).
           Sing l -> l ++ '[] :~: l
appNilR SNil = Refl
appNilR (SCons _ sxs) | Refl <- appNilR sxs = Refl

appAssoc :: forall (l1 :: NatList) (l2 :: NatList) (l3 :: NatList).
            Sing l1 -> Sing l2 -> Sing l3
         -> (l1 ++ l2) ++ l3 :~: l1 ++ (l2 ++ l3)
appAssoc SNil _ _ = Refl
appAssoc (SCons _ sls1) l2 l3 | Refl <- appAssoc sls1 l2 l3 = Refl

revAppDistr :: forall (l1 :: NatList) (l2 :: NatList).
               Sing l1 -> Sing l2
            -> Rev (l1 ++ l2) :~: Rev l2 ++ Rev l1
revAppDistr SNil l2 | Refl <- appNilR (sRev l2) = Refl
revAppDistr (SCons sl1 sls1) l2 | Refl <- revAppDistr sls1 l2
                                , Refl <- appAssoc (sRev l2) (sRev sls1) (SCons sl1 SNil)
                                = Refl

revInvolutive :: forall (l :: NatList).
                 Sing l -> Rev (Rev l) :~: l
revInvolutive SNil = Refl
revInvolutive (SCons sl sls) | Refl <- revInvolutive sls
                             , Refl <- revAppDistr (sRev sls) (SCons sl SNil)
                             = Refl

appAssoc4 :: forall (l1 :: NatList) (l2 :: NatList) (l3 :: NatList) (l4 :: NatList).
             Sing l1 -> Sing l2 -> Sing l3 -> Sing l4
          -> l1 ++ (l2 ++ (l3 ++ l4)) :~: ((l1 ++ l2) ++ l3) ++ l4
appAssoc4 l1 l2 l3 l4 | Refl <- appAssoc l1 l2 (l3 %++ l4)
                      , Refl <- appAssoc (l1 %++ l2) l3 l4
                      = Refl

nonzerosApp :: forall (l1 :: NatList) (l2 :: NatList).
               Sing l1 -> Sing l2
            -> Nonzeros (l1 ++ l2) :~: Nonzeros l1 ++ Nonzeros l2
nonzerosApp SNil _ = Refl
nonzerosApp (SCons SZ     sls1) l2 | Refl <- nonzerosApp sls1 l2 = Refl
nonzerosApp (SCons (SS _) sls1) l2 | Refl <- nonzerosApp sls1 l2 = Refl

$(singletons [d|
  beqNatlist :: NatList -> NatList -> Bool
  beqNatlist []     []     = True
  beqNatlist (x:xs) (y:ys) = x == y && beqNatlist xs ys
  beqNatlist []     (_:_)  = False
  beqNatlist (_:_)  []     = False
  |])

beqNatlistRefl :: forall (l :: NatList).
                  Sing l -> True :~: BeqNatlist l l
beqNatlistRefl SNil = Refl
beqNatlistRefl (SCons sl sls) | Refl <- beqNatlistRefl sls
                              , Refl <- natRefl sl
                              = Refl

natRefl :: forall (n :: Nat). Sing n -> (n == n) :~: True
natRefl SZ = Refl
natRefl (SS sn) | Refl <- natRefl sn = Refl

countMemberNonzero :: forall (s :: Bag). Sing s ->
                      Lit 1 `Leb` Count (Lit 1) (Lit 1:s) :~: True
countMemberNonzero SNil = Refl
countMemberNonzero (SCons _ sls) | Refl <- countMemberNonzero sls = Refl

bleNSn :: forall (n :: Nat). Sing n ->
          n `Leb` S n :~: True
bleNSn SZ = Refl
bleNSn (SS sn) | Refl <- bleNSn sn = Refl

removeDecreasesCount :: forall (s :: Bag). Sing s ->
                        Count (Lit 0) (RemoveOne (Lit 0) s) `Leb` Count (Lit 0) s :~: True
removeDecreasesCount SNil = Refl
removeDecreasesCount (SCons SZ sls) | Refl <- removeDecreasesCount sls
                                    , Refl <- bleNSn (sCount SZ sls)
                                    = Refl
removeDecreasesCount (SCons (SS _) sls) | Refl <- removeDecreasesCount sls = Refl

revInjective :: forall (l1 :: NatList) (l2 :: NatList).
                Sing l1 -> Sing l2
             -> Rev l1 :~: Rev l2
             -> l1 :~: l2
revInjective sl1 sl2 Refl
  | let revRev :: Rev (Rev l1) :~: Rev (Rev l2)
        revRev = Refl
  , Refl <- revRev
  , Refl <- revInvolutive sl1
  , Refl <- revInvolutive sl2
  = Refl

$(singletons [d|
  data NatOption
    = Some Nat
    | None

  optionElim :: Nat -> NatOption -> Nat
  optionElim _ (Some n') = n'
  optionElim d None = d

  hd :: Nat -> NatList -> Nat
  hd def []    = def
  hd _   (h:_) = h

  hdError :: NatList -> NatOption
  hdError [] = None
  hdError (n:_) = Some n
  |])

testHdError1 :: HdError '[] :~: None
testHdError1 = Refl

testHdError2 :: HdError '[Lit 1] :~: Some (Lit 1)
testHdError2 = Refl

testHdError3 :: HdError (Map LitSym0 '[5,6]) :~: Some (Lit 5)
testHdError3 = Refl

optionElimHd :: forall (l :: NatList) (def :: Nat).
                Sing l -> Sing def
             -> Hd def l :~: OptionElim def (HdError l)
optionElimHd SNil       _ = Refl
optionElimHd (SCons {}) _ = Refl

$(singletons [d|
  newtype Id = Id Nat deriving Eq
  |])

beqIdRefl :: forall (x :: Id). Sing x -> (x == x) :~: True
beqIdRefl (SId n) = natRefl n

$(singletons [d|
  data PartialMap
    = Empty
    | Record Id Nat PartialMap

  update :: PartialMap -> Id -> Nat -> PartialMap
  update d x value = Record x value d

  find :: Id -> PartialMap -> NatOption
  find _ Empty = None
  find x (Record y v d') = if x == y
                           then Some v
                           else find x d'
  |])

updateEq :: forall (d :: PartialMap) (x :: Id) (v :: Nat).
            Sing d -> Sing x -> Sing v
         -> Find x (Update d x v) :~: Some v
updateEq sD sX sV
  = case sUpdate sD sX sV of
      SRecord sY _ sD' ->
        case sX %== sY of
          STrue -> Refl
          SFalse | Refl <- updateEq sD' sX sV
                 -> Refl

updateNeq :: forall (d :: PartialMap) (x :: Id) (y :: Id) (o :: Nat).
             Sing d -> Sing x -> Sing y -> Sing o
          -> (x == y) :~: False
          -> Find x (Update d y o) :~: Find x d
updateNeq _ _ _ _ Refl = Refl
