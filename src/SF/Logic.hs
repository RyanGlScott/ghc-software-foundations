{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
module SF.Logic where

import Data.Kind
import Data.Nat
import Data.Singletons.Prelude hiding
       ( All, AllSym0, AllSym1, AllSym2, Not, NotSym0, NotSym1 )
import Data.Singletons.Sigma
import Data.Singletons.TH
import Data.Void
import SF.Induction
import Prelude hiding (Double)

type Prop = Type -- lol
type Not a = a -> Void
type (/\) = (,)
infixr 3 /\
type (\/) = Either
infixr 2 \/
type p <-> q = (p -> q) /\ (q -> p)
infix 1 <->
type a :/: b = (a :~: b) -> Void
infix 4 :/:
$(genDefunSymbols [''Not, ''(/\), ''(\/), ''(<->), ''(:/:)])

andExercise :: forall (n :: Nat) (m :: Nat).
               Sing n -> Sing m
            -> n + m :~: Lit 0
            -> (n :~: Lit 0) /\ (m :~: Lit 0)
andExercise SZ     _ Refl = (Refl, Refl)
andExercise (SS _) _ x    = case x of {}

proj2 :: forall (p :: Prop) (q :: Prop).
         p /\ q -> q
proj2 = snd

andAssoc :: forall (p :: Prop) (q :: Prop) (r :: Prop).
            p /\ (q /\ r) -> (p /\ q) /\ r
andAssoc (p, (q, r)) = ((p, q), r)

notImpliesOurNot :: forall (p :: Prop).
  Not p -> (forall (q :: Prop). p -> q)
notImpliesOurNot np p = absurd (np p)

contrapositive :: forall (p :: Prop) (q :: Prop).
  (p -> q) -> (Not q -> Not p)
contrapositive pq nq = nq . pq

notBothTrueAndFalse :: forall (p :: Prop).
  Not (p, Not p)
notBothTrueAndFalse (p, np) = np p

orDistributesOverAnd :: forall (p :: Prop) (q :: Prop) (r :: Prop).
                        p \/ (q /\ r) <-> (p \/ q) /\ (p \/ r)
orDistributesOverAnd = (nec, suf)
  where
    nec :: p \/ (q /\ r) -> (p \/ q) /\ (p \/ r)
    nec (Left p) = (Left p, Left p)
    nec (Right (q,r)) = (Right q, Right r)

    suf :: (p \/ q) /\ (p \/ r) -> p \/ (q /\ r)
    suf (_,       Left p)  = Left p
    suf (Left p,  _)       = Left p
    suf (Right q, Right r) = Right (q,r)

distNotExists :: forall (x :: Type) (p :: x ~> Prop).
  (forall xx. p @@ xx) -> Not (Sigma x (NotSym0 .@#@$$$ p))
distNotExists px ((_ :: Sing xx) :&: npx) = npx (px @xx)

type POrQ (p :: x ~> Prop) (q :: x ~> Prop) (xx :: x)
  = (p @@ xx) \/ (q @@ xx)
$(genDefunSymbols [''POrQ])

distExistsOr :: forall (x :: Type) (p :: x ~> Prop) (q :: x ~> Prop).
                Sigma x (POrQSym2 p q) <-> Sigma x p \/ Sigma x q
distExistsOr = (nec, suf)
  where
    nec :: Sigma x (POrQSym2 p q) -> Sigma x p \/ Sigma x q
    nec (x :&: y) = case y of
                      Left  yy -> Left  (x :&: yy)
                      Right yy -> Right (x :&: yy)

    suf :: Sigma x p \/ Sigma x q -> Sigma x (POrQSym2 p q)
    suf (Left  (x :&: y)) = x :&: Left  y
    suf (Right (x :&: y)) = x :&: Right y

type family In (x :: a) (l :: [a]) :: Prop where
  In _ '[]     = Void
  In x (x':l') = x' :~: x \/ In x l'

type InAppIffAux (f :: a ~> b) (l :: [a]) (y :: b) (x :: a)
  = f @@ x :~: y /\ In x l
$(genDefunSymbols [''InAppIffAux])

inMapIff :: forall (a :: Type) (b :: Type)
                   (f :: a ~> b) (l :: [a]) (y :: b).
            Sing f -> Sing l -> Sing y
         -> In y (Map f l) <-> Sigma a (InAppIffAuxSym3 f l y)
inMapIff _ sL _ = (nec sL, suf sL)
  where
    nec :: forall (ll :: [a]). Sing ll
        -> In y (Map f ll) -> Sigma a (InAppIffAuxSym3 f ll y)
    nec SNil (i :: Void) = case i of {}
    nec (SCons sl sls) i
      = case i of
          Left  Refl -> sl :&: (Refl, Left Refl)
          Right i'   -> case nec sls i' of
                          sl' :&: (Refl, wat) -> sl' :&: (Refl, Right wat)

    suf :: forall (ll :: [a]). Sing ll
        -> Sigma a (InAppIffAuxSym3 f ll y) -> In y (Map f ll)
    suf SNil (_ :&: (_, x)) = absurd x
    suf (SCons _ _)   (_  :&: (Refl, Left Refl)) = Left Refl
    suf (SCons _ sls) (hm :&: (Refl, Right i'))
      = Right $ suf sls (hm :&: (Refl, i'))

inAppIff :: forall (a :: Type) (l :: [a]) (l' :: [a]) (aa :: a).
            Sing l -> Sing l' -> Sing aa
         -> In aa (l ++ l') <-> In aa l \/ In aa l'
inAppIff sL _ _ = (nec sL, suf sL)
  where
    nec :: forall (ll :: [a]). Sing ll ->
           In aa (ll ++ l') -> In aa ll \/ In aa l'
    nec SNil i = Right i
    nec (SCons _ sls) i
      = case i of
          Left Refl -> Left (Left Refl)
          Right i' -> case nec sls i' of
                        Left  l -> Left (Right l)
                        Right r -> Right r

    suf :: forall (ll :: [a]). Sing ll ->
           In aa ll \/ In aa l' -> In aa (ll ++ l')
    suf SNil i
      = case i of
          Left  l -> absurd l
          Right r -> r
    suf (SCons _ sls) i
      = case i of
          Left (Left Refl) -> Left Refl
          Left (Right i')  -> Right $ suf sls (Left i')
          Right i'         -> Right $ suf sls (Right i')

type family All (p :: t ~> Prop) (l :: [t]) :: Prop where
  All _ '[] = ()
  All p (x:xs) = (p @@ x, All p xs)


{-
allIn1 :: forall (t :: Type) (p :: t ~> Prop) (l :: [t]).
          Sing p -> Sing l
       -> (forall z. In z l -> p @@ z) -> All p l
allIn1 _  SNil _ = ()
allIn1 sP (SCons (_ :: Sing x) (sls :: Sing xs)) ip
  = (px, apx) -- (\(x :: In z xs) -> ip @z (Right x :: In z l) :: p @@ z))
  where
    px :: p @@ x
    px = ip (Left Refl)

    apx :: All p xs
    apx = allIn1 sP sls (\(x :: In z xs) -> wat @z x)

    wat :: forall z. In z xs -> p @@ z
    wat = undefined
-}

{-
allIn2 :: forall (t :: Type) (p :: t ~> Prop) (l :: [t]) (z :: t).
          Sing p -> Sing l
       -> All p l -- -> (forall (z :: t). In z l -> p @@ z)
       -> In z l -> p @@ z
allIn2 _ SNil () x = absurd x
allIn2 sP (SCons _ (sls :: Sing ls)) (px, apx) i
  = case i of
      Left Refl -> px
      Right (i' :: In z ls) ->
        case allIn2 sP sls apx i' of
          _ -> _
-}

-- TODO RGS

$(singletons [d|
  oddb :: Nat -> Bool
  oddb Z         = False
  oddb (S Z)     = True
  oddb (S (S n)) = oddb n
  |])

type CombineOddEven (podd :: Nat ~> Prop) (peven :: Nat ~> Prop) (n :: Nat)
  = If (Oddb n) (podd @@ n) (peven @@ n)

combineOddEvenIntro :: forall (podd :: Nat ~> Prop) (peven :: Nat ~> Prop) (n :: Nat).
                       Sing podd -> Sing peven -> Sing n
                    -> (Oddb n :~: True  -> podd  @@ n)
                    -> (Oddb n :~: False -> peven @@ n)
                    -> CombineOddEven podd peven n
combineOddEvenIntro _ _ sn po pe
  = case sOddb sn of
      STrue  -> po Refl
      SFalse -> pe Refl

combineOddEvenElimOdd :: forall (podd :: Nat ~> Prop) (peven :: Nat ~> Prop) (n :: Nat).
                         Sing podd -> Sing peven -> Sing n
                      -> CombineOddEven podd peven n
                      -> Oddb n :~: True
                      -> podd @@ n
combineOddEvenElimOdd _ _ _ coe Refl = coe

combineOddEvenElimEven :: forall (podd :: Nat ~> Prop) (peven :: Nat ~> Prop) (n :: Nat).
                          Sing podd -> Sing peven -> Sing n
                       -> CombineOddEven podd peven n
                       -> Oddb n :~: False
                       -> peven @@ n
combineOddEvenElimEven _ _ _ coe Refl = coe

$(singletons [d|
  rev :: [a] -> [a]
  rev [] = []
  rev (x:xs) = rev xs ++ [x]

  revAppend :: [x] -> [x] -> [x]
  revAppend []      l2 = l2
  revAppend (x:l1') l2 = revAppend l1' (x:l2)

  trRev :: [x] -> [x]
  trRev l = revAppend l []
  |])

trRevCorrect :: forall (a :: Type) (x :: [a]). Sing x
             -> TrRev x :~: Rev x
trRevCorrect SNil = Refl
trRevCorrect (SCons sl sls)
  | Refl <- trRevCorrect sls
  , Refl <- lemma sls SNil (SCons sl SNil)
  = Refl
  where
    lemma :: forall (l1 :: [a]) (l2 :: [a]) (l3 :: [a]).
             Sing l1 -> Sing l2 -> Sing l3
          -> RevAppend l1 (l2 ++ l3) :~: RevAppend l1 l2 ++ l3
    lemma SNil _ _ = Refl
    lemma (SCons sl1 sls1) sl2 sl3
      | Refl <- lemma sls1 (SCons sl1 sl2) sl3
      = Refl

type EDCAux (n :: Nat) (k :: Nat) = n :~: If (Evenb n) (Double k) (S (Double k))
$(genDefunSymbols [''EDCAux])

evenbDoubleConv :: forall (n :: Nat). Sing n ->
                   Sigma Nat (EDCAuxSym1 n)
evenbDoubleConv SZ      = SZ :&: Refl
evenbDoubleConv (SS sn)
  | sn' :&: Refl <- evenbDoubleConv sn
  , Refl <- evenbS sn
  = case sEvenb sn of
      STrue -> sn' :&: Refl
      SFalse -> SS sn' :&: Refl

type EBPAux (n :: Nat) (k :: Nat) = n :~: Double k
$(genDefunSymbols [''EBPAux])

andbTrueIff :: forall (b1 :: Bool) (b2 :: Bool).
               Sing b1 -> Sing b2
            -> (b1 && b2) :~: True <-> (b1 :~: True) /\ (b2 :~: True)
andbTrueIff s1 _ = (nec s1, suf s1)
  where
    nec :: forall (bb1 :: Bool). Sing bb1
        -> (bb1 && b2) :~: True -> (bb1 :~: True) /\ (b2 :~: True)
    nec STrue Refl = (Refl, Refl)
    nec SFalse x = case x of {}

    suf :: forall (bb1 :: Bool). Sing bb1
        -> (bb1 :~: True) /\ (b2 :~: True) -> (bb1 && b2) :~: True
    suf STrue  (Refl, Refl) = Refl
    suf SFalse (x, Refl) = case x of {}

orbTrueIff :: forall (b1 :: Bool) (b2 :: Bool).
              Sing b1 -> Sing b2
           -> (b1 || b2) :~: True <-> (b1 :~: True) \/ (b2 :~: True)
orbTrueIff s1 _ = (nec s1, suf)
  where
    nec :: forall (bb1 :: Bool). Sing bb1
        -> (bb1 || b2) :~: True -> (bb1 :~: True) \/ (b2 :~: True)
    nec STrue  Refl = Left Refl
    nec SFalse Refl = Right Refl

    suf :: (b1 :~: True) \/ (b2 :~: True) -> (b1 || b2) :~: True
    suf (Left Refl) = Refl
    suf (Right Refl) = Refl

beqNatFalse :: forall (x :: Nat) (y :: Nat).
               Sing x -> Sing y
            -> (x == y) :~: False <-> x :/: y
beqNatFalse sx sy = (nec sx sy, suf sx sy)
  where
    nec :: forall (xx :: Nat) (yy :: Nat).
           Sing xx -> Sing yy
        -> (xx == yy) :~: False -> xx :/: yy
    nec SZ       _        Refl xy   = case xy of {}
    nec (SS _)   SZ       Refl xy   = case xy of {}
    nec (SS sx') (SS sy') Refl Refl = nec sx' sy' Refl Refl

    suf :: forall (xx :: Nat) (yy :: Nat).
           Sing xx -> Sing yy
        -> xx :/: yy -> (xx == yy) :~: False
    suf SZ       SZ       f = absurd (f Refl)
    suf SZ       SS{}     _ = Refl
    suf SS{}     SZ       _ = Refl
    suf (SS sx') (SS sy') f = suf sx' sy' $ \Refl -> f Refl

$(singletons [d|
  beqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
  beqList _ []     []     = True
  beqList _ []     (_:_)  = False
  beqList _ (_:_)  []     = False
  beqList f (x:xs) (y:ys) = f x y && beqList f xs ys
  |])

beqListTrueIff :: forall (a :: Type) (beq :: a ~> a ~> Bool).
                  Sing beq
               -> (forall (a1 :: a) (a2 :: a).
                      Sing a1 -> Sing a2
                   -> beq @@ a1 @@ a2 :~: True <-> a1 :~: a2)
               -> forall (l1 :: [a]) (l2 :: [a]).
                  Sing l1 -> Sing l2
               -> BeqList beq l1 l2 :~: True <-> l1 :~: l2
beqListTrueIff sBeq flurb sl1 sl2 = (nec sl1 sl2, suf sl1 sl2)
  where
    nec :: forall (z1 :: [a]) (z2 :: [a]).
           Sing z1 -> Sing z2
        -> BeqList beq z1 z2 :~: True -> z1 :~: z2
    nec SNil SNil Refl = Refl
    nec SNil SCons{} x = case x of {}
    nec SCons{} SNil x = case x of {}
    nec (SCons sz1 szs1) (SCons sz2 szs2) Refl
      = case sBeq @@ sz1 @@ sz2 of
          STrue
            | Refl <- fst (flurb sz1 sz2) Refl
            , Refl <- nec szs1 szs2 Refl
           -> Refl

    suf :: forall (z1 :: [a]) (z2 :: [a]).
           Sing z1 -> Sing z2
        -> z1 :~: z2 -> BeqList beq z1 z2 :~: True
    suf SNil    SNil    Refl = Refl
    suf SNil    SCons{} x    = case x of {}
    suf SCons{} SNil    x    = case x of {}
    suf (SCons sz1 szs1) (SCons sz2 szs2) Refl
      | Refl <- snd (flurb sz1 sz2) Refl
      , Refl <- suf szs1 szs2 Refl
      = Refl

$(singletons [d|
  forallb :: (x -> Bool) -> [x] -> Bool
  forallb _    []     = True
  forallb test (x:l') = test x && forallb test l'
  |])

type FTIAux (test :: x ~> Bool) (a :: x) = test @@ a :~: True
$(genDefunSymbols [''FTIAux])

forallbTrueIff :: forall (x :: Type) (test :: x ~> Bool) (l :: [x]).
                  Sing test -> Sing l
               -> Forallb test l :~: True <-> All (FTIAuxSym1 test) l
forallbTrueIff sTest sl = (nec sl, suf sl)
  where
    nec :: forall (z :: [x]). Sing z
        -> Forallb test z :~: True -> All (FTIAuxSym1 test) z
    nec SNil Refl = ()
    nec (SCons sz szs) Refl
      = case sTest @@ sz of
          STrue -> (Refl, nec szs Refl)

    suf :: forall (z :: [x]). Sing z
        -> All (FTIAuxSym1 test) z -> Forallb test z :~: True
    suf SNil () = Refl
    suf (SCons _ szs) (Refl, a) = suf szs a

-- TODO RGS

excludedMiddleIrrefutable :: forall (p :: Prop).
  Not (Not (Either p (Not p)))
excludedMiddleIrrefutable nne = nne $ Right $ nne . Left

excludedMiddle :: forall (p :: Prop).
  Either p (Not p)
excludedMiddle = excludedMiddle

-- TODO RGS

type Peirce = forall (p :: Prop) (q :: Prop). ((p -> q) -> p) -> p

type DoubleNegationElimination = forall (p :: Prop). Not (Not p) -> p

type DeMorganNotAndNot = forall (p :: Prop) (q :: Prop). Not (Not p /\ Not q) -> p \/ q

type ImpliesToOr = forall (p :: Prop) (q :: Prop). (p -> q) -> (Not p \/ q)

oneToTwo :: Peirce -> DoubleNegationElimination
oneToTwo peirce dne = peirce (absurd . dne)

twoToOne :: DoubleNegationElimination -> Peirce
twoToOne dne peirce = dne $ \f -> f (peirce (absurd . f))

{-
oneToThree :: Peirce -> DeMorganNotAndNot
oneToThree peirce deMorgan
  = absurd $ deMorgan (peirce _)
  -- = peirce $ \(pqr :: _) -> pqr (absurd $ deMorgan _)
-}

threeToOne :: DeMorganNotAndNot -> Peirce
threeToOne deMorgan peirce
  = either id id $ deMorgan $ \(np, nq) -> np $ peirce $ absurd . nq

{-
oneToFour :: Peirce -> ImpliesToOr
oneToFour peirce impliesToOr
  =
-}

{-
fourToOne :: ImpliesToOr -> Peirce
fourToOne impliesToOr peirce = either peirce _ $ impliesToOr _
-}

twoToThree :: DoubleNegationElimination -> DeMorganNotAndNot
twoToThree dne deMorgan = dne $ \nPorQ -> deMorgan (nPorQ . Left, nPorQ . Right)

threeToTwo :: DeMorganNotAndNot -> DoubleNegationElimination
threeToTwo deMorgan dne = either id id $ deMorgan $ dne . fst

twoToFour :: DoubleNegationElimination -> ImpliesToOr
twoToFour dne impliesToOr
  = dne $ \nNpOrQ -> nNpOrQ $ Left $ nNpOrQ . Right . impliesToOr

{-
fourToTwo :: ImpliesToOr -> DoubleNegationElimination
fourToTwo impliesToOr dne
  = case impliesToOr (\wat -> dne $ \p -> wat p) of
      Left (nnp :: _) -> absurd $ nnp $ \(_ :: _) -> _
      Right y -> absurd y
-}

threeToFour :: DeMorganNotAndNot -> ImpliesToOr
threeToFour deMorgan impliesToOr = deMorgan $ \(nnp, nq) -> nnp $ nq .impliesToOr

{-
fourToThree :: ImpliesToOr -> DeMorganNotAndNot
fourToThree impliesToOr deMorgan = absurd $ deMorgan $ _ $ impliesToOr _
-}

{-
type Peirce = forall (p :: Prop) (q :: Prop). ((p -> q) -> p) -> p

type DoubleNegationElimination = forall (p :: Prop). Not (Not p) -> p

type DeMorganNotAndNot = forall (p :: Prop) (q :: Prop). Not (Not p /\ Not q) -> p \/ q

type ImpliesToOr = forall (p :: Prop) (q :: Prop). (p -> q) -> (Not p \/ q)
-}

-- TODO RGS
