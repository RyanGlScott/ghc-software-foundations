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
module SF.IndProp where

import Data.Kind
import Data.Nat
import Data.Singletons.Prelude hiding (Not, POrd(..))
import Data.Singletons.Sigma
import Data.Singletons.TH (genDefunSymbols, singletons)
import Data.Type.Equality
import Prelude hiding (Double)
import SF.Basics
import SF.Induction
import SF.Logic
import SF.Poly (appAssoc, Fold) -- Length)

data Ev :: Nat -> Prop where
  Ev0  :: Ev Z
  EvSS :: Ev n -> Ev (S (S n))

evDouble :: forall (n :: Nat). Sing n -> Ev (Double n)
evDouble SZ      = Ev0
evDouble (SS sn) = EvSS (evDouble sn)

ssssEvEven :: forall (n :: Nat). Ev (S (S (S (S n)))) -> Ev n
ssssEvEven (EvSS (EvSS en)) = en

even5Nonsense :: Ev (Lit 5) -> (Lit 2 + Lit 2 :~: Lit 9)
even5Nonsense (EvSS (EvSS e)) = case e of {}

evSum :: forall (n :: Nat) (m :: Nat).
         Ev n -> Ev m -> Ev (n + m)
evSum Ev0       em = em
evSum (EvSS en) em = EvSS (evSum en em)

data Ev' :: Nat -> Prop where
  Ev'0   :: Ev' (Lit 0)
  Ev'2   :: Ev' (Lit 2)
  Ev'Sum :: Ev' n -> Ev' m -> Ev' (n + m)

ev'Ev :: forall (n :: Nat). Ev' n <-> Ev n
ev'Ev = (nec, suf)
  where
    nec :: forall (nn :: Nat). Ev' nn -> Ev nn
    nec Ev'0           = Ev0
    nec Ev'2           = EvSS Ev0
    nec (Ev'Sum en em) = evSum (nec en) (nec em)

    suf :: forall (nn :: Nat). Ev nn -> Ev' nn
    suf Ev0       = Ev'0
    suf (EvSS en) = Ev'Sum Ev'2 (suf en)

evEvEv :: forall (n :: Nat) (m :: Nat).
          Ev (n + m) -> Ev n -> Ev m
evEvEv enm       Ev0       = enm
evEvEv (EvSS en) (EvSS em) = evEvEv en em

evPlusPlus :: forall (n :: Nat) (m :: Nat) (p :: Nat).
              Sing n -> Sing m -> Sing p
           -> Ev (n + m) -> Ev (n + p) -> Ev (m + p)
evPlusPlus sn sm sp enm enp            -- (n + m) + (n + p)
  | Refl <- plusAssoc sn sm (sn %+ sp) -- n + (m + (n + p))
  , Refl <- plusAssoc sm sn sp         -- n + ((m + n) + p)
  , Refl <- plusComm sm sn             -- n + ((n + m) + p)
  , Refl <- plusAssoc sn sm sp         -- n + (n + (m + p))
  , Refl <- plusAssoc sn sn (sm %+ sp) -- (n + n) + (m + p)
  , Refl <- doublePlus sn              -- Double n + (m + p)
  = evEvEv (evSum enm enp) (evDouble sn)

data TotalRelation :: Nat -> Nat -> Prop where
  TR :: TotalRelation n n

data EmptyRelation :: Nat -> Nat -> Prop

data Le :: Nat -> Nat -> Prop where
  LeN :: Le n n
  LeS :: Le n m -> Le n (S m)

type (<=) = Le
infix 4 <=

type (<) (n :: Nat) = Le (S n)
infix 4 <

leTrans :: forall (m :: Nat) (n :: Nat) (o :: Nat).
           m <= n -> n <= o -> m <= o
leTrans leMN LeN         = leMN
leTrans leMN (LeS leNO') = LeS (leTrans leMN leNO')

zeroLeN :: forall (n :: Nat). Sing n -> Lit 0 <= n
zeroLeN SZ      = LeN
zeroLeN (SS sn) = LeS (zeroLeN sn)

leLiftS :: forall (n :: Nat) (m :: Nat).
           n <= m -> S n <= S m
leLiftS LeN       = LeN
leLiftS (LeS les) = LeS (leLiftS les)

leLowerS :: forall (n :: Nat) (m :: Nat).
            S n <= S m -> n <= m
leLowerS LeN                = LeN
leLowerS (LeS LeN)          = LeS LeN
leLowerS (LeS les@(LeS {})) = LeS (leLowerS les)

lePlusL :: forall (a :: Nat) (b :: Nat).
           Sing a -> Sing b
        -> a <= a + b
lePlusL SZ sb      = zeroLeN sb
lePlusL (SS sa) sb = leLiftS (lePlusL sa sb)

lePlusR :: forall (a :: Nat) (b :: Nat).
           Sing a -> Sing b
        -> b <= a + b
lePlusR sa SZ | Refl <- plus0R sa
              = zeroLeN sa
lePlusR sa (SS sb) | Refl <- plusNSm sa sb
                   = leLiftS (lePlusR sa sb)

plusLt :: forall (n1 :: Nat) (n2 :: Nat) (m :: Nat).
          Sing n1 -> Sing n2 -> Sing m
       -> n1 + n2 < m
       -> n1 < m /\ n2 < m
plusLt _ _ SZ x = case x of {}
plusLt sn1 sn2 (SS _) LeN
  | Refl <- plusNSm sn1 sn2
  = (lePlusL (SS sn1) sn2, lePlusR sn1 (SS sn2))
plusLt sn1 sn2 (SS sm) (LeS le)
  = case plusLt sn1 sn2 sm le of
      (n1LtM, n2LtM) -> (LeS n1LtM, LeS n2LtM)

ltS :: forall (n :: Nat) (m :: Nat).
       n < m -> n < S m
ltS LeN      = LeS LeN
ltS (LeS le) = LeS (ltS le)

lebComplete :: forall (n :: Nat) (m :: Nat).
               Sing n -> Sing m
            -> Leb n m :~: True -> n <= m
lebComplete SZ      sm      Refl = zeroLeN sm
lebComplete (SS _)  SZ      x    = case x of {}
lebComplete (SS sn) (SS sm) Refl = leLiftS $ lebComplete sn sm Refl

lebCorrect :: forall (n :: Nat) (m :: Nat).
              Sing n -> Sing m
           -> n <= m
           -> Leb n m :~: True
lebCorrect _  SZ      LeN = Refl
lebCorrect _  (SS sm) LeN = lemma sm
  where
    lemma :: forall (a :: Nat). Sing a
          -> Leb a a :~: True
    lemma SZ      = Refl
    lemma (SS sz) = lemma sz
lebCorrect sn sm' (LeS le) =
    case sm' of
      SS sm -> lemma sn sm (lebCorrect sn sm le)
  where
    lemma :: forall (a :: Nat) (b :: Nat).
             Sing a -> Sing b
          -> Leb a b :~: True -> Leb a (S b) :~: True
    lemma SZ      _       Refl = Refl
    lemma (SS _)  SZ      x    = case x of {}
    lemma (SS sa) (SS sb) Refl = lemma sa sb Refl

lebTrueTrans :: forall (n :: Nat) (m :: Nat) (o :: Nat).
                Sing n -> Sing m -> Sing o
             -> Leb n m :~: True
             -> Leb m o :~: True
             -> Leb n o :~: True
lebTrueTrans sn sm so nLeM mLeO
  = lebCorrect sn so $
    leTrans (lebComplete sn sm nLeM) (lebComplete sm so mLeO)

lebIff :: forall (n :: Nat) (m :: Nat).
          Sing n -> Sing m
       -> Leb n m :~: True <-> n <= m
lebIff sn sm = (nec, suf)
  where
    nec :: Leb n m :~: True -> n <= m
    nec = lebComplete sn sm

    suf :: n <= m -> Leb n m :~: True
    suf = lebCorrect sn sm

data R :: Nat -> Nat -> Nat -> Prop where
  C1 :: R Z Z Z
  C2 :: R m n o -> R (S m) n (S o)
  C3 :: R m n o -> R m (S n) (S o)
  C4 :: R (S m) (S n) (S (S o)) -> R m n o
  C5 :: R m n o -> R n m o

r112 :: R (Lit 1) (Lit 1) (Lit 2)
r112 = C3 $ C2 C1

$(singletons [d|
  fR :: Nat -> Nat -> Nat
  fR = (+)
  |])

rEquivFR :: forall (m :: Nat) (n :: Nat) (o :: Nat).
            Sing m -> Sing n -> Sing o
         -> R m n o <-> FR m n :~: o
rEquivFR sm sn so = (nec sm sn so, suf sm sn so)
  where
    nec :: forall (mm :: Nat) (nn :: Nat) (oo :: Nat).
           Sing mm -> Sing nn -> Sing oo
        -> R mm nn oo -> FR mm nn :~: oo
    nec SZ SZ SZ C1 = Refl
    nec (SS smm) snn (SS soo) (C2 c) | Refl <- nec smm snn soo c = Refl
    nec smm (SS snn) (SS soo) (C3 c) | Refl <- nec smm snn soo c
                                     , Refl <- plusNSm smm snn
                                     = Refl
    nec smm snn soo (C4 c)
      | Refl <- nec (SS smm) (SS snn) (SS (SS soo)) c
      , Refl <- plusNSm smm snn
      = Refl
    nec smm snn soo (C5 c) | Refl <- nec snn smm soo c
                           , Refl <- plusComm smm snn
                           = Refl

    suf :: forall (mm :: Nat) (nn :: Nat) (oo :: Nat).
           Sing mm -> Sing nn -> Sing oo
        -> FR mm nn :~: oo -> R mm nn oo
    suf SZ SZ SZ Refl = C1
    suf (SS smm) snn (SS soo) Refl = C2 $ suf smm snn soo Refl
    suf smm (SS snn) (SS soo) Refl | Refl <- plusNSm smm snn
                                   = C3 $ suf smm snn soo Refl
    suf SZ     SZ     (SS _) x = case x of {}
    suf SZ     (SS _) SZ     x = case x of {}
    suf (SS _) SZ     SZ     x = case x of {}
    suf (SS _) (SS _) SZ     x = case x of {}

data Subseq :: [Nat] -> [Nat] -> Prop where
  SubseqNil    :: Subseq '[] l2
  SubseqCons   :: Subseq a b -> Subseq (x:a) (x:b)
  SubseqExtend :: Subseq a b -> Subseq a (y:b)

subseqRefl :: forall (l :: [Nat]). Sing l -> Subseq l l
subseqRefl SNil          = SubseqNil
subseqRefl (SCons _ sxs) = SubseqCons (subseqRefl sxs)

subseqApp :: forall (l1 :: [Nat]) (l2 :: [Nat]) (l3 :: [Nat]).
             Subseq l1 l2 -> Subseq l1 (l2 ++ l3)
subseqApp SubseqNil = SubseqNil
subseqApp (SubseqCons (ss :: Subseq a b))
  = SubseqCons $ subseqApp @a @b @l3 ss
subseqApp (SubseqExtend (ss :: Subseq a b))
  = SubseqExtend $ subseqApp @a @b @l3 ss

subseqTrans :: forall (l1 :: [Nat]) (l2 :: [Nat]) (l3 :: [Nat]).
               Subseq l1 l2 -> Subseq l2 l3 -> Subseq l1 l3
subseqTrans ss12                SubseqNil           = subseqApp ss12
subseqTrans SubseqNil           (SubseqCons _)      = SubseqNil
subseqTrans (SubseqCons ss12)   (SubseqCons ss23)   = SubseqCons   $ subseqTrans ss12 ss23
subseqTrans (SubseqExtend ss12) (SubseqCons ss23)   = SubseqExtend $ subseqTrans ss12 ss23
subseqTrans ss12                (SubseqExtend ss23) = SubseqExtend $ subseqTrans ss12 ss23

data R' :: Nat -> [Nat] -> Prop where
  C1' :: R' Z '[]
  C2' :: R' n l     -> R' (S n) (n:l)
  C3' :: R' (S n) l -> R' n l

r'2L10 :: R' (Lit 2) (Map LitSym0 '[1,0])
r'2L10 = C2' $ C2' C1'

r'1L1210 :: R' (Lit 1) (Map LitSym0 '[1,2,1,0])
r'1L1210 = C3' $ C2' $ C3' $ C3' $ C2' $ C2' $ C2' C1'

$(singletons [d|
  data RegExp :: Type -> Type where
    EmptySet :: RegExp t
    EmptyStr :: RegExp t
    Char     :: t -> RegExp t
    App      :: RegExp t -> RegExp t -> RegExp t
    Union    :: RegExp t -> RegExp t -> RegExp t
    Star     :: RegExp t -> RegExp t
  |])

data ExpMatch :: forall (t :: Type). [t] -> RegExp t -> Prop where
  MEmpty   :: ExpMatch '[] EmptyStr
  MChar    :: ExpMatch '[x] ('Char x)
  MApp     :: Sing s1 -> Sing s2
           -> ExpMatch s1 re1
           -> ExpMatch s2 re2
           -> ExpMatch (s1 ++ s2) (App re1 re2)
  MUnionL  :: ExpMatch s1 re1
           -> ExpMatch s1 (Union re1 re2)
  MUnionR  :: ExpMatch s2 re2
           -> ExpMatch s2 (Union re1 re2)
  MStar0   :: ExpMatch '[] (Star re)
  MStarApp :: ExpMatch s1 re
           -> ExpMatch s2 (Star re)
           -> ExpMatch (s1 ++ s2) (Star re)

type (=~) = ExpMatch
infix 8 =~
$(genDefunSymbols [''(=~)])

emptyIsEmpty :: forall (t :: Type) (s :: [t]).
                Not (s =~ EmptySet)
emptyIsEmpty x = case x of {}

mUnion' :: forall (t :: Type) (s :: [t]) (re1 :: RegExp t) (re2 :: RegExp t).
           s =~ re1 \/ s =~ re2
        -> s =~ Union re1 re2
mUnion' = either MUnionL MUnionR


mStar' :: forall (t :: Type) (ss :: [[t]]) (re :: RegExp t).
          Sing ss
       -- Uncomment below for a GHC 8.4.1 panic
       -- -> (forall (s :: _). In s ss -> s =~ re)
       -> (forall (s :: [t]). In s ss -> s =~ re)
       -> Fold (++@#@$) ss '[] =~ Star re
mStar' SNil _ = MStar0
mStar' (SCons _ sxs) f
  = MStarApp (f $ Left Refl)
             (mStar' sxs $ f . Right)

$(singletons [d|
  regExpOfList :: [t] -> RegExp t
  regExpOfList []     = EmptyStr
  regExpOfList (x:l') = App (Char x) (regExpOfList l')
  |])

regExpOfListSpec :: forall (t :: Type) (s1 :: [t]) (s2 :: [t]).
                    Sing s1 -> Sing s2
                 -> s1 =~ RegExpOfList s2 <-> s1 :~: s2
regExpOfListSpec s1 s2 = (nec s1 s2, suf s1 s2)
  where
    nec :: forall (s1' :: [t]) (s2' :: [t]).
           Sing s1' -> Sing s2'
        -> s1' =~ RegExpOfList s2' -> s1' :~: s2'
    nec _              SNil           MEmpty         = Refl
    nec SNil           (SCons {})     (MApp _ _ x _) = case x of {}
    nec (SCons _ sxs1) (SCons _ sxs2) (MApp _ _ MChar em)
      | Refl <- nec sxs1 sxs2 em
      = Refl

    suf :: forall (s1' :: [t]) (s2' :: [t]).
           Sing s1' -> Sing s2'
        -> s1' :~: s2' -> s1' =~ RegExpOfList s2'
    suf _              SNil           Refl = MEmpty
    suf SNil           (SCons {})     x    = case x of {}
    suf (SCons sx1 sxs1) (SCons _ sxs2) Refl =
      MApp (SCons sx1 SNil) sxs1 MChar $ suf sxs1 sxs2 Refl

$(singletons [d|
  reNotEmpty :: RegExp t -> Bool
  reNotEmpty EmptySet        = False
  reNotEmpty EmptyStr        = True
  reNotEmpty (Char _)        = True
  reNotEmpty (App re1 re2)   = reNotEmpty re1 && reNotEmpty re2
  reNotEmpty (Union re1 re2) = reNotEmpty re1 || reNotEmpty re2
  reNotEmpty (Star _)        = True
  |])

reNotEmptyCorrect :: forall (t :: Type) (re :: RegExp t). Sing re
                  -> Sigma [t] (FlipSym2 (TyCon2 (=~)) re) <-> ReNotEmpty re :~: True
reNotEmptyCorrect sre = (nec sre, suf sre)
  where
    nec :: forall (re' :: RegExp t). Sing re'
        -> Sigma [t] (FlipSym2 (TyCon2 (=~)) re') -> ReNotEmpty re' :~: True
    nec SEmptySet (_ :&: em) = case em of {}
    nec SEmptyStr _ = Refl
    nec (SChar _) _ = Refl
    nec (SApp sre1 sre2) (_ :&: MApp s1 s2 em1 em2)
      = case (nec sre1 (s1 :&: em1), nec sre2 (s2 :&: em2)) of
          (Refl, Refl) -> Refl
    nec (SUnion sre1 _) (l :&: MUnionL em)
      | Refl <- nec sre1 (l :&: em)
      = Refl
    nec (SUnion _ sre2) (l :&: MUnionR em)
      | Refl <- nec sre2 (l :&: em)
      = Refl
    nec (SStar _) _ = Refl

    suf :: forall (re' :: RegExp t). Sing re'
        -> ReNotEmpty re' :~: True -> Sigma [t] (FlipSym2 (TyCon2 (=~)) re')
    suf SEmptySet x    = case x of {}
    suf SEmptyStr Refl = SNil :&: MEmpty
    suf (SChar t) Refl = (SCons t SNil) :&: MChar
    suf (SApp sre1 sre2) Refl
      = case (sReNotEmpty sre1, sReNotEmpty sre2) of
          (STrue, STrue)
            -> case (suf sre1 Refl, suf sre2 Refl) of
                 (l1 :&: em1, l2 :&: em2) -> (l1 %++ l2) :&: MApp l1 l2 em1 em2
    suf (SUnion sre1 sre2) Refl
      = case (sReNotEmpty sre1, sReNotEmpty sre2) of
          (STrue, _)
            -> case suf sre1 Refl of
                 l :&: em -> l :&: MUnionL em
          (SFalse, STrue)
            -> case suf sre2 Refl of
                 l :&: em -> l :&: MUnionR em
    suf (SStar _) Refl = SNil :&: MStar0

type MStar''Aux1 (s :: [t]) (re :: RegExp t) (ss :: [[t]])
  = s :~: Fold (++@#@$) ss '[] /\ MStar''Aux2 re ss
newtype MStar''Aux2 (re :: RegExp t) (ss :: [[t]])
  = MkMStar''Aux2 { runMStar''Aux2 :: forall (s' :: [t]). In s' ss -> s' =~ re }
$(genDefunSymbols [''MStar''Aux1])

{-
mStar'' :: forall (t :: Type) (s :: [t]) (re :: RegExp t).
           Sing re
        -> s =~ Star re
        -> Sigma [[t]] (MStar''Aux1Sym2 s re)
-}

-- TODO RGS

$(singletons [d|
  pumpingConstant :: RegExp t -> Nat
  pumpingConstant EmptySet = 0
  pumpingConstant EmptyStr = 1
  pumpingConstant (Char _) = 2
  pumpingConstant (App re1 re2)   = pumpingConstant re1 + pumpingConstant re2
  pumpingConstant (Union re1 re2) = pumpingConstant re1 + pumpingConstant re2
  pumpingConstant (Star _) = 1

  napp :: Nat -> [t] -> [t]
  napp Z      _ = []
  napp (S n') l = l ++ napp n' l
  |])

nappPlus :: forall (t :: Type) (n :: Nat) (m :: Nat) (l :: [t]).
            Sing n -> Sing m -> Sing l
         -> Napp (n + m) l :~: Napp n l ++ Napp m l
nappPlus SZ _ _ = Refl
nappPlus (SS sn) sm sl | Refl <- nappPlus sn sm sl
                       , Refl <- appAssoc sl (sNapp sn sl) (sNapp sm sl)
                       = Refl

type family PumpingAux1 (re :: RegExp t) (s :: [t]) (ss :: ([t], [t], [t])) :: Type where
  PumpingAux1 re s '(s1, s2, s3)
    =    s :~: (s1 ++ s2 ++ s3)
      /\ Not (s2 :~: '[])
      /\ PumpingAux2 re s1 s2 s3
newtype PumpingAux2 (re :: RegExp t) (s1 :: [t]) (s2 :: [t]) (s3 :: [t])
  = MkPumpingAux2 { runPumpingAux2 :: forall (m :: Nat).
                                      Proxy m -> s1 ++ Napp m s2 ++ s3 =~ re }
$(genDefunSymbols [''PumpingAux1])

{-
pumping :: forall (t :: Type) (re :: RegExp t) (s :: [t]).
           s =~ re
        -> PumpingConstant re <= Length s
        -> Sigma ([t], [t], [t]) (PumpingAux1Sym2 re s)
pumping = undefined
-}

-- TODO RGS