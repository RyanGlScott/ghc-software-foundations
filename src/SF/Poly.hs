{-# LANGUAGE AllowAmbiguousTypes #-}
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
module SF.Poly where

import Data.Kind
import Data.Nat
import Data.Singletons.Prelude
import Data.Singletons.Prelude.List hiding
       ( Length, LengthSym0, LengthSym1, sLength )
import Data.Singletons.TH
import SF.Induction
import Prelude hiding (length)

$(singletons [d|
  length :: [a] -> Nat
  length [] = Z
  length (_:xs) = S (length xs)

  rev :: [a] -> [a]
  rev [] = []
  rev (x:xs) = rev xs ++ [x]
  |])

appNilR :: forall (x :: Type) (l :: [x]). Sing l
        -> l ++ '[] :~: l
appNilR SNil = Refl
appNilR (SCons _ sls) | Refl <- appNilR sls = Refl

appAssoc :: forall (a :: Type) (l :: [a]) (m :: [a]) (n :: [a]).
            Sing l -> Sing m -> Sing n
         -> l ++ (m ++ n) :~: (l ++ m) ++ n
appAssoc SNil _ _ = Refl
appAssoc (SCons _ sls) sm sn | Refl <- appAssoc sls sm sn
                             = Refl

appLength :: forall (x :: Type) (l1 :: [x]) (l2 :: [x]).
             Sing l1 -> Sing l2
          -> Length (l1 ++ l2) :~: Length l1 + Length l2
appLength SNil _ = Refl
appLength (SCons _ sls1) sl2 | Refl <- appLength sls1 sl2
                             = Refl

revAppDistr :: forall (x :: Type) (l1 :: [x]) (l2 :: [x]).
               Sing l1 -> Sing l2
            -> Rev (l1 ++ l2) :~: Rev l2 ++ Rev l1
revAppDistr SNil sl2 | Refl <- appNilR (sRev sl2) = Refl
revAppDistr (SCons s1 sls1) sl2
  | Refl <- revAppDistr sls1 sl2
  , Refl <- appAssoc (sRev sl2) (sRev sls1) (SCons s1 SNil)
  = Refl

revInvolutive :: forall (x :: Type) (l :: [x]). Sing l -> Rev (Rev l) :~: l
revInvolutive SNil = Refl
revInvolutive (SCons sl sls) | Refl <- revInvolutive sls
                             , Refl <- revAppDistr (sRev sls) (SCons sl SNil)
                             = Refl

$(singletons [d|
  split :: [(x,y)] -> ([x],[y])
  split [] = ([], [])
  split ((a,b):zs) =
    let (as,bs) = split zs
    in (a:as, b:bs)
  |])

testSplit :: Split '[ '(1,False), '(2,False) ] :~: '( '[1,2], '[False,False] )
testSplit = Refl

$(singletons [d|
  data Option x
    = Some x
    | None

  hdError :: [x] -> Option x
  hdError []    = None
  hdError (x:_) = Some x
  |])

testHdError1 :: HdError '[1,2] :~: Some 1
testHdError1 = Refl

testHdError2 :: HdError '[ '[1], '[2] ] :~: Some '[1]
testHdError2 = Refl

$(singletons [d|
  filterEvenGt7 :: [Nat] -> [Nat]
  filterEvenGt7 = filter (\x -> evenb x && x > 7)
  |])

testFilterEvenGt7_1 :: FilterEvenGt7 (Map LitSym0 '[1,2,6,9,10,3,12,8]) :~: Map LitSym0 '[10,12,8]
testFilterEvenGt7_1 = Refl

testFilterEvenGt7_2 :: FilterEvenGt7 (Map LitSym0 '[5,2,6,19,129]) :~: '[]
testFilterEvenGt7_2 = Refl

$(singletons [d|
  oddb :: Nat -> Bool
  oddb x = not (evenb x)
  |])

testPartition1 :: Partition OddbSym0 (Map LitSym0 '[1,2,3,4,5]) :~:
                  '(Map LitSym0 '[1,3,5], Map LitSym0 '[2,4])
testPartition1 = Refl

testPartition2 :: Partition (ConstSym1 False) (Map LitSym0 '[5,9,0]) :~:
                  '( '[], Map LitSym0 '[5,9,0])
testPartition2 = Refl

mapApp :: forall (x :: Type) (y :: Type)
                 (f :: x ~> y) (l1 :: [x]) (l2 :: [x]).
          Sing f -> Sing l1 -> Sing l2
       -> Map f (l1 ++ l2) :~: Map f l1 ++ Map f l2
mapApp _ SNil _ = Refl
mapApp sF (SCons _ sls1) sl2 | Refl <- mapApp sF sls1 sl2
                             = Refl

mapRev :: forall (x :: Type) (y :: Type)
                 (f :: x ~> y) (l :: [x]).
          Sing f -> Sing l
       -> Map f (Rev l) :~: Rev (Map f l)
mapRev _ SNil = Refl
mapRev sF (SCons sl sls) | Refl <- mapRev sF sls
                         , Refl <- mapApp sF (sRev sls) (SCons sl SNil)
                         = Refl

type Foo n = '[n,n,n]
$(genDefunSymbols [''Foo])

testConcatMap1 :: ConcatMap FooSym0 '[1,5,4] :~: '[1,1,1,5,5,5,4,4,4]
testConcatMap1 = Refl

$(singletons [d|
  fold :: (x -> y -> y) -> [x] -> y -> y
  fold _ []    b = b
  fold f (h:t) b = f h (fold f t b)

  foldLength :: [x] -> Nat
  foldLength l = fold (const S) l Z

  foldMap :: (x -> y) -> [x] -> [y]
  foldMap f l = fold ((:).f) l []
  |])

testFoldLength1 :: FoldLength '[4,7,0] :~: Lit 3
testFoldLength1 = Refl

foldLengthCorrect :: forall (x :: Type) (l :: [x]).
                     Sing l
                  -> FoldLength l :~: Length l
foldLengthCorrect SNil = Refl
foldLengthCorrect (SCons _ sls) | Refl <- foldLengthCorrect sls
                                = Refl

foldMapCorrect :: forall (x :: Type) (y :: Type) (f :: x ~> y) (l :: [x]).
                  Sing f -> Sing l
               -> FoldMap f l :~: Map f l
foldMapCorrect _  SNil = Refl
foldMapCorrect sF (SCons _ sls) | Refl <- foldMapCorrect sF sls
                                = Refl

uncurryCurry :: forall (x :: Type) (y :: Type) (z :: Type)
                       (f :: x ~> y ~> z) (xx :: x) (yy :: y).
                Sing f -> Sing xx -> Sing yy
             -> Curry (UncurrySym1 f) xx yy :~: f @@ xx @@ yy
uncurryCurry _ _ _ = Refl

curryUncurry :: forall (x :: Type) (y :: Type) (z :: Type)
                       (f :: (x, y) ~> z) (p :: (x, y)).
                Sing f -> Sing p
             -> Uncurry (CurrySym1 f) p :~: f @@ p
curryUncurry _ (STuple2 {}) = Refl
