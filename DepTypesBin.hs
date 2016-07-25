{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, MultiParamTypeClasses, FlexibleInstances, GADTs, TypeFamilies, UndecidableInstances, TypeOperators #-}

module DepTypesBin where

data T = T deriving (Show, Eq)
data F = F deriving (Show, Eq)

data HNil = HNil deriving (Show, Eq)
data HCons a b = HCons a b deriving (Show, Eq)

class Nat n where
  toInt :: n -> Integer
  el :: n

instance Nat T where
  toInt _ = 1
  el = T

instance Nat F where
  toInt _ = 0
  el = F

instance Nat HNil where
  toInt _ = 0
  el = HNil
--instance Nat N0 where
--  toInt _ = 0
--  el = HCons F HNil
--
--instance Nat N1 where
--  toInt _ = 1
--  el = HCons T HNil

instance (Nat n) => Nat (HCons T n) where
  toInt (HCons T n) = 1 + 2 * toInt n
  el = HCons T (el :: n)

instance (Nat n) => Nat (HCons F n) where
  toInt (HCons F n) = 0 + 2 * toInt n
  el = HCons F (el :: n)

type N0 = HCons F HNil
type N1 = HCons T HNil
type N2 = N1 :+ N1
type N3 = N1 :+ N2
type N4 = N2 :+ N2
type N5 = N4 :+ N1
type N6 = N4 :+ N2
type N7 = N4 :+ N3
type N8 = N4 :+ N4
type N9 = N4 :+ N5
type N10 = N4 :+ N6
type N16 = N8 :+ N8

type family a :& b where
  T :& T = T
  a :& b = F

type family a :== b where
  T :== T = T
  F :== F = T
  HNil :== HNil = T
  HCons c1 l :== HCons c2 k = (c1 :== c2) :& (l :== k)
  a :== b = F

type family a :+ b where
  N0 :+ b = b
  a :+ N0 = a
  N1 :+ N1 = HCons F N1
  N1 :+ HCons F l = HCons T l
  N1 :+ HCons T l = HCons F (N1 :+ l)
  HCons F l :+ N1 = HCons T l
  HCons T l :+ N1 = HCons F (N1 :+ l)
  HCons T l :+ HCons F k = HCons T (l :+ k)
  HCons F l :+ HCons T k = HCons T (l :+ k)
  HCons F l :+ HCons F k = HCons F (l :+ k)
  HCons T l :+ HCons T k = HCons F (AddBin l k T)

type family AddBin a b c where
  AddBin N0 N0 c = HCons c HNil
  AddBin a N0 c = a :+ HCons c HNil 
  AddBin N0 b c = b :+ HCons c HNil
  AddBin N1 N1 T = HCons T (HCons T HNil)
  AddBin v1 v2 F = v1 :+ v2
  AddBin (HCons T l) (HCons T k) T = HCons T (AddBin l k T)
  AddBin (HCons F l) (HCons T k) T = HCons F (AddBin l k T)
  AddBin (HCons T l) (HCons F k) T = HCons F (AddBin l k T) 
  AddBin (HCons F l) (HCons F k) T = HCons T (l :+ k)

type family Decr a where
  Decr N1 = N0
  Decr (HCons T l) = Cleanup (HCons F l)
  Decr (HCons F l) = Cleanup (HCons T (Decr l))

type family IfThenElse a b c where
  IfThenElse T b c = b
  IfThenElse F b c = c 

type family AllFalse a where
  AllFalse (HCons T l) = F
  AllFalse (HCons F HNil) = T
  AllFalse (HCons F l) = AllFalse l

type family Cleanup a where
  Cleanup N0 = N0
  Cleanup N1 = N1
  Cleanup (HCons F N0) = N0
  Cleanup (HCons T N0) = N1
  Cleanup (HCons T a) = (HCons T (IfThenElse (AllFalse a) HNil (Cleanup a)))
  Cleanup (HCons F a) = (HCons F (IfThenElse (AllFalse a) HNil (Cleanup a)))

type family a :>> b where
  N0 :>> b = N0
  a :>> N0 = a
  a :>> N1 = HCons F a
  a :>> b = HCons F (a :>> Decr b)

type family a :* b where
  a :* N0 = N0
  N0 :* b = N0
  a :* N1 = a
  N1 :* b = b
  a :* b = MultBin a b N0

type family MultBin a b p where
  MultBin N0 k p = N0
  MultBin N1 k p = k :>> p
  MultBin (HCons T l) k p = (k :>> p) :+ MultBin l k (p :+ N1)
  MultBin (HCons F l) k p = (MultBin l k (p :+ N1))

type family Length a where
  Length N0 = N1
  Length (HCons a l) = N1 :+ Length l

type family a :^ b where
  a :^ N0 = N1
  N0 :^ b = N0
  a :^ N1 = a
  a :^ HCons F l = (a :* a) :^ l
  a :^ HCons T l = a :* ((a :* a) :^ l)

test :: Bool
test = and (testSum ++ testCleanup ++ testDecr ++ testShift ++ testProduct ++ testPow)

testSum, testCleanup, testDecr, testShift, testProduct, testPow :: [Bool]
testSum = [
    0 == toInt (el :: N0)
  , 0 == toInt (el :: (N0 :+ N0))
  , 1 == toInt (el :: (N0 :+ N1))
  , 1 == toInt (el :: (N1 :+ N0))
  , 2 == toInt (el :: (N1 :+ N1))
  , 2 == toInt (el :: (N2 :+ N0))
  , 2 == toInt (el :: (N0 :+ N2))
  , 3 == toInt (el :: (N1 :+ N1 :+ N1))
  , 8 == toInt (el :: N8)
  , 10 == toInt (el :: N5 :+ N5)
  , 12 == toInt (el :: N6 :+ N6)
  , 12 == toInt (el :: N5 :+ N7)
  , 14 == toInt (el :: N7 :+ N7)
  , 14 == toInt (el :: N6 :+ N8)
  , 14 == toInt (el :: N5 :+ N9)
  , 16 == toInt (el :: (N8 :+ N8))
  , 31 == toInt (el :: (N1 :+ N2 :+ N4 :+ N8 :+ N16)) ]

testCleanup = [
    (el :: N3) == (el :: Cleanup N3)
  , (el :: N3) == (el :: Cleanup (HCons T (HCons T (HCons F (HCons F HNil))))) ]

testDecr = [
      0 == toInt (el :: Decr N1)
    , 1 == toInt (el :: Decr N2)
    , 1 == toInt (el :: Decr (Decr N3))
    , 4 == toInt (el :: Decr (N4 :+ N1))
  ]

testShift = [
    0 == toInt (el :: (N0 :>> N0))
  , 0 == toInt (el :: (N0 :>> N1))
  , 0 == toInt (el :: (N0 :>> N2))
  , 1 == toInt (el :: (N1 :>> N0))
  , 2 == toInt (el :: (N2 :>> N0))
  , 8 == toInt (el :: (N2 :>> N2))
  , 1024 == toInt (el :: (N2 :>> (N8 :+ N1))) ]

testProduct = [
    0 == toInt (el :: N0 :* N0)
  , 0 == toInt (el :: N0 :* N1)
  , 0 == toInt (el :: N0 :* N2)
  , 0 == toInt (el :: N2 :* N0)
  , 1 == toInt (el :: N1 :* N1)
  , 2 == toInt (el :: N1 :* N2)
  , 2 == toInt (el :: N2 :* N1)
  , 2^4 == toInt (el :: ((N2 :* N2) :* N2) :* N2)
  , 2^4 == toInt (el :: (N2 :* N2) :* (N2 :* N2))
  , 2^4 == toInt (el :: (N2 :* (N2 :* (N2 :* N2))))
  , 2^5 == toInt (el :: (N2 :* (N2 :* (N2 :* N2))) :* N2)
  ]

testPow = [
    1 == toInt (el :: N0 :^ N0)
  , 1 == toInt (el :: N1 :^ N0)
  , 1 == toInt (el :: N2 :^ N0)
  , 1 == toInt (el :: N1 :^ N2)
  , 0 == toInt (el :: N0 :^ N1)
  , 0 == toInt (el :: N0 :^ N2)
  , 4 == toInt (el :: N2 :^ N2)
  , 4^2 == toInt (el :: N4 :^ N2)
  , 2^4 == toInt (el :: N2 :^ N4)
  , 2^10 == toInt (el :: N2 :^ N10)]

main :: IO ()
main = print $ "Test: " ++ if test then "Success!" else "Fail!"
