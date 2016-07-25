{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, MultiParamTypeClasses, FlexibleInstances, GADTs, TypeFamilies, UndecidableInstances, TypeOperators #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}

module DepTypes where

data Z = Z deriving Show
data S n = S n deriving Show

class Nat n where
  toInt :: n -> Integer
  element :: n

instance Nat Z where
  toInt _ = 0
  element = Z
instance (Nat n) => Nat (S n) where
  toInt (S n) = 1 + toInt n
  element = S (element :: n)

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2
type N4 = S N3
type N5 = S N4
type N6 = S N5
type N7 = S N6
type N8 = S N7
type N9 = S N8
type N10 = S N9

type family a + b where
  a + Z = a
  n + S m = S n + m


type family a :* b where
  a :* Z = Z
  a :* S Z = a
  n :* S m = n + (n :* m)

type family a ^ b where
  Z ^ m = Z
  n ^ Z = N1
  n ^ S m = n :* (n ^ m)





--main :: IO ()
--main = print (toInt (Suc Zero))
