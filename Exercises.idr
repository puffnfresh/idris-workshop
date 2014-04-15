module Exercises

import Control.Isomorphism
import Data.Vect

{-

## Assumptions

Bit of experience with Haskell

## Totality

Everything is a term

-}

total typeAndTerm : Type

{-

Termination

Evaluation is normalisation (Church-Rosser theorem)

## Dependent functions

Parametric types

-}

total theConst : (a : Type) -> (b : Type) -> a -> b -> a

{-

Problem with type casing

## Interactive

C-c C-l

C-c C-h C-a
C-c C-d

C-c C-s
C-c C-a

-}


-- printf, from "Cayenne - a language with dependent types" http://fsl.cs.illinois.edu/images/5/5e/Cayenne.pdf

data Format = FInt Format
            | FString Format
            | FOther Char Format
            | FEnd

||| Idris> format (unpack "%d %s %d") = FInt (FOther ' ' (FString (FOther ' ' (FInt FEnd))))
total format : List Char -> Format

||| Idris> PrintfType (FInt (FOther ' ' (FString (FOther ' ' (FInt FEnd))))) = (Int -> String -> Int -> String)
total PrintfType : Format -> Type

||| Type depends on format String
total printf : (fmt : String) -> PrintfType (format (unpack fmt))

-- Verified algebra

||| Define semigroupOpIsAssociative in the VerifiedSemigroup instance
data X = MkX

instance Semigroup X where
  MkX <+> MkX = MkX

instance VerifiedSemigroup X where

-- Propositional equality proofs

||| Trivial
total oneIsOne : 1 = 1

||| Trivial
total twoIsPlusOneOne : 2 = 1 + 1

||| Tricky, will need to use tactics
total succIsPlusRightOne : (n : Nat) -> S n = n + 1


-- Isomorphism proofs

total maybeBoolIso : Iso Bool (Maybe ())


-- Exists

total filterNot : Vect n a -> (a -> Bool) -> (m ** Vect m a)


-- Give evidence element is in data structure

||| Look at Data.Vect in base
total without : {x : a} -> (xs : Vect (S n) a) -> Elem x xs -> Vect n a


-- Get each 3 combination from a List

||| Extra tricky: Make the type: Vect (div (fact n) (6 * fact (n - 6))) (Vect 3 a)
total chooseThree : List a -> List (Vect 3 a)
chooseThree l = choose' l []
  where choose' : List a -> List a -> List (Vect 3 a)


-- Division by 1 is identity

total repeatedSubtraction : Nat -> Nat -> Nat -> Nat
repeatedSubtraction Z        centre right = Z
repeatedSubtraction (S left) centre right =
  if lte centre right then
    Z
  else
    S (repeatedSubtraction left (centre - (S right)) right)

total divNatt : Nat -> Nat -> Nat
divNatt left Z         = S left
divNatt left (S right) = repeatedSubtraction left left right

||| Trivial
total divZeroSucc : (n : Nat) -> div n 0 = S n

||| Tricky, will need to use an inductive hypothesis
total divvOne : (n : Nat) -> repeatedSubtraction n n 0 = n

||| Will need to reuse the above
total divOne : (n : Nat) -> divNatt n 1 = n


-- EAdd EBool EBool -> _|_


-- Even Odd

data Even : Nat -> Type where
  evenZ : Even Z
  evenS : Even n -> Even (S (S n))

data Odd : Nat -> Type where
  oddO : Odd (S Z)
  oddS : Odd n -> Odd (S (S n))

total ee : Even n -> Even m -> Even (n + m)

total eo : Even n -> Odd m -> Odd (n + m)

total oe : Odd n -> Even m -> Odd (n + m)

total oo : Odd n -> Odd m -> Even (n + m)


-- Write an effect


-- Get each N element from a vector, give (div M N)

total everyN : Fin (S n) -> Vect m a -> Vect (divNat m (S n)) a


-- EDSL for dc
