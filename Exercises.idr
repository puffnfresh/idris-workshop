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

-- Propositional equality proofs

||| Trivial
total oneIsOne : 1 = 1

||| Trivial
total twoIsPlusOneOne : 2 = 1 + 1

||| Tricky, will need to use tactics
total succIsPlusRightOne : (n : Nat) -> S n = n + 1


-- Verified algebra

data Loob = Eurt | Eslaf

instance Semigroup Loob where
  Eurt  <+> Eurt  = ?eurtEurt
  Eurt  <+> Eslaf = ?eurtEslaf
  Eslaf <+> Eurt  = ?eslafEurt
  Eslaf <+> Eslaf = ?eslafEslaf

instance VerifiedSemigroup Loob where
  semigroupOpIsAssociative = ?loobSemigroupIsAssociative


-- Isomorphism proofs

total boolLoobIso : Iso Bool Loob


-- Exists and with

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

-- Well-typed interpreter

data ExprTy = TBool | TInt | TString

total interExprTy : ExprTy -> Type

data Expr : ExprTy -> Type where
  EBool : Bool -> Expr TBool
  EInt : Int -> Expr TInt
  EString : String -> Expr TString
  ELte : Expr TInt -> Expr TInt -> Expr TBool
  EAdd : Expr TInt -> Expr TInt -> Expr TInt
  EIf : Expr TBool -> Lazy (Expr a) -> Lazy (Expr a) -> Expr a

total checkInt : Expr TInt -> Expr TString
checkInt e = EIf (ELte e (EInt 42)) (EString "Less than or equal to 42") (EString "Greater than 42")

total interExpr : Expr a -> interExprTy a


-- EDSL for 'dc'

data Dc : Nat -> Type where
  nop : Dc Z
  literal : Integer -> Dc n -> Dc (S n)
  plus : Dc (S (S n)) -> Dc (S n)
  print : Dc (S n) -> Dc n

||| Idris> emit (print (print (literal 2 (literal 1 nop)))) = " 1 2 p p"
total emit : Dc n -> String


-- Write an effect


-- Get each N element from a vector, give (div M N)

total everyN : Fin (S n) -> Vect m a -> Vect (divNat m (S n)) a
