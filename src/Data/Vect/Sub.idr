module Data.Vect.Sub

import public Data.Vect

%default total
%access export

||| A Sublist is a list of proofs that each element in 'subXs' is an element of 'xs'
public export
data Sub : (subXs : Vect n a) -> (xs : Vect m a) -> Type where
  Nil : Sub [] xs
  (::) : Elem x ys -> Sub xs ys -> Sub (x::xs) ys

%name Sub es,xs,ys,zs


||| If list is a subset of another list, it can be a sublist of a longer list
expandSub : Sub xs ys -> Sub xs (y::ys)
expandSub [] = Nil
expandSub (y :: z) = There y :: expandSub z

||| Find the corresponding location of an element thanks to a sublist
public export
mapElem : Elem x xs -> {auto prf: Sub xs ys} -> Elem x ys
mapElem Here {prf = []} impossible
mapElem (There _) {prf = []} impossible
mapElem Here {prf = z :: es} = z
mapElem (There later) {prf = (z :: es)} = mapElem later {prf = es}

||| A list is its own sub
%hint
reflSub : Sub xs xs
reflSub {xs = []} = []
reflSub {xs = (x :: xs)} = Here :: expandSub reflSub

||| 'Sub' is transitive
transitivity : Sub xs ys -> Sub ys zs -> Sub xs zs
transitivity [] y = []
transitivity (x :: es) es' = mapElem x {prf = es'} :: transitivity es es'

Uninhabited (Sub (x::xs) []) where

  uninhabited (Here :: _) impossible
  uninhabited ((There _) :: _) impossible


||| A non empty list is not a 'Sub' of the empty list
nonEmptyNotSubNil : (x : a) -> Not (Sub (x::xs) [])
nonEmptyNotSubNil _ = absurd

noElemImpliesNoSub : (contra : Elem x ys -> Void) -> Not (Sub (x :: xs) ys)
noElemImpliesNoSub contra (prf :: es) = contra prf

noSubExpand : (contra : Sub xs ys -> Void) -> Not (Sub (x :: xs) ys)
noSubExpand contra (x :: es) = contra es

||| Decide whether the sublist property holds for two vectors
decSub : DecEq a => (xs : List a) -> (ys : List a) -> Dec (Sub xs ys)
decSub [] ys = Yes []
decSub (x :: xs) ys with (isElem x ys)
  | (Yes prfHead) with (decSub xs ys)
    | (Yes prfTail) = Yes (prfHead :: prfTail)
    | (No contra) = No (noSubExpand contra)
  | (No contra) = No (noElemImpliesNoSub contra)

