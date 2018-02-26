module Data.Sub

import Data.List

%default total
%access export

||| A Sublist is a list of proofs that each element in 'subXs' is an element of 'xs'
public export
data Sub : (subXs : List a) -> (xs : List a) -> Type where
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

||| A non empty list is not a 'Sub' of the empty list
nonEmptyNotSubNil : Not (Sub (x::xs) [])
nonEmptyNotSubNil = \es => case es of
                                (Here :: _) impossible
                                ((There _) :: _) impossible
