module Tests

%hide List
%hide Nat
%hide Pair 
%hide DPair

data Pair : Type -> Type -> Type where
  MkPair : (x : a) -> (y : b) -> Pair a b

data DPair : (a : Type) -> (a -> Type) -> Type where
 MkDPair : (e : a) -> (pf : p e) -> DPair a p

data List : Type -> Type where
  LNil  : List a
  LCons : a -> List a -> List a 

data Nat : Type where
  Z : Nat
  S : Nat -> Nat

(+) : Nat -> Nat -> Nat
Z + m = m
(S n) + m = S (n + m)

minus : Nat -> Nat -> Nat
minus Z m = Z
minus n Z = n
minus (S n) (S m) = minus n m

append : (xs : List a) -> (ys : List a) -> List a
append xs ys = ?a

map: (a -> b) -> List a -> List b


foldr : (a -> b -> b) -> (acc : b) -> List a -> b


replicate : a -> Nat -> List a


drop : Nat -> (xs : List a) -> List a


isEmpty : List a -> Bool


isElem :  a -> List a -> Bool


duplicate : List a -> List a


zip : List a -> List b -> List (Pair a b)


ithElem : List a -> Nat -> Maybe a


index : a -> List a -> Maybe Nat


data Vect : Nat -> Type -> Type where
  VNil : Vect Z a
  VCons : a -> Vect n a -> Vect (S n) a

append' : (xs : Vect n a) -> (ys : Vect m a) -> Vect (n + m) a


map' : (a -> b) -> Vect n a -> Vect n b


foldr' : (a -> b -> b) -> (acc : b) -> Vect n a -> b


replicate' : a -> (n : Nat) -> Vect n a

drop' : (m : Nat) -> (xs : Vect n a) -> Vect (minus n m) a


isEmpty' : Vect n a -> Bool


isElem' :  a -> Vect n a -> Bool


duplicate' : Vect n a -> Vect (n + n) a


zip' : Vect n a -> Vect n b -> Vect n (Pair a b)


ithElem' : Vect n a -> Nat -> Maybe a


index' : a -> Vect n a -> Maybe Nat


len : List a -> Nat
len LNil = Z
len (LCons x y) = S (len y)

listToVec : (ls : List a) -> Vect (len ls) a
listToVec LNil = VNil
listToVec (LCons x y) = VCons x (listToVec y)

vecToList : Vect n a -> List a
vecToList VNil = LNil
vecToList (VCons x y) = LCons x (vecToList y)

data Bot : Type where 

data DU : Type -> Type -> Type where
  DUinl : (a : Type) -> (b : Type) -> (el : a) -> DU a b
  DUinr : (a : Type) -> (b : Type) -> (el : b) -> DU a b

pSym : Pair a b -> Pair b a
--pSym (x, y) = (y, x)


duSym : DU a b -> DU b a
duSym (DUinl _ _ el) = DUinr b a el
duSym (DUinr _ _ el) = DUinl b a el



data Equality : (a : Type) -> a -> a -> Type where
 Refl : (a : Type) -> (e : a) -> Equality a e e

botElim : Bot -> a

not : Type -> Type
not p = Bot

plusComm : (n : Nat) -> (m : Nat) -> Equality Nat (n + m) (m + n)


plusSuc : (n : Nat) -> (m : Nat) -> Equality Nat ((+) n (S m)) (S ((+) n m))


sym : (a : Type) -> (x : a) -> (y : a) -> Equality a x y -> Equality a y x


trans : (a : Type) -> (x : a) -> (y : a) -> (z : a) -> Equality a x y -> Equality a y z -> Equality a x z


cong : (a : Type) -> (b : Type) -> (x : a) -> (y : a) -> (f : a -> b) -> Equality a x y -> Equality b (f x) (f y) 


appDU : (a : Type) -> (b : Type) -> (c : Type) -> (DU a b) -> (a -> c) -> (b -> c) -> c

notNot : (a : Type) -> a -> not (not a)


nnnN : (a : Type) -> not (not (not a)) -> not a


------------------------------------------------------------------

data EMPTY : Vect n a -> Type where
  E : EMPTY VNil
  NE : (EMPTY (VCons h t))
    
isEmpty'' : (v : Vect n a) -> EMPTY v



data ELEM :  a -> Vect n a -> Type where
  Here  : ELEM x (VCons x xs)
  Later : ELEM x ys -> ELEM x (VCons y xs)

isElem'' :  (x : a) -> (xs : Vect n a) -> Maybe (ELEM x xs) 


duplicate'' : (xs : Vect n a) -> 
 (DPair (Vect (n + n) a) 
        (\ ys => Equality (Vect (n + n) a) ys (append' xs xs)))


fsts : Vect n (Pair a b) -> Vect n a


snds : Vect n (Pair a b) -> Vect n b


zip'' : (as : Vect n a) -> (bs : Vect n b) -> 
  (DPair (Vect n (Pair a b)) 
         (\ ys => Pair (Equality (Vect n a) (fsts ys) as) 
                       (Equality (Vect n b) (snds ys) bs)))


lookupV : Nat -> Vect n a -> Maybe a


ithElem'' : (xs : Vect n a) -> (m : Nat) -> 
   Maybe (DPair a (\ x => Equality (Maybe a) (lookupV m xs) (Just x)) )


index'' : (x : a) -> (xs : Vect n a) ->
   Maybe (DPair Nat (\ m => Equality (Maybe a) (lookupV m xs) (Just x)) )




