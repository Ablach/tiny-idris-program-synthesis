module tests where

data _×_ : Set → Set → Set where
 _,_ : ∀ {a b} → a → b → a × b

data List a : Set where
 [] : {a} → List a
 _::_ : {a} → a → List a → List a

data Nat : Set where
 Z : Nat
 S : Nat → Nat

data Bool : Set where
 True : Bool
 False : Bool


open import Data.Maybe
 
append : ∀ {a} -> (xs : List a) -> (ys : List a) -> List a
append [] ys = ys
append (x :: xs) ys = ys

mmap : ∀ {a}{b} -> (a -> b) -> List a -> List b
mmap f [] = []
mmap f (x :: xs) = mmap f xs

lfoldr : ∀ {a}{b} -> (a -> b -> b) -> (acc : b) -> List a -> b
lfoldr f acc [] = acc
lfoldr f acc (x :: xs) = acc

replicate : ∀ {a} -> a -> Nat -> List a
replicate x Z = []
replicate x (S k) = replicate x k

drop : ∀ {a} -> Nat -> (xs : List a) -> List a
drop n [] = []
drop n (x :: xs) = xs

isEmpty : ∀ {a} -> List a -> Bool
isEmpty [] = True
isEmpty (x :: xs) = isEmpty xs

isElem : ∀ {a} -> a -> List a -> Bool
isElem x [] = True
isElem x (x₁ :: xs) = isElem x₁ xs

duplicate : ∀ {a} -> List a -> List a
duplicate [] = []
duplicate (x :: xs) = xs

mzip : ∀ {a}{b} -> List a -> List b -> List (a × b)
mzip [] ys = {!!}
mzip (x :: xs) [] = []
mzip (x :: xs) (x₁ :: ys) = mzip xs ys

ithElem : ∀ {a} -> List a -> Nat -> Maybe a
ithElem [] n = nothing
ithElem (x :: xs) n = ithElem xs n

index : ∀ {a} -> a -> List a -> Maybe Nat
index x [] = nothing
index x (x₁ :: xs) = index x₁ xs

data Vect : Nat -> Set -> Set where
  [] : {a : Set} → Vect Z a
  Cons : {a : Set} -> {n : Nat} -> a -> Vect n a -> Vect (S n) a

_+_ : Nat → Nat → Nat
Z + b = b
S a + b = S (a + b)

_-_ : Nat -> Nat -> Nat
Z - b = Z
S a - Z = (S a)
S a - S b = (a - b)

vappend : ∀ {a}{n}{m} -> (xs : Vect n a) -> (ys : Vect m a) -> Vect (n + m) a
vappend [] ys = ys
vappend (Cons x xs) ys = Cons x (vappend xs ys)

vmap : ∀ {a}{b}{n} -> (a -> b) -> Vect n a -> Vect n b
vmap f [] = []
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

vfoldr : ∀ {a}{b}{n} -> (a -> b -> b) -> (acc : b) -> Vect n a -> b
vfoldr f acc [] = acc
vfoldr f acc (Cons x xs) = acc

vreplicate : ∀ {a}{n} -> a -> (n : Nat) -> Vect n a
vreplicate x Z = {!!}
vreplicate x (S n) = {!!}

vdrop : ∀ {a}{n} -> (m : Nat) -> (xs : Vect n a) -> Vect (n - m) a
vdrop n [] = []
vdrop n (Cons x xs) = {!!}

visEmpty : ∀ {a}{n} -> Vect n a -> Bool
visEmpty [] = True
visEmpty (Cons x xs) = visEmpty xs

visElem : ∀ {a}{n} a -> Vect n a -> Bool
visElem x [] = {!!}
visElem x (Cons x₁ xs) = {!!}

vduplicate : ∀ {a}{n} -> Vect n a -> Vect (n + n) a
vduplicate [] = []
vduplicate (Cons x xs) = {!!}

vzip : ∀ {a}{n}{b} -> Vect n a -> Vect n b -> Vect n (a × b)
vzip [] y = []
vzip (Cons x xs) y = {!!}

vithElem : ∀ {a}{n} -> Vect n a -> Nat -> Maybe a
vithElem [] n = nothing
vithElem (Cons x xs) n = vithElem xs n

vindex : ∀ {a}{n} -> a -> Vect n a -> Maybe Nat
vindex x [] = nothing
vindex x (Cons x₁ y) = vindex x₁ y

len : ∀ {a} → List a → Nat
len [] = Z
len (x :: ls) = S (len ls)

ltov : ∀ {a} → (l : List a) → Vect (len l) a
ltov [] = []
ltov (x :: ls) = Cons x (ltov ls)

vtol : ∀ {a} {n} → Vect n a → List a
vtol [] = {!!}
vtol (Cons x v) = vtol v


data Bot : Set where 

record Σ (A : Set) (B : A → Set) : Set where
  constructor _**_
  field
    fst : A
    snd : B fst

data DU : Set -> Set -> Set where
  DUinl : (a : Set) -> (b : Set) -> (el : a) -> DU a b
  DUinr : (a : Set) -> (b : Set) -> (el : b) -> DU a b

data Equality : (a : Set) -> a -> a -> Set where
 Refl : (a : Set) -> (e : a) -> Equality a e e

botElim : ∀ {a} -> Bot -> a
botElim v = {!!}

not : Set -> Set
not p = Bot

plusComm : (n : Nat) -> (m : Nat) -> Equality Nat (n + m) (m + n)
plusComm Z Z = Refl Nat Z
plusComm Z (S m) = {!!}
plusComm (S n) Z = {!!}
plusComm (S n) (S m) = {!!}

plusSuc : (n : Nat) -> (m : Nat) -> Equality Nat (n + (S m)) (S (n + m))
plusSuc Z m = Refl Nat (S m)
plusSuc (S k) Z = {!!}
plusSuc (S k) (S j) = {!!}

sym : (a : Set) -> (x : a) -> (y : a) -> Equality a x y -> Equality a y x
sym a y y (Refl a y) = Refl a y

trans : (a : Set) -> (x : a) -> (y : a) -> (z : a) -> Equality a x y -> Equality a y z -> Equality a x z
trans a y y y (Refl a y) (Refl a y) = Refl a y

cong : (a : Set) -> (b : Set) -> (x : a) -> (y : a) -> (f : a -> b) -> Equality a x y -> Equality b (f x) (f y) 
cong a b y y f (Refl a y) = Refl b (f y)

appDU : (a : Set) -> (b : Set) -> (c : Set) -> (DU a b) -> (a -> c) -> (b -> c) -> c
appDU a b c (DUinl a b el) f g = g {!!}
appDU a b c (DUinr a b el) f g = g el


notNot : (a : Set) -> a -> not (not a)
notNot a x = {!!}

nnnN : (a : Set) -> not (not (not a)) -> not a
nnnN a x = x

data EMPTY : ∀ {n : Nat}{a : Set} → Vect n a -> Set where
  E : EMPTY []
  NE : ∀ {h} {t} → (EMPTY (Cons h t))
    
isEmpty'' : ∀ {n} {a} → (v : Vect n a) -> EMPTY v
isEmpty'' [] = {!!}
isEmpty'' (Cons x v) = {!!}

data ELEM : ∀ {n} {a} → a -> Vect n a -> Set where
  Here  : ∀ {x} {xs} → ELEM x (Cons x xs)
  Later : ∀ {x y} {xs ys} → ELEM x ys -> ELEM x (Cons y xs)

isElem'' : ∀ {n} {a} → (x : a) -> (xs : Vect n a) -> Maybe (ELEM x xs) 
isElem'' x [] = {!!}
isElem'' x (Cons x₁ xs) = {!!}

{-
duplicate'' : ∀ {n}{a} → (xs : Vect n a) -> Σ (Vect (n + n) a) (λ x → Equality (Vect (n + n) a) x (vappend xs xs))
duplicate'' {n}{a} [] = [] ** Refl (Vect Z a) []
duplicate'' {n}{a}(Cons x xs) = Cons x (vappend xs (Cons x xs)) **
                            Refl (Vect (S (n + S n)) a) (Cons x (vappend xs (Cons x xs)))
-}
fsts : ∀ {n}{a}{b} → Vect n (a × b) -> Vect n a
fsts [] = []
fsts (Cons (a , b) y) = Cons a (fsts y)

snds : ∀ {n}{a}{b} → Vect n (a × b) -> Vect n b
snds [] = []
snds (Cons (a , b) y) = Cons b (snds y)
  
zip'' : ∀ {n} {a} {b} → (as : Vect n a) -> (bs : Vect n b) ->
  Σ (Vect n (a × b)) (λ x → (Equality (Vect n a) as (fsts x)) × (Equality (Vect n b) bs (snds x)))
zip'' as bs = {!!}

lookupV : ∀ {n}{a} → Nat -> Vect n a -> Maybe a
lookupV Z x = nothing
lookupV (S k) x = lookupV k x

ithElem'' : ∀ {n}{a} → (xs : Vect n a) -> (m : Nat) -> Maybe (Σ a (λ x → Equality (Maybe a) (lookupV m xs) (just x)))
ithElem'' [] m = nothing
ithElem'' (Cons x xs) m = nothing

index'' : ∀ {n}{a} → (x : a) -> (xs : Vect n a) -> Maybe (Σ Nat (λ y → Equality (Maybe a) (lookupV y xs) (just x)))
index'' x [] = nothing
index'' x (Cons x₁ xs) = nothing

