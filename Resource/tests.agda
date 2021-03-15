module tests where

data List a : Set where
 [] : {a} → List a
 _::_ : {a} → a → List a → List a

data Nat : Set where
 Z : Nat
 S : Nat → Nat

data Bool : Set where
 True : Bool
 False : Bool

open import Data.Product
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
