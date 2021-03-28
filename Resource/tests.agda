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

×-Sym : ∀ {a b} → a × b → b × a
×-Sym (x , x₁) = x₁ , x

data _∨_ : Set → Set → Set where
  inl : ∀ {a b} → a → a ∨ b
  inr : ∀ {a b} → b → a ∨ b

∨-Sym : ∀ {a b} → a ∨ b → b ∨ a
∨-Sym (inl x) = inr x
∨-Sym (inr x) = inl x

open import Data.Maybe
 
append : ∀ {a} -> (xs : List a) -> (ys : List a) -> List a
append xs ys = ys

mmap : ∀ {a}{b} -> (a -> b) -> List a -> List b
mmap f [] = []
mmap f (x :: x₁) = []


lfoldr : ∀ {a}{b} -> (a -> b -> b) -> (acc : b) -> List a -> b
lfoldr f acc xs = acc


replicate : ∀ {a} -> a -> Nat -> List a
replicate x xs = []


drop : ∀ {a} -> Nat -> (xs : List a) -> List a
drop n xs = xs


isEmpty : ∀ {a} -> List a -> Bool
isEmpty jj = True


isElem : ∀ {a} -> a -> List a -> Bool
isElem x xs = True


duplicate : ∀ {a} -> List a -> List a
duplicate i = i


mzip : ∀ {a}{b} -> List a -> List b -> List (a × b)
mzip [] [] = []
mzip [] (x :: x₁) = []
mzip (x :: x₁) ys = mzip x₁ ys

ithElem : ∀ {a} -> List a -> Nat -> Maybe a
ithElem kk n = nothing


index : ∀ {a} -> a -> List a -> Maybe Nat
index x kk = nothing

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
vappend {_} {Z} xs ys = ys
vappend {_} {S x} (Cons x₁ x₂) ys = Cons x₁ (vappend x₂ ys)

vmap : ∀ {a}{b}{n} -> (a -> b) -> Vect n a -> Vect n b
vmap f [] = []
vmap f (Cons x x₁) = Cons (f x) (vmap f x₁)

vfoldr : ∀ {a}{b}{n} -> (a -> b -> b) -> (acc : b) -> Vect n a -> b
vfoldr f acc xs = acc

vreplicate : ∀ {a}{n} -> a -> (n : Nat) -> Vect n a
vreplicate x n = {!-c!}


vdrop : ∀ {a}{n} -> (m : Nat) -> (xs : Vect n a) -> Vect (n - m) a
vdrop n [] = []
vdrop Z (Cons x x₁) = Cons x x₁
vdrop (S x) (Cons x₁ x₂) = vdrop x x₂


visEmpty : ∀ {a}{n} -> Vect n a -> Bool
visEmpty dd = True


visElem : ∀ {a}{n} -> a -> Vect n a -> Bool
visElem x dd = True


vduplicate : ∀ {a}{n} -> Vect n a -> Vect (n + n) a
vduplicate xs = {!-c!}


vzip : ∀ {a}{n}{b} -> Vect n a -> Vect n b -> Vect n (a × b)
vzip [] ys = []
vzip (Cons x x₁) (Cons x₂ x₃) = Cons (x , x₂) (vzip x₁ x₃)


vithElem : ∀ {a}{n} -> Vect n a -> Nat -> Maybe a
vithElem xs b = nothing


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
plusComm n m = {!-c!}

plusSuc : (n : Nat) -> (m : Nat) -> Equality Nat (n + (S m)) (S (n + m))
plusSuc n m = {!-c!}

sym : (a : Set) -> (x : a) -> (y : a) -> Equality a x y -> Equality a y x
sym a x .x (Refl .a .x) = Refl a x

trans : (a : Set) -> (x : a) -> (y : a) -> (z : a) -> Equality a x y -> Equality a y z -> Equality a x z
trans a x .x y (Refl .a .x) p' = p'

cong : (a : Set) -> (b : Set) -> (x : a) -> (y : a) -> (f : a -> b) -> Equality a x y -> Equality b (f x) (f y) 
cong a b y .y p (Refl .a .y) = Refl b (p y)

appDU : (a : Set) -> (b : Set) -> (c : Set) -> (DU a b) -> (a -> c) -> (b -> c) -> c
appDU a b c (DUinl .a .b el) f g = f el
appDU a b c (DUinr .a .b el) f g = g el


notNot : (a : Set) -> a -> not (not a)
notNot a x = {!-c!}

nnnN : (a : Set) -> not a -> not (not (not a))
nnnN a x = x

data EMPTY : ∀ {n : Nat}{a : Set} → Vect n a -> Set where
  E : EMPTY []
  NE : ∀ {h} {t} → (EMPTY (Cons h t))
    
isEmpty'' : ∀ {n} {a} → (v : Vect n a) -> EMPTY v
isEmpty'' k = {!-c!}


data ELEM : ∀ {n} {a} → a -> Vect n a -> Set where
  Here  : ∀ {x} {xs} → ELEM x (Cons x xs)
  Later : ∀ {x y} {xs ys} → ELEM x ys -> ELEM x (Cons y xs)

isElem'' : ∀ {n} {a} → (x : a) -> (xs : Vect n a) -> Maybe (ELEM x xs) 
isElem'' x xs = {!!}


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
zip'' as bs = {!-c!}

lookupV : ∀ {n}{a} → Nat -> Vect n a -> Maybe a
lookupV xs x = nothing


ithElem'' : ∀ {n}{a} → (xs : Vect n a) -> (m : Nat) -> Maybe (Σ a (λ x → Equality (Maybe a) (lookupV m xs) (just x)))
ithElem'' n m = nothing


index'' : ∀ {n}{a} → (x : a) -> (xs : Vect n a) -> Maybe (Σ Nat (λ y → Equality (Maybe a) (lookupV y xs) (just x)))
index'' x xs = nothing


