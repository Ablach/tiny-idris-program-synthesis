module Tests

append : (xs : List a) -> (ys : List a) -> List a
append [] ys = ys
append (x :: xs) ys = ys

map : (a -> b) -> List a -> List b
map f [] = []
map f (x :: xs) = []



lfoldr : (a -> b -> b) -> (acc : b) -> List a -> b
lfoldr f acc [] = acc
lfoldr f acc (x :: xs) = acc



replicate : a -> Nat -> List a
replicate x k = []




drop : Nat -> (xs : List a) -> List a
drop Z xs = xs
drop (S k) xs = xs



isEmpty : List a -> Bool
isEmpty [] = False
isEmpty (x :: xs) = False




isElem :  a -> List a -> Bool
isElem x [] = False
isElem x (y :: xs) = False



duplicate : List a -> List a
duplicate [] = []
duplicate (x :: xs) = xs



zip : List a -> List b -> List (a, b)
zip [] [] = []
zip [] (x :: xs) = []
zip (x :: xs) [] = []
zip (x :: xs) (y :: ys) = []




ithElem : List a -> Nat -> Maybe a
ithElem [] k = Nothing
ithElem (x :: xs) k = Nothing






index : a -> List a -> Maybe Nat
index x xs = Nothing



data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  Cons : a -> Vect n a -> Vect (S n) a

vappend : (xs : Vect n a) -> (ys : Vect m a) -> Vect (n + m) a
vappend [] ys = ys
vappend (Cons x y) ys = Cons x (vappend y ys)




vmap : (a -> b) -> Vect n a -> Vect n b
vmap f [] = []
vmap f (Cons x y) = Cons (f x) (vmap f y)




vfoldr : (a -> b -> b) -> (acc : b) -> Vect n a -> b
vfoldr f acc [] = acc
vfoldr f acc (Cons x y) = acc






vreplicate : a -> (n : Nat) -> Vect n a
vreplicate x Z = []
vreplicate x (S k) = Cons x (vreplicate x k)




vdrop : (m : Nat) -> (xs : Vect n a) -> Vect (minus n m) a
vdrop Z xs = ?vdrop_rhs_5
vdrop (S k) xs = ?vdrop_rhs_3






visEmpty : Vect n a -> Bool
visEmpty [] = False
visEmpty (Cons x y) = False




visElem :  a -> Vect n a -> Bool
visElem x [] = False
visElem x (Cons y z) = False



vduplicate : Vect n a -> Vect (n + n) a
vduplicate [] = []
vduplicate (Cons x y) = Cons x ?vduplicate_rhs_3


vzip : Vect n a -> Vect n b -> Vect n (a, b)
vzip [] y = []
vzip (Cons x z) (Cons y w) = Cons (x, y) (vzip z w)




vithElem : Vect n a -> Nat -> Maybe a
vithElem [] k = Nothing
vithElem (Cons x y) k = Nothing




vindex : a -> Vect n a -> Maybe Nat
vindex x y = Nothing

len : List a -> Nat
len [] = Z
len (x :: xs) = S (len xs)

listToVec : (ls : List a) -> Vect (len ls) a
listToVec [] = []
listToVec (x :: xs) = Cons x (listToVec xs)



vecToList : Vect n a -> List a
vecToList [] = []
vecToList (Cons x y) = x :: vecToList y


