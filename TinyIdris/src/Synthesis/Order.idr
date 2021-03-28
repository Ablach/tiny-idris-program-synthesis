{-
Module: Synthesis.Order 
Author: Scott Mora
Last Modified: 28.03.2021
Summary: Define heuristics for ranking 
candidate terms for a given search.
-}


module Synthesis.Order 

import Core.Core
import Core.TT
import Core.Env
import TTImp.TTImp
import Synthesis.Search


{-
referenced: Traverses a term testing if 
it references a given name.                                        
-}
referenced : {vars : _} -> 
             Name -> Term vars -> 
             Bool
referenced n (Local idx p) = n == nameAt idx p
referenced n (Ref nty x) = n == x
referenced n (Bind x y scope) = referenced n scope
referenced n (App x y) = referenced n x || referenced n y
referenced n _ = False

{-
The following two functions are used to determine 
which of two terms uses the largest number of 
arguments present in a list of names.
-}
argsUsed : {vars : _} -> 
           List Name -> Term vars ->
           Nat
argsUsed [] tm = Z
argsUsed (x :: xs) tm
  = if referenced x tm then S (argsUsed xs tm) else argsUsed xs tm

mostUsed : {vars : _} ->
           Search vars -> Term vars -> Term vars ->
           Ordering
mostUsed (MkSearch depth name env lhs target) tm tm' 
  = compare (argsUsed vars tm) (argsUsed vars tm')
     

{-
rec: Given a left hand side, find the name of the 
function and test if it is present within the 
right hand side. 
-}
rec : {vars : _} -> RawImp -> Term vars -> Bool
rec (IVar n) t = referenced n t
rec (IPatvar x ty scope) t = rec scope t
rec (IApp x y) t = rec x t
rec _ _ = False

{-
sortRecMax :  If either term is a recursive call, 
prioritise it, if both or neither are, take the 
term that uses the largest number of arguments fron 
the left habd side. 
-}
recSortMax : {vars : _} ->
       Search vars -> Term vars -> Term vars ->
       Ordering
recSortMax s@(MkSearch depth name env lhs target) tm tm' 
  = case (rec lhs tm, rec lhs tm') of
        (True , y) => if y then mostUsed s tm tm' else GT
        (False, y) => if y then LT else mostUsed s tm tm'

{-
sort: Given a search and two candidate terms,
compare the terms using a heuristic defined above.
-}
export 
sort : {vars : _} ->
       Search vars -> Term vars -> Term vars ->
       Ordering
sort s tm tm' = mostUsed s tm tm'
