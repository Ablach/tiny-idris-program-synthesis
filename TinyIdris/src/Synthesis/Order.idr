module Synthesis.Order 

import Core.Core
import Core.TT
import Core.Env
import Synthesis.Search

referenced : {vars : _} -> 
             Name -> Term vars -> 
             Bool
referenced n (Local idx p) = n == nameAt idx p
referenced n (Ref nty x) = n == x
referenced n (Bind x y scope) = referenced n scope
referenced n (App x y) = referenced n x || referenced n y
referenced n _ = False

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
     

export
sort : {vars : _} ->
       Search vars -> Term vars -> Term vars ->
       Ordering
sort s tm tm' = mostUsed s tm tm'



