module Synthesis.Nsynth

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Unify
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

import Synthesis.Rescope
import Synthesis.Unelab
import Synthesis.Resugar
import Synthesis.Monad 

import Data.List
import Data.Maybe
import Data.Either
import Data.SortedMap


synthesiseTerm : {vars : _ } ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST UState} ->
                 Nat -> Env Term vars -> 
                 (Term vars, Name) -> 
                 Core (List (Search (Term vars)))

------------
-- UTILITIES
------------



showN : Name -> String
showN (UN x) = x
showN (MN x y) = x

showB : {vars : _} -> Binder (Term vars) -> String
showB (Lam x y z) = "Lam " ++ (showN x) ++ " : " ++ (show z)
showB (Pi x y z) = "Pi " ++ (showN x) ++ " : " ++ (show z)
showB (PVar x y) = "PVar " ++ (showN x) ++ " : " ++ (show y)
showB (PVTy x) = "PTY " ++ (show x)


showE : {vars : _} -> Env Term vars -> String
showE [] = "[]"
showE (x :: y) = (showE y) ++ " :: " ++ (showB x)

showT : {vars : _} -> Term vars -> String
showT retTy = case retTy of 
                (Local idx p) => "Local " ++ (show idx)
                (Ref x y) => "Ref " ++ (showN y)
                (Meta x xs) => "Meta " ++ (showN x)
                (Bind x y scope) => "bind " ++ (showN x) ++ " " ++ (showB y) ++ " " ++ (showT scope)
                (App x y) => showT x
                TType => "ttype"
                Erased => "erased"

trans : List (Search a) -> List (a)
trans [] = []
trans (Stop :: xs) = trans xs
trans ((Go x) :: xs) = x :: trans xs

export 
functions : {auto c : Ref Ctxt Defs} -> Core (List (Search (Name, Term [])))
functions = mapDefs' (\ (n,def) =>
               do let (PMDef args treeCT) = definition def
                    | _ => Stop
                  Go (n,(type def)))
 
first : List (Search a) -> Search a
first [] = Stop
first (Stop :: xs) = first xs
first ((Go x) :: xs) = Go x

printResults : {vars : _} ->
               List (Search (Term vars)) ->
               Core ()
printResults [] = pure ()
printResults (Stop :: xs) = printResults xs
printResults ((Go x) :: xs) = do log (show x) ; printResults xs 

printFinals : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars ->
              List (Search (Term vars)) ->
              Core ()
printFinals env [] = pure ()
printFinals env (Stop :: xs) = printFinals env xs
printFinals env (Go x :: xs) 
  = do log (resugarTop $ unelab env x) ; printFinals env xs

showC : Constraint -> String
showC (MkConstraint env x y) =  show x ++ " == " ++ show y
showC (MkSeqConstraint env xs ys) =  "seq " ++ show xs ++ show ys
showC Resolved =  "resolved"

showCs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         List Int -> Core String
showCs [] = pure "[]"
showCs (x :: xs) 
  = do let cs = constraints !(get UST)
       let Just con = lookup x cs
       | _ => pure ""
       case con of 
        (MkConstraint env y z) => 
          pure $ "\nConstraint: " ++ (show x) ++ " Term 1: (" ++ 
                                (showT (y)) ++ ") Term 2: (" ++
                                (showT (z)) ++ ") rest: " ++ !(showCs xs)
        (MkSeqConstraint env y z) => 
          pure $ "\nSConstraint: " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z) ++ !(showCs xs)
        Resolved => pure $ "\nResolved" ++ (show x) ++ !(showCs xs)


filterResults : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                List (Search (Term vars, List Int)) ->  
                Core (List (Search (Term vars)))
filterResults [] = none
filterResults (Stop :: xs) = filterResults xs
filterResults ((Go (t, is)) :: xs) = do [] <- retryInts is
                                          | _ => filterResults xs
                                        pure $ Go t :: !(filterResults xs)


makeApps : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars -> Term vars ->
           List (List (Search (Term vars))) ->
           Core (List (Search (Term vars)))
makeApps env tm [] = none
makeApps env tm ([] :: xs) = none -- argument cannot be synthesised anymore
makeApps env tm ((Go x :: ts) :: xs) 
  = pure $ !(makeApps env (App tm x) xs) ++ !(makeApps env tm (ts :: xs))
makeApps env tm ((Stop :: ts) :: xs) = makeApps env tm (ts :: xs)

--------------------
-- MAIN ------------
--------------------

data UFail : Type where
export
tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Search (UnifyResult))
tryUnify env a b
  = do 
       newRef UFail False 
       --log $ "unifying " ++ (resugarTop $ unelab env a) ++ " and " ++ (resugarTop $ unelab env b)
       ures <- catch (unify env a b) 
                    (\ _ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       -- we want to union the constraints and find where they fail?
       if !(get UFail) 
          then stop -- do log "unification failed" ; stop
          else pure $ Go (ures)
          --else do log $ "unification worked" ++ !(showCs constr); pure $ Go (constr)


fillMetas : {vars :_} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} -> 
            Env Term vars -> NF vars ->
            Core (NF vars, List (Term [], Name))
fillMetas env (NBind n (Pi n' pinfo tm) sc) 
  = do defs <- get Ctxt 
       empty <- clearDefs defs
       ty <- quote empty env tm
       nm <- genName "mta"
       tm' <- newMeta env nm ty Hole
       (f, as) <- fillMetas env !(sc defs (toClosure env tm'))
       let sh' = concat $ intersperse " " !(traverse id !(mapDefs' (\ (n,d) => pure (show n))))
       Just def <- lookupDef nm !(get Ctxt) 
        | _ => ?impossible 
       pure (f , ((type def), nm) :: as)
fillMetas env tm = pure (tm , [])


tryWhile : {vars : _} -> 
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST UState} -> 
           (depth : Nat) ->
           (env : Env Term vars) -> 
           (target : Term vars) -> 
           (args : List (Term vars , Name)) ->
           Core (List (Search (Term vars)))
tryWhile depth env target [] = ?fdsf_1
tryWhile depth env target (x :: xs) = ?fdsf_2

tryClosed : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} -> 
            (depth : Nat) ->
            (env : Env Term vars) -> 
            (target : Term vars) -> 
            Name -> NameType -> (ct : Term []) -> 
            Core (List (Search (Term vars)))
tryClosed Z _ _ _ _ _ = none
tryClosed (S depth) env target n nty ct
  = do defs <- get Ctxt
       --log $ "trying " ++ (show target) ++ " with " ++ (showN n)
       (tm, args) <- fillMetas env !(nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars ct))
       Go ures <- tryUnify env target !(quote defs env tm)
        | _ => none
       let weakened = map (\ (a,b) => (weakenNs vars a , b)) args
       
       args' <- traverse (synthesiseTerm depth env) (rewrite sym (appendNilRightNeutral vars) in weakened)
       makeApps env (Ref nty n) args'
       ?fsdfd
------------
-- MAIN
------------

checkLocals : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} ->
              (env : Env Term vars) -> 
              (usable : List (Term vars)) -> 
              (tm : Term vars) ->
              Core (List (Search (Term vars)))
checkLocals env ((Local idx p) :: xs) tm 
  = 
 do --log $ "in locals, checking " ++ (show (binderType $ getBinder p env)) ++ " with " ++ (show tm)
    Go ures <- tryUnify env tm (binderType $ getBinder p env)
      | _ => checkLocals env xs tm
    let [] = constraints ures
      | _ => checkLocals env xs tm
    --log "success"
    pure $ (Go (Local idx p)) :: !(checkLocals env xs tm) 
checkLocals env (_ :: xs) tm = checkLocals env xs tm
checkLocals _ [] _ = none

searchFunctions : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  (depth : Nat) ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  Core (List (Search (Term vars)))
searchFunctions Z _ _ = none
searchFunctions depth env tm 
  = do ust <- get UST
       let fs = Data.SortedMap.toList $ functions ust
       --log "in functions"
       ts <- traverse (\(n,y) => tryClosed depth env tm n Func y) fs 
       pure $ concat ts
                                  
{-
  = pure $ concat !(traverse id !(mapDefs' (\ (n , def) => 
      do defs <- get Ctxt 
         let (PMDef args treeCT) = definition def
          | _ => none
         tryClosed depth env tm (n, Func) (type def))))
          -}
tryConstructor : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->  
                 {auto u : Ref UST UState} ->
                 (depth : Nat) -> 
                 (env : Env Term vars) ->
                 (tm : Term vars) ->
                 (n : Name) ->
                 Core (List (Search (Term vars)))
tryConstructor Z _ _ _ = none
tryConstructor depth env tm n
  = do defs <- get Ctxt
       Just def <- lookupDef n defs
        | _ => none
       case definition def of    
         (DCon tag arity) => 
          do --log "in datacons"
             tryClosed depth env tm n (DataCon tag arity) (type def)
         (TCon tag arity datacons) => 
          do --log "trying type cons"
             pure $ concat !(traverse id 
                            (map (\ d => 
                                    tryConstructor depth env tm d) datacons))
         _ => none


synthesiseTerm Z env (tm,n)
  = do --log $ "env " ++ (showE env)
       --log $ "usable " ++ (show (getUsableEnv [] env) )
       checkLocals env (getUsableEnv [] env) tm
synthesiseTerm depth env ((Bind n (Pi nm pinfo tm) scope) , name)
  = do let env' : Env Term (n :: _) = (Lam nm pinfo tm) :: env
       --log $ "Term is a binder, adding lambda for" ++ (show n)
       results <- synthesiseTerm depth env' (scope , n)
       pure $ map (\ res =>
                      map (\ tm' =>
                             (Bind n (Lam nm pinfo tm) tm'))
                             res) results
synthesiseTerm depth env (tm,n)
  = do let (ret , args) = getFnArgs tm
       --log $ "env " ++ (showE env)
       --log $ "usable " ++ (show (getUsableEnv [] env) )
       locals <- checkLocals env (getUsableEnv [] env) tm 
       datas <- case ret of 
                  (Ref (TyCon tag arity) n) 
                      => tryConstructor depth env tm n
                  _ => none 
       fs <- searchFunctions depth env tm
       {-log $ "searching for " ++ (show tm)
       log "local results"
       printFinals env locals
       log "datacon results"
       printFinals env $ (map (map fst)) datas
       log "function results"
       printFinals env $ (map (map fst)) fs -}
       --case (locals ++ datas ++ fs) of
         --   [] => log $ "no results found for " ++ (show tm)
           -- (x :: xs) => log $ "results found for " ++ (show tm)
       pure $ locals ++ datas ++ fs 


tt : {auto c : Ref Ctxt Defs} -> 
     {auto u : Ref UST UState} ->
     Core ()
tt = do defs <- get Ctxt
        Just nil <- lookupDef (UN "Nil") defs
          | _ => log "no nil"
        Just tm <- lookupDef (UN "v02") defs
          | _ => log "no tm"
        let (MetaVar vars env ret) = definition tm
          | _ => log "not meta"
        let us = (getUsableEnv [] env) 
        log $ "env " ++ (showE env)
        log $ "usable " ++ (show us)
        log $ concat $ intersperse " ::  " $ map (\ l => case l of
                                                Local idx p => show (binderType $ getBinder p env)
                                                _ => "not local") us
        ls <- checkLocals env us ret
        case ls of 
             [] => log "none"
             (x :: xs) => log "some"
        {-
        nfnil <- nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars (type nil))
        empty <- clearDefs defs
        let (NBind n (Pi n' pinfo tx) sc) = nfnil
          | _ => log "nfnil not binder"
        ty <- quote empty env tx
        nm <- genName "mta"
        tm' <- newMeta env nm ty Hole
        log (show tm')
        case !(lookupDef nm !(get Ctxt)) of
             Nothing => log $ (show nm) ++ " not there"
             (Just x) => log "there!"
             -}


public export
run : {auto c : Ref Ctxt Defs} ->
      {auto u : Ref UST UState} ->
      Name -> Core String
--run n = do tt ; pure ""
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           ust <- get UST
           let cs = Data.SortedMap.toList $ constraints ust
           let s = map (\(x,y) => (show x) ++ ": " ++ (showC y) ++ "\n") cs
           log $ concat s
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           res <- (synthesiseTerm 3 {vars = vars} env (retTy, n)) 
           let (Go result) = first res
            | _ => pure "No result"
           pure $ resugarTop $ unelab env result
           

