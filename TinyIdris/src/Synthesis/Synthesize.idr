module Synthesis.Synthesize 
{-
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
                 Core (List (Search (Term vars, List Int)))

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

showCs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST UState} ->
         List Int -> Core String
showCs [] = pure ""
showCs (x :: xs) 
  = do let cs = constraints !(get UST)
       let Just con = lookup x cs
       | _ => pure ""
       case con of 
        (MkConstraint env y z) => 
          pure $ "\nConstraint: " ++ (show x) ++ " " ++ 
                                (show (y)) ++ " " ++
                                (show (z)) ++ !(showCs xs)
        (MkSeqConstraint env y z) => 
          pure $ "\nSConstraint: " ++ (show x) ++ " " ++ (show y) ++ " " ++ (show z) ++ !(showCs xs)
        Resolved => pure $ "\nResolved" ++ (show x) ++ !(showCs xs)

data UFail : Type where
export
tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Search (List Int))
tryUnify env a b
  = do 
       newRef UFail False 
       --log $ "unifying " ++ (resugarTop $ unelab env a) ++ " and " ++ (resugarTop $ unelab env b)
       (MkUnifyResult constr res) <- catch (unify env a b) 
                    (\ _ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       -- we want to union the constraints and find where they fail?
       if !(get UFail) 
          then stop -- do log "unification failed" ; stop
          else pure $ Go (constr)
          --else do log $ "unification worked" ++ !(showCs constr); pure $ Go (constr)

tryUnify' : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Search (UnifyResult))
tryUnify' env a b
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


fillMetas' : {vars :_} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} -> 
            Env Term vars -> NF vars ->
            Core (NF vars, List (Term vars, Name))
fillMetas' env (NBind n (Pi n' pinfo tm) sc) 
  = do defs <- get Ctxt 
       empty <- clearDefs defs
       ty <- quote empty env tm
       nm <- genName "n'"
       tm' <- newMeta env nm ty Hole
       (f, as) <- fillMetas' env !(sc defs (toClosure env tm'))
       pure (f , (tm', nm) :: as)
fillMetas' env tm = pure (tm , [])


fillMetas : {vars :_} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} -> 
            Term vars -> Env Term vars ->
            Core (metas **
              (Term (metas ++ vars),
                List (Term (metas ++ vars)),
                  Env Term (metas ++ vars)))
fillMetas (Bind x (Pi n pinfo w) scope) env 
  = do let env' = Pi n pinfo w :: env
       (metas ** (tm , ts, env'')) <- fillMetas scope env'
       let tm' = App tm (Meta x [])
       pure $ ((metas ++ [x]) ** 
                (rewrite sym (appendAssociative metas [x] vars) 
                      in (tm , 
                           ((weakenNs metas (weaken w)) :: ts) ,
                             env''))) 
fillMetas tm env = pure $ ([] ** (tm , [], env))

makeApps : {vars : _} ->
           List (List (Search (Term vars))) ->
           Term vars ->
           Core (List (Search (Term vars)))
makeApps [] x = pure $ [Go x]
makeApps ([] :: xs) x = none
makeApps (((Go y) :: ys) :: xs) x 
  = do scopes <- (makeApps xs x)
       rest <- makeApps (ys :: xs) x
       let apps = map (\ x => map (App y) x) scopes
       pure $ apps ++ rest
makeApps ((Stop :: ys) :: xs) x = makeApps (ys :: xs) x

tryUnifyInScope : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST UState} -> 
              (env : Env Term vars) ->
              (target : Term vars) ->
              (argtms : List (Search (Term vars, List Int))) -> 
              (sc : Defs -> Closure vars -> Core (NF vars)) -> 
              Core (List (Search (Term vars, List Int)))
tryUnifyInScope env target (Go (tm' , cs) :: argtms) sc
  = do defs <- get Ctxt
       Go res <- tryUnify env target !(quote defs env !(sc defs (toClosure env tm')))
        | _ => tryUnifyInScope env target argtms sc
       pure $ Go (tm' , cs) :: !(tryUnifyInScope env target argtms sc)
tryUnifyInScope env target (Stop :: argtms) sc = tryUnifyInScope env target argtms sc
tryUnifyInScope env target [] sc = none

tryUnifyAll : {vars : _} ->
              {auto c : Ref Ctxt Defs} -> 
              {auto u : Ref UST UState} ->
              Env Term vars -> Term vars -> 
              List (Search (Term vars, List Int)) -> 
              Core (List (Search (Term vars, List Int)))
tryUnifyAll env tm [] = none
tryUnifyAll env tm (Stop :: xs) = tryUnifyAll env tm xs
tryUnifyAll env tm ((Go (tm',cs)) :: xs) = do Go [] <- tryUnify env tm tm'
                                                | _ => tryUnifyAll env tm xs
                                              pure $ Go (tm' , []) :: !(tryUnifyAll env tm xs)
extendApp : {vars : _} -> Term vars -> List Int -> (Term vars, List Int) -> (Term vars , List Int)
extendApp arg cs (tm, fcs) = (App tm arg, (cs ++ fcs))

mutual
  synthBinderArgs' : {vars :_} -> 
                     {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST UState} ->
                     Nat -> Env Term vars -> Term vars ->
                     (Name, NameType) -> (Defs -> Closure vars -> Core (NF vars)) -> 
                     Search (Term vars, List Int) -> Core (List (Search (Term vars , List Int)))
  synthBinderArgs' depth env target (name,nty) sc (Go (tm , cs)) 
    = do defs <- get Ctxt
         res'' <- synthBinderArgs (S depth) env target (name, nty) !(sc defs (toClosure env tm))  
         pure $ map (map (extendApp tm cs)) res'' 
  synthBinderArgs' _ _ _ _ _ _ = none

  -- instead what we want it to move along the results from the fill metas
  -- and remove one from env and synthesise the rest
  synthBinderArgs : {vars : _} -> 
                    {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST UState} ->
                    Nat ->
                    (env : Env Term vars) ->
                    (target : Term vars) ->
                    (Name, NameType) ->
                    (tm : NF vars) ->
                    Core (List (Search (Term vars, List Int)))
  synthBinderArgs (S depth) env target (name,nty) (NBind n (Pi n' pinfo tm) sc) 
   = do defs <- get Ctxt 
        argtms <- synthesiseTerm depth env (!(quote defs env tm),?fdsddddd)
        argtms' <- tryUnifyInScope env target argtms sc
        res' <- traverse id $ map (synthBinderArgs' depth env target (name, nty) sc) argtms'
        pure $ concat res'
  synthBinderArgs Z env target (name,nty) (NBind n (Pi n' pinfo tm) sc)
     = none
  synthBinderArgs depth env target (n,nty) tm
    = pure $ [Go $ (Ref nty n, [])]

tryClosed : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} -> 
            (depth : Nat) ->
            (env : Env Term vars) -> 
            (target : Term vars) -> 
            Name -> (ct : Term []) -> 
            Core (List (Search (Term vars)))
tryClosed depth env target n ct
  = do defs <- get Ctxt
       (tm, args) <- fillMetas' env !(nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars ct))
       Go ures <- tryUnify' env target !(quote defs env tm)
        | _ => none
       let [] = constraints ures
        | cs => do log !(showCs cs) ; none
       args' <- traverse (synthesiseTerm depth env) args
       ?fdis
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
 do --log "usable env:"
    --traverse (\ x => log (show x)) ((Local idx p) :: xs) 
    --log $ "trying " ++ (show tm) ++ " with " ++ (show (Local idx p))
    case !(tryUnify env tm (binderType $ getBinder p env)) of 
         (Go []) => pure $ (Go (Local idx p)) :: !(checkLocals env xs tm) 
         _ => checkLocals env xs tm
checkLocals env (_ :: xs) tm = checkLocals env xs tm
checkLocals _ [] _ = none

searchFunctions : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  (depth : Nat) ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  Core (List (Search (Term vars, List Int)))
searchFunctions Z _ _ = none
searchFunctions (S depth) env tm 
  = pure $ concat !(traverse id !(mapDefs' (\ (n , def) => 
      do defs <- get Ctxt 
         let (PMDef args treeCT) = definition def
          | _ => none
         (metas ** (ftm , ts, e)) <- fillMetas
                                      (weakenNs vars (type def))
                                      (rewrite appendNilRightNeutral vars in env)  
         Go meta_cs <- tryUnify e (rewrite appendNilRightNeutral vars in weakenNs metas tm) ftm      
                | _ => none
         
         synthBinderArgs depth env tm (n,Func) 
          !(nf defs env (rewrite sym (appendNilRightNeutral vars)
                              in weakenNs vars (type def)))))) 

tryConstructor : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->  
                 {auto u : Ref UST UState} ->
                 (depth : Nat) -> 
                 (env : Env Term vars) ->
                 (tm : Term vars) ->
                 (n : Name) ->
                 Core (List (Search (Term vars, List Int)))
tryConstructor Z _ _ _ = none
tryConstructor (S depth) env tm n
  = do defs <- get Ctxt
       Just def <- lookupDef n defs
        | _ => none
       case definition def of    
         (DCon tag arity) => 
            do 
               --log $ "Name " ++ (show n) ++ " is a data Constructor "
               (metas ** (ftm , ts, e)) <- fillMetas
                                             (weakenNs vars (type def))
                                             (rewrite appendNilRightNeutral vars in env)  
               
               Go meta_cs <- tryUnify e (rewrite appendNilRightNeutral vars in weakenNs metas tm) ftm      
                | _ => none

               synthBinderArgs depth env tm (n, DataCon tag arity)
                        !(nf defs env (rewrite sym (appendNilRightNeutral vars)
                                            in weakenNs vars (type def)))
         (TCon tag arity datacons) => do                  
           -- log $ "Name " ++ (show n) ++ " is a type Constructor "
           pure $ concat !(traverse id 
                            (map (\ d => 
                                    tryConstructor depth env tm d) datacons))
         _ => none


synthesiseTerm Z env (tm,n)
  = pure $ map (map (\ x => (x,[]))) !(checkLocals env (getUsableEnv [] env) tm)
synthesiseTerm depth env ((Bind n (Pi nm pinfo tm) scope) , name)
  = do let env' : Env Term (n :: _) = (Lam nm pinfo tm) :: env
       --log $ "Term is a binder, adding lambda for" ++ (show n)
       results <- synthesiseTerm depth env' (scope , ?fdas)
       pure $ map (\ res =>
                      map (\ (tm', cs') =>
                             (Bind n (Lam nm pinfo tm) tm' , cs'))
                             res) results
synthesiseTerm depth env (tm,n)
  = do let (ret , args) = getFnArgs tm
       -- when we get usable, we check for lambdas and patterns 
       -- returning locals
       locals <- checkLocals env (getUsableEnv [] env) tm
       let locals' = map (map (\ x => (x,[]))) locals
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
       pure $ locals' ++ datas ++ fs 

fst' : {vars : _} ->
       List (Search (a,b)) ->
       List (Search a)


public export
run : {auto c : Ref Ctxt Defs} ->
      {auto u : Ref UST UState} ->
      Name -> Core String
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           
           --log $ showE env
           res <- (synthesiseTerm 4 {vars = vars} env (retTy, n))
           res' <- filterResults res
           --log "Results: "
           --log $ "Synthesising for " ++ (show retTy)   
           --printFinals env res'

           let (Go result) = first res 
            | _ => pure "No result"
           pure $ resugarTop $ unelab env (fst result)

-}
