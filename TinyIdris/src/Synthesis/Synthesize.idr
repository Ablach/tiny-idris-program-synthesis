module Synthesis.Synthesize 

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
                 Nat ->
                 Env Term vars -> 
                 Term vars -> 
                 Core (List (Search (Term vars, List Int)))

------------
-- UTILITIES
------------

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
                                (show (resugarTop $ unelab env y)) ++ " " ++
                                (show (resugarTop $ unelab env z)) ++ !(showCs xs)
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
          then pure Stop -- do log "unification failed" ; pure Stop
          else pure $ Go (constr)
          --else do log $ "unification worked" ++ !(showCs constr); pure $ Go (constr)

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
makeApps ([] :: xs) x = pure []
makeApps (((Go y) :: ys) :: xs) x 
  = do scopes <- (makeApps xs x)
       rest <- makeApps (ys :: xs) x
       let apps = map (\ x => map (App y) x) scopes
       pure $ apps ++ rest
makeApps ((Stop :: ys) :: xs) x = makeApps (ys :: xs) x


filterResults : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST UState} ->
                List (Search (Term vars, List Int)) ->  
                Core (List (Search (Term vars)))
filterResults [] = pure []
filterResults (Stop :: xs) = filterResults xs
filterResults ((Go (t, is)) :: xs) = do [] <- retryInts is
                                          | _ => filterResults xs
                                        pure $ Go t :: !(filterResults xs)


-- instead what we want it to move along the results from the fill metas
-- and remove one from env and synthesise the rest
synthBinderArgs : {vars : _} -> 
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  Nat ->
                  (env : Env Term vars) ->
                  (target : Term vars) ->
                  ((Name, NameType)) ->
                  (tm : NF vars) ->
                  Core (List (Search (Term vars, List Int)))
synthBinderArgs (S depth) env target (name,nty) (NBind n (Pi n' pinfo tm) sc) 
 = do defs <- get Ctxt
      let Go (tm', cs) = first $ !(synthesiseTerm depth env 
                                  !(quote defs env tm))
        | _ => pure []
      (Go (sc', cs') :: more) <- synthBinderArgs (S depth) env 
                                          target (name,nty)
                                          !(sc defs (toClosure env tm'))
        | _ => pure [] 
      pure $ [Go $ (App sc' tm', cs ++ cs')]
synthBinderArgs Z env target (name,nty) (NBind n (Pi n' pinfo tm) sc)
  = pure []
synthBinderArgs depth env target (n,nty) tm
  = pure $ [Go $ (Ref nty n, [])]

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
checkLocals _ [] _ = pure []

searchFunctions : {vars : _} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  (depth : Nat) ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  Core (List (Search (Term vars, List Int)))
searchFunctions Z _ _ = pure []
searchFunctions (S depth) env tm 
  = pure $ concat !(traverse id !(mapDefs' (\ (n , d) => 
      do defs <- get Ctxt 
         let (PMDef args treeCT) = definition d
          | _ => pure []
         --log $ "trying definition for " ++ (show n)
         (metas ** (ftm , ts , e)) <- fillMetas 
                                        (rewrite sym (appendNilRightNeutral vars)
                                              in (weakenNs vars (type d))) env
         Go meta_cs <- tryUnify e (weakenNs metas tm) ftm
          | _ => pure []
         traverse deleteConstraint meta_cs
         --log "unification succedded, synthesising arguments"
         synthBinderArgs depth env tm (n,Func) 
          !(nf defs env (rewrite sym (appendNilRightNeutral vars)
                              in weakenNs vars (type d)))))) 

tryConstructor : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->  
                 {auto u : Ref UST UState} ->
                 (depth : Nat) -> 
                 (env : Env Term vars) ->
                 (tm : Term vars) ->
                 (n : Name) ->
                 Core (List (Search (Term vars, List Int)))
tryConstructor Z _ _ _ = pure []
tryConstructor (S depth) env tm n
  = do defs <- get Ctxt
       Just def <- lookupDef n defs
        | _ => pure []
       case definition def of    
         (DCon tag arity) => 
            do 
               --log $ "Name " ++ (show n) ++ " is a data Constructor "
               (metas ** (ftm , ts, e)) <- fillMetas
                                             (weakenNs vars (type def))
                                             (rewrite appendNilRightNeutral vars in env)
               Go meta_cs <- tryUnify e 
                               (rewrite appendNilRightNeutral vars in weakenNs metas tm)
                               ftm
                 | _ => pure [] --do log $ "unifying " ++ (show tm) ++ " and " ++ (show ftm) ++ " failed" 
               traverse deleteConstraint meta_cs
               -- log $ "unification between " ++ (show tm) ++ " and " ++
               -- (show ftm) ++ " succeded, synthesising arguments" 
               synthBinderArgs depth env tm (n, DataCon tag arity)
                        !(nf defs env (rewrite sym (appendNilRightNeutral vars)
                                            in weakenNs vars (type def)))
         (TCon tag arity datacons) => do                  
           -- log $ "Name " ++ (show n) ++ " is a type Constructor "
           pure $ concat !(traverse id 
                            (map (\ d => 
                                    tryConstructor depth env tm d) datacons))
         _ => pure []


synthesiseTerm Z env tm 
  = pure $ map (map (\ x => (x,[]))) !(checkLocals env (getUsableEnv [] env) tm)
synthesiseTerm depth env (Bind n (Pi nm pinfo tm) scope) 
  = do let env' : Env Term (n :: _) = (Lam nm pinfo tm) :: env
       --log $ "Term is a binder, adding lambda for" ++ (show n)
       results <- synthesiseTerm depth env' scope
       pure $ map (\ res =>
                      map (\ (tm', cs') =>
                             (Bind n (Lam nm pinfo tm) tm' , cs'))
                             res) results
synthesiseTerm depth env tm
  = do let (ret , args) = getFnArgs tm
       -- when we get usable, we check for lambdas and patterns 
       -- returning locals
       --log $ "searching for " ++ (show tm)
       --log "Locals"
       locals <- checkLocals env (getUsableEnv [] env) tm
       let locals' = map (map (\ x => (x,[]))) locals
       --log "local results"
       --printFinals env locals
       --log "resugarToped"
       --printFinals env locals
       --log "Data Constructors"
       datas <- case ret of 
                  (Ref (TyCon tag arity) n) 
                    => tryConstructor depth env tm n
                  _ => pure []
       --log "datacon results"
       --printFinals env datas
       --log "functions"
       fs <- searchFunctions depth env tm
       --log "function results"
       --printFinals env fs
       pure $ locals' ++ datas ++ fs


public export
run : {auto c : Ref Ctxt Defs} ->
      {auto u : Ref UST UState} ->
      Name -> Core String
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           --log $ "Synthesising for " ++ (show retTy)
           res <- (synthesiseTerm 3 {vars = vars} env retTy)
           res' <- filterResults res
           --log "Results: "
           --printFinals env res'
           --log "Final: " 
           let (Go result) = first res' 
            | _ => pure "No result"
           pure $ resugarTop $ unelab env result 


