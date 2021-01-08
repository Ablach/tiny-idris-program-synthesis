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
                 Nat ->
                 Env Term vars ->
                 List Int ->
                 Term vars -> 
                 Core (List (Search (Term vars)))

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


data UFail : Type where
export
tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Search (List Int))
tryUnify env a b
  = do newRef UST initUState
       newRef UFail False 
       --log $ "unifying " ++ (show a) ++ " and " ++ (show b)
       (MkUnifyResult constr res) <- catch (unify env a b) 
                    (\ _ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       -- we want to union the constraints and find where they fail?
       if !(get UFail) 
          then pure Stop -- do log "unification failed" ; pure Stop
          else pure $ Go (constr)
          -- else do log "unification worked" ; pure $ Go (constr)

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


-- instead what we want it to move along the results from the fill metas
-- and remove one from env and synthesise the rest
synthBinderArgs : {vars : _} -> 
        {auto c : Ref Ctxt Defs} ->
        Nat ->
        (cs : List Int) ->
        (env : Env Term vars) ->
        (target : Term vars) ->
        ((Name, NameType)) ->
        (tm : NF vars) ->
        Core (List (Search (Term vars)))
synthBinderArgs (S depth) cs env target (name,nty) (NBind n (Pi n' pinfo tm) sc) 
 = do defs <- get Ctxt
      let Go tm' = first $ !(synthesiseTerm depth env cs 
                              !(quote defs env tm))
        | _ => pure []
      (Go sc' :: more) <- synthBinderArgs (S depth) cs env 
                                          target (name,nty)
                                          !(sc defs (toClosure env tm'))
        | _ => pure [] 
      pure $ [Go $ App sc' tm']
synthBinderArgs Z cs env target (name,nty) (NBind n (Pi n' pinfo tm) sc)
  = pure []
synthBinderArgs depth cs env target (n,nty) tm
  = pure $ [Go $ Ref nty n]

------------
-- MAIN
------------

checkLocals : {vars : _} ->
              {auto c : Ref Ctxt Defs} ->
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
                  (depth : Nat) ->
                  (cs : List Int) ->
                  (env : Env Term vars) ->
                  (tm : Term vars) ->
                  Core (List (Search (Term vars)))
searchFunctions Z _ _ _ = pure []
searchFunctions (S depth) cs env tm 
  = pure $ concat !(traverse id !(mapDefs' (\ (n , d) => 
      do defs <- get Ctxt
         newRef UST initUState
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
         synthBinderArgs depth cs env tm (n,Func) 
          !(nf defs env (rewrite sym (appendNilRightNeutral vars)
                              in weakenNs vars (type d)))))) 

tryConstructor : {vars : _} ->
                 {auto c : Ref Ctxt Defs} ->  
                 (depth : Nat) ->
                 (cs : List Int) ->
                 (env : Env Term vars) ->
                 (tm : Term vars) ->
                 (n : Name) ->
                 Core (List (Search (Term vars)))
tryConstructor Z _ _ _ _ = pure []
tryConstructor (S depth) cs env tm n
  = do defs <- get Ctxt
       Just def <- lookupDef n defs
        | _ => pure []
       case definition def of    
         (DCon tag arity) => 
            do newRef UST initUState
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
               synthBinderArgs depth cs env tm (n, DataCon tag arity)
                        !(nf defs env (rewrite sym (appendNilRightNeutral vars)
                                            in weakenNs vars (type def)))
         (TCon tag arity datacons) => do                  
           -- log $ "Name " ++ (show n) ++ " is a type Constructor "
           pure $ concat !(traverse id 
                            (map (\ d => 
                                    tryConstructor depth cs env tm d) datacons))
         _ => pure []


synthesiseTerm Z env cs tm
  = checkLocals env (getUsableEnv [] env) tm 
synthesiseTerm depth env cs (Bind n (Pi nm pinfo tm) scope) 
  = do let env' : Env Term (n :: _) = (Lam nm pinfo tm) :: env
       --log $ "Term is a binder, adding lambda for" ++ (show n)
       results <- synthesiseTerm depth env' cs scope
       pure $ map (\ res =>
                      map (\ tm' =>
                             (Bind n (Lam nm pinfo tm) tm'))
                             res) results
synthesiseTerm depth env cs tm
  = do let (ret , args) = getFnArgs tm
       -- when we get usable, we check for lambdas and patterns 
       -- returning locals
       --log $ "searching for " ++ (show tm)
       --log "Locals"
       locals <- checkLocals env (getUsableEnv [] env) tm
       --log "local results"
       --printResults locals
       --log "resugarToped"
       --printFinals env locals
       --log "Data Constructors"
       datas <- case ret of 
                  (Ref (TyCon tag arity) n) 
                    => tryConstructor depth cs env tm n
                  _ => pure []
       --log "datacon results"
       --printResults datas
       --log "functions"
       fs <- searchFunctions depth cs env tm
       --log "function results"
       --printResults fs
       pure $ locals ++ datas ++ fs


filterResults : {vars : _} ->
                {auto c : Ref Ctxt Defs} ->
                Env Term vars ->
                Term vars ->
                List (Search (Term vars)) ->
                Core (List (Search (Term vars)))
filterResults env tm [] = pure []
filterResults env tm (Go x :: xs) 
  = do Go res <- tryUnify env tm x
        | _ => filterResults env tm xs
       pure ((Go x) :: !(filterResults env tm xs))
filterResults env tm (_ :: xs) = filterResults env tm xs


public export
run : {auto c : Ref Ctxt Defs} ->
      Name -> Core String
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           --log $ "Synthesising for " ++ (show retTy)
           res <- (synthesiseTerm 3 {vars = vars} env empty retTy)
           res' <- filterResults env retTy res
           --log "Results: "
           --printFinals env res'
           --log "Final: " 
           let (Go result) = first res' 
            | _ => pure "No result"
           pure $ resugarTop $ unelab env result 


