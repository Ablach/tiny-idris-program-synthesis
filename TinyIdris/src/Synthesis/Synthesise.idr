module Synthesis.Synthesise

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
import Data.Nat
import Data.Maybe
import Data.Either
import Data.SortedMap

record Attempt (vars : List Name) where
  constructor MkAttempt
  n : Name 
  nty : NameType
  norm : NF vars

record Search (vars : List Name) where
 constructor MkSearch
 depth : Nat
 name : Name
 env : Env Term vars
 target : Term vars
 
synthesise : {vars : _} -> 
             {auto c : Ref Ctxt Defs} -> 
             {auto u : Ref UST UState} ->
             Search vars -> Core (List (Term vars))


data UFail : Type where
export
tryUnify : {vars : _} ->
           {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           Env Term vars ->
           Term vars -> Term vars -> 
           Core (Maybe (UnifyResult))
tryUnify env a b
  = do 
       newRef UFail False 
       ures <- catch (unify env a b) 
                    (\ _ => do put UFail True 
                               pure $ MkUnifyResult [] False)
       if !(get UFail) 
          then pure Nothing 
          else pure $ Just (ures)


fillMetas : {vars : _} -> 
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST UState} ->
            Env Term vars -> NF vars ->
            Core (NF vars , List (Term vars, Name))
fillMetas env (NBind n (Pi n' pinfo tm) scope) 
  = do defs <- get Ctxt 
       nm <- genName "filling"
       mta <- newMeta env nm !(quote defs env tm) Hole
       (f , args) <- fillMetas env !(scope defs (toClosure env mta))
       pure (f , (mta , nm) :: args)
fillMetas env tm = pure (tm , [])

showCons : {auto c : Ref Ctxt Defs} -> 
           {auto u : Ref UST UState} ->
           List Int -> Core ()
showCons [] = pure ()
showCons (x :: xs) = do let cons = constraints !(get UST)
                            Just con = lookup x cons
                              | _ => pure ()
                        case con of 
                             (MkConstraint env y z) => log $ "con " ++ (show y) ++ " = " ++ (show z)
                             (MkSeqConstraint env ys zs) => ?fdsfdsf_2
                             Resolved => ?fdsfdsf_3

tryIfSuccessful : {vars :_} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST UState} ->
                  (Search vars) ->
                  Name -> NameType ->
                  NF vars -> Core (List (Term vars))
tryIfSuccessful s@(MkSearch (S depth) name env target) n nty (NBind m (Pi nm pinfo tm) sc)
  = do defs <- get Ctxt
       (tm' :: ts) <- synthesise (MkSearch (pred depth) m env !(quote defs env tm))
        | _ => pure []
       results <- traverse help (tm' :: ts)
       pure $ concat results
  where help : Term vars ->
               Core (List (Term vars))
        help tm
         = do defs <- get Ctxt
              sc' <- sc defs (toClosure env tm)
              (filled , fas) <- fillMetas env sc'
              Just ures <- tryUnify env target !(quote defs env filled)
               | _ => do deleteMetas fas ;  pure []
              deleteMetas fas
              
              --log $ "trying " ++ (show tm) ++ "with scope " ++ (show !(quote defs env sc'))
              (r :: rs) <- tryIfSuccessful s n nty sc'
               | _ => pure []
              pure $ map (\ z => App z tm) (r :: rs)
tryIfSuccessful (MkSearch 0 name env target) n nty tm = pure []
tryIfSuccessful (MkSearch depth name env target) n nty tm 
  = do defs <- get Ctxt
       --log $ "trying " ++ (show target) ++ " and " ++ (show !(quote defs env tm))
       Just (MkUnifyResult [] holesSolved) <- tryUnify env target !(quote defs env tm)
        | _ => pure [] 
 --      if holesSolved then log $ "holes solved" else log "no holes solved"
       --showCons constraints
       pure [Ref nty n]


tryDef : {vars : _} ->
         {auto c : Ref Ctxt Defs} -> 
         {auto u : Ref UST UState} ->
         Search vars -> Name -> NameType ->
         Term [] -> Core (List (Term vars))
tryDef s@(MkSearch depth name env target) n nty tm 
 = do defs <- get Ctxt
      norm <- nf defs env (rewrite sym (appendNilRightNeutral vars) in weakenNs vars tm)
      (ntm , args) <- fillMetas env norm
      deleteMetas args
      qtm <- quote defs env ntm
      Just cs <- tryUnify env target qtm
        | _ => pure []
      tryIfSuccessful s n nty norm 
      

tryLocals : {vars : _} -> 
            {auto c : Ref Ctxt Defs} -> 
            {auto u : Ref UST UState} ->
            Search vars -> 
            (usable : List (Term vars)) ->
            Core (List (Term vars))
tryLocals s@(MkSearch depth name env target) (l@(Local idx p) :: usable)
 = case !(tryUnify env target (binderType $ getBinder p env)) of 
        Just (MkUnifyResult [] holesSolved) => 
           do --  log $ "found " ++ (resugarTop $ unelab env (Local idx p)) ++ " for " ++ (show target)
              pure (Local idx p :: !(tryLocals s usable))
        _ => tryLocals s usable
tryLocals _ _ = pure []


synthesise (MkSearch depth name env (Bind n (Pi n' pinfo tm) scope)) 
 = pure $ map (\ st => Bind n (Lam n' pinfo tm) st)
              !(synthesise (MkSearch depth n (Lam n' pinfo tm :: env) scope))
synthesise s@(MkSearch d name env TType) 
  = pure $ !(tryLocals s (getUsableEnv [] env)) ++ !typeRefs
synthesise s@(MkSearch 0 name env tm)
 = tryLocals s (getUsableEnv [] env)
synthesise s@(MkSearch (S k) name env tm)
 = do defs <- get Ctxt
      ust <- get UST
      locals <- tryLocals s (getUsableEnv [] env)
      cons <- case getFnArgs tm of 
                ((Ref nty@(TyCon tag arity) n), as)
                   => do Just def <- lookupDef n defs
                          | _ => pure []
                         let (TCon tag' arity' datacons) = definition def
                          | _ => pure []
                         pure $ concat  !(traverse (\ x => 
                                             do Just d <- lookupDef x defs | _ => pure []
                                                let (DCon t a) = definition d | _ => pure []
                                                tryDef s x (DataCon t a) (type d)) datacons) 
                _ => pure []
      let funcs : List (Name , Term []) = toList $ functions ust
      let fs = concat $ !(traverse (\ (fn, ft) => tryDef s fn Func ft) $ funcs)
      pure (locals ++ cons ++ fs)

public export
run : {auto c : Ref Ctxt Defs} -> 
      {auto u : Ref UST UState} ->
      Name -> Core String
run n = do Just def <- lookupDef n !(get Ctxt)
            | _ => pure "Invalid Name" 
           ust <- get UST
           let (MetaVar vars env retTy) = definition def
            | _ => pure "Invalid Name"
           (r :: res) <- synthesise (MkSearch 4 n env retTy)
            | _ => pure "No result"
           pure $ resugarTop $ unelab env r
           
