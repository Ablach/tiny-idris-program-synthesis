module Synthesis.Synthesize 

import Core.Context
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.UnifyState
import Core.Value

import TTImp.Elab.Term
import TTImp.TTImp

import Data.List
import Data.List.Quantifiers
import Data.Maybe


synthesize_world : {vars' : _} ->
                   {auto c : Ref Ctxt Defs} -> 
                   {auto u : Ref UST UState} ->
                   Env Term vars' -> Closure vars' -> 
                   Maybe (NF vars')
synthesize_world env (MkClosure lenv env' (Ref n nty)) = ?synthesize_world_rhs_4
synthesize_world env (MkClosure lenv env' (Bind n bdr scope)) = ?synthesize_world_rhs_6
synthesize_world env (MkClosure lenv env' _) = Nothing

mltodef : Maybe (List (NF vars)) ->
          Maybe Def

synthesize : {vars : _} -> 
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST UState} ->
             Env Term vars ->
             NF vars -> Core (Maybe Def)
synthesize env (NTCon x tag arity xs)
   = do let ds = map (synthesize_world env) xs                                                     
        let res = help ds                                                                        
        case res of                                                                              
             Nothing => pure Nothing                                                             
             js => pure (mltodef js)
     where                                                                                       
        help : List (Maybe a) -> Maybe (List a)                                                  
        help [] = Just []                                                                        
        help (y :: ys)                                                                           
        = case isItJust y of                                                                     
               (Yes prf) => do let y' = fromJust y                                               
                               case help ys of                                                   
                                    Nothing => Nothing                                           
                                    (Just t) => Just (y' :: t) 
               (No contra) => Nothing                                                           
synthesize _ _ = pure Nothing 

to_string : {vars : _} -> NF vars -> String
to_string x = ?to_string_rhs

export
synthesize_single : {vars : _} ->
                    {auto c : Ref Ctxt Defs} -> 
                    {auto u : Ref UST UState} ->  
                    Env Term vars ->
                    Glued vars -> 
                    Core String
synthesize_single env ty 
  = do t <- getTerm ty 
       case t of 
            (Bind name tm scope) => 
                  do defs <- get Ctxt
                     let env' = tm :: env
                     let gscope = gnf env' scope
                     synthesize_single env' gscope                        
            (Ref namety n) => 
                 do defs <- get Ctxt
                    def <- lookupDef n defs
                    case def of
                         Nothing => pure "Name not in context."
                         (Just d) => 
                              do res <- synthesize env !(getNF ty)
                                 case res of 
                                      Nothing => pure "Could not synthesize a definiton."
                                      (Just x) => pure $ ?fdfrest --to_string x
            otherwise => pure "Invalid signature"
     
