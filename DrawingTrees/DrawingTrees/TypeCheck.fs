namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016

open System
open Machine
open GuardedCommands.Frontend.AST

module TypeCheck = 

/// tcE gtenv ltenv e gives the type for expression e on the basis of type environments gtenv and ltenv
/// for global and local variables 
   let rec tcE gtenv ltenv = function                            
         | N _                                                                         -> ITyp   
         | B _                                                                         -> BTyp   
         | Access acc                                                                  -> tcA gtenv ltenv acc
         | Apply(f,[e])     when List.exists (fun x ->  x=f) ["-";"!"]                 -> tcMonadic gtenv ltenv f e
         | Apply(f,[e1;e2]) when List.exists (fun x ->  x=f) ["+";"*"; "="; "&&"; "-"] -> tcDyadic gtenv ltenv f e1 e2   
         | Apply(f, exprs)                                                             -> match  (Map.tryFind f gtenv) with 
                                                                                          | Some(FTyp(a,b))  -> if List.forall2(fun exp a' -> tcE gtenv ltenv exp = a') exprs a 
                                                                                                                then b.Value 
                                                                                                                else failwith "illtyped function application"
                                                                                          | Some(_) | None   -> failwith "illtyped function application"
         | _                                                                           -> failwith "tcE: not supported yet"

   and tcMonadic gtenv ltenv f e = match (f, tcE gtenv ltenv e) with
                                   | ("-", ITyp) -> ITyp
                                   | ("!", BTyp) -> BTyp
                                   | _           -> failwith "illegal/illtyped monadic expression" 
   
   and tcDyadic gtenv ltenv f e1 e2 = match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["+";"*";"-"]  -> ITyp
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["="]          -> BTyp
                                      | (o, BTyp, BTyp) when List.exists (fun x ->  x=o) ["&&";"="]     -> BTyp 
                                      | _                                                               -> failwith("illegal/illtyped dyadic expression: " + f)

   and tcNaryFunction gtenv ltenv f es = failwith "type check: functions not supported yet"
 
   and tcNaryProcedure gtenv ltenv f es = failwith "type check: procedures not supported yet"
      

/// tcA gtenv ltenv e gives the type for access acc on the basis of type environments gtenv and ltenv
/// for global and local variables 
   and tcA gtenv ltenv = function 
         | AVar x         -> match Map.tryFind x ltenv with
                             | None   -> match Map.tryFind x gtenv with
                                         | None   -> failwith ("no declaration for : " + x)
                                         | Some t -> t
                             | Some t -> t            
         | AIndex(acc, e) -> failwith "tcA: array indexing not supported yes"
         | ADeref e       -> failwith "tcA: pointer dereferencing not supported yes"
 

/// tcS gtenv ltenv retOpt s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
/// for global and local variables and the possible type of return expressions 
   and tcS gtenv ltenv retOpt = function                           
                         | PrintLn e ->                    ignore(tcE gtenv ltenv e)
                         | Ass(acc,e) ->                   if tcA gtenv ltenv acc = tcE gtenv ltenv e 
                                                           then ()
                                                           else failwith "illtyped assignment"                                
                         | Block([], stms)              -> List.iter (tcS gtenv ltenv retOpt) stms
                         | Block(decs,stms)             -> List.iter (tcS (updEnv gtenv decs) ltenv retOpt) stms
                         | Alt (GC(gcs)) | Do (GC(gcs)) -> tcGCSeq gtenv ltenv retOpt gcs
                         | Return(Some(e))              -> if Some(tcE gtenv ltenv e) = retOpt 
                                                           then () 
                                                           else failwith "illtyped return statement"
                         | _                            -> failwith "tcS: this statement is not supported yet"

   and addFTyp f topt = function
    | VarDec(a,b)::decs -> (a,b)::(addFTyp f topt decs)
    | FunDec(_,_,_,_)::decs -> failwith "illtyped function declaration"
    | []          -> []
    
    and updEnv gtenv = function
        | VarDec(t,s)::decs -> updEnv (Map.add s t gtenv) decs
        | FunDec(_,_,_,_)::decs -> failwith "cannot have a function declaration inside a function declaration"
        | [] -> gtenv

   and tcGDec gtenv = function  
                      | VarDec(t,s)                      -> Map.add s t gtenv
                      | FunDec(topt, f, decs, stm)       -> let gtenv = updEnv gtenv decs
                                                            let l' = List.map(fun x -> fst x) (addFTyp f topt decs)
                                                            let gtenv = Map.add f (FTyp(l', topt)) gtenv
                                                            if tcGDecRet gtenv (stm, topt) && List.length (Set.toList (set(tcGDecDiff decs))) = decs.Length && tcS gtenv Map.empty topt stm = ()
                                                            then gtenv 
                                                            else failwith "illtyped function declaration"

   and tcGDecs gtenv = function
                       | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
                       | _         -> gtenv

   and tcGCSeq gtenv ltenv retOpt = function
                       | (((exp:Exp), (stms:Stm list))::gc) -> List.iter (tcS gtenv ltenv retOpt) stms 
                                                               if tcE gtenv ltenv exp = BTyp  then () else failwith "guardedCommand must contain a boolean expression"
                                                               tcGCSeq gtenv ltenv retOpt gc                       
                       | []                                 -> ()

   and tcGDecDiff = function
    | (VarDec(a, b))::decs -> b::tcGDecDiff decs
    | _ -> []
    
   and tcGDecRet gtenv = function
    | (Return(Some(exp)), typ) -> Some(tcE gtenv Map.empty exp) = typ
    
    | (Block(decs, stms), typ)  -> if decs.Length > 0 
                                   then 
                                        let l = updEnv gtenv decs
                                        List.forall(fun stm -> tcGDecRet l (stm, typ)) stms
                                   else 
                                   List.forall(fun stm -> tcGDecRet gtenv (stm, typ)) stms
    | _ -> true

/// tcP prog checks the well-typeness of a program prog
   and tcP(P(decs, stms)) = let gtenv = tcGDecs Map.empty decs
                            List.iter (tcS gtenv Map.empty None) stms