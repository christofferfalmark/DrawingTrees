namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft
open System
open Machine

open GuardedCommands.Frontend.AST
module CodeGeneration =


(* A global variable has an absolute address, a local one has an offset: *)
   type Var = 
     | GloVar of int                   (* absolute address in stack           *)
     | LocVar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and 
   keeps track of next available offset for local variables *)

   type varEnv = Map<string, Var*Typ> * int

(* The function environment maps function name to label and parameter decs *)

   type ParamDecs = (Typ * string) list
   type funEnv = Map<string, label * Typ option * ParamDecs>
     
     // The following functions (bindParam & bindParams) is based on the provided Micro-C project (P. Sestoft).
     (* Bind declared parameters in env: *)
   let bindParam (env, fdepth) dec  : varEnv = 
    match dec with
     | VarDec(typ,x) -> (Map.add x (LocVar fdepth, typ) env, fdepth+1)
     | _ -> (env,fdepth)
    
   let bindParams (paras:Dec list) ((env, fdepth) : varEnv) : varEnv = List.fold bindParam (env, fdepth) paras

/// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
   let rec CE vEnv fEnv = 
       function
       | N n          -> [CSTI n]
       | B b          -> [CSTI (if b then 1 else 0)]
       | Access acc   -> CA vEnv fEnv acc @ [LDI] 
       | Apply("-", [e]) -> CE vEnv fEnv e @  [CSTI 0; SWAP; SUB]
       | Apply("!", [e]) -> CE vEnv fEnv e @ [NOT]
       | Apply("&&",[b1;b2]) -> let labend   = newLabel()
                                let labfalse = newLabel()
                                CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2
                                @ [GOTO labend; Label labfalse; CSTI 0; Label labend]

       | Apply(o,[e1;e2]) when List.exists (fun x -> o=x) ["+"; "*"; "="; "-"]
                             -> let ins = match o with
                                          | "+"  -> [ADD]
                                          | "*"  -> [MUL]
                                          | "="  -> [EQ] 
                                          | "-"  -> [SUB] 
                                          | _    -> failwith "CE: this case is not possible"
                                CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins
       | Apply(f, es) -> callfun f es vEnv fEnv
       | _ -> failwith "CE: not supported yet"
       
   (* Generate code to evaluate a list es of expressions: *)
   and CEs vEnv fEnv es : instr list = List.concat(List.map (fun e -> CE vEnv fEnv e) es)

/// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
   and CA vEnv fEnv = function 
   | AVar x         -> match Map.find x (fst vEnv) with
                             | (GloVar addr,_) -> [CSTI addr]
                             | (LocVar addr,_) -> [GETBP; CSTI addr; ADD]
   | AIndex(acc, e) -> failwith "CA: array indexing not supported yet" 
   | ADeref e       -> failwith "CA: pointer dereferencing not supported yet"

  // The following code is based on the provided Micro-C project (P. Sestoft).
   and callfun f es vEnv fEnv : instr list =
     let (labf, tyOpt, paramdecs) = Map.find f fEnv
     let argc = List.length es
     if argc = List.length paramdecs 
     then CEs vEnv fEnv es @ [CALL(argc, labf)]
     else failwith "parameter/argument mismatch"

(* Bind declared variable in env and generate code to allocate it: *)   
   let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv)  =
    let (env, fdepth) = vEnv 
    match typ with
    | ATyp (ATyp _, _) -> raise (Failure "allocate: array of arrays not permitted")
    | ATyp (t, Some i) -> failwith "allocate: array not supported yet"
    | _ -> 
      let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
      let code = [INCSP 1]
      (newEnv, code)
                      
/// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment                          
   let labend   = newLabel()
   let labbegin = newLabel()
   let rec CS vEnv fEnv = function
       | PrintLn e        -> CE vEnv fEnv e @ [PRINTI; INCSP -1] 

       | Ass(acc,e)       -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]

       | Block([],stms)    -> CSs vEnv fEnv stms
       | Block(decs, stms) -> 
                              // The following code is based on the provided Micro-C project (P. Sestoft).
                              let rec loop vEnv = function
                                | VarDec(typ, x)::dr -> 
                                    let (varEnv1, code1) = allocate LocVar (typ, x) vEnv 
                                    let (fdepthr, coder) = loop varEnv1 dr
                                    (fdepthr, code1 @ coder)
                                | [] | _    -> (vEnv, [])
                              let rec loop1 vEnv fEnv = function
                                | []     -> (vEnv, [])
                                | s1::sr -> 
                                    let (varEnv1, code1) = (vEnv, CS vEnv fEnv s1) 
                                    let (fdepthr, coder) = loop1 varEnv1 fEnv sr
                                    (fdepthr, code1 @ coder)
                              let (vEnv1, code1) = loop vEnv decs
                              let (vEnv2, code2) = loop1 vEnv1 fEnv stms
                              code1 @ code2 @ [INCSP -(snd vEnv)]
                              
       | Alt (GC(gcs))   -> CSGCAlt vEnv fEnv gcs

       | Do (GC(gcs))    -> [Label labbegin] @ CSGCDo vEnv fEnv gcs
       | Return (Some e) -> CE vEnv fEnv e @ [RET (snd vEnv)]
       | Return None     -> failwith "CS: return procedures"
       | _ -> failwith "CS: not supported yet..."

   and CSs vEnv fEnv stms = List.collect (CS vEnv fEnv) stms 
  
   (*
   and cStmtOrDec block vEnv fEnv =  
    match block with
    | Block(decs, stms) -> let ((vEnv, fdepth),code) = allocate LocVar (typ, x) vEnv 
                           let (c,d) = (vEnv, CS stmt vEnv fEnv)
                           ()
*)
   and CSGCDo vEnv fEnv = function 
     | (((exp:Exp), (stms:Stm list))::gc) -> let labfalse = newLabel()
                                             CE vEnv fEnv exp @ [IFZERO labfalse] @ CSs vEnv fEnv stms @ [GOTO labbegin; Label labfalse] @ CSGCDo vEnv fEnv gc
     | _ -> []

   and CSGCAlt vEnv fEnv = function 
     | (((exp:Exp), (stms:Stm list))::gc) -> let labfalse = newLabel()
                                             CE vEnv fEnv exp @ [IFZERO labfalse] @ CSs vEnv fEnv stms @ [GOTO labend; Label labfalse] @ CSGCAlt vEnv fEnv gc
     | _ -> [STOP; Label labend]

(* ------------------------------------------------------------------- *)

   
(* Build environments for global variables and functions *)

   let makeGlobalEnvs decs = 
       let rec addv decs vEnv fEnv = 
           match decs with 
           | []         -> (vEnv, fEnv, [])
           | dec::decr  -> 
             match dec with
             | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                    let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                    (vEnv2, fEnv2, code1 @ code2)
             | FunDec (tyOpt, f, xs, body) ->  let (vEnv1, _ ,code1) = addv xs vEnv fEnv
                                               let (_, fvEnv2 ,code2) = addv decr vEnv1 (Map.add f (newLabel(), tyOpt, xs) fEnv)
                                               (vEnv1, fvEnv2, code1 @ code2)
       addv decs (Map.empty, 0) Map.empty

  
/// CP prog gives the code for a program prog
   let CP (P(decs,stms)) = 
       let _ = resetLabels ()
       let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs

       // The following code is based on the provided Micro-C project (P. Sestoft).
       let compilefun (tyOpt, f, xs, body) =
           let (labf, _, paras) = Map.find f fEnv
           let (envf, fdepthf) = bindParams paras (gvM, 0)
           let code = CS (envf, fdepthf) fEnv body
           [Label labf] @ code @ [RET (paras.Length-1)]
       let functions = 
              List.choose (function 
                               | FunDec (rTy, name, argTy, body) -> Some (compilefun (rTy, name, argTy, body))
                               | VarDec _                        -> None) decs       
       initCode @ CSs gvEnv fEnv stms @ [STOP] @ List.concat functions



