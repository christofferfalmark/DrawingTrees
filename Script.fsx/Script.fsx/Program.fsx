System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

//#I @"C:\Users\Christoffer\Dropbox\DTU Master\3. Semester E16\02257 Applied functional programming\Project 2\Compiler\GuardedCommands\GuardedCommands"
#I @"..\..\..\GuardedCommands\GuardedCommands"
#r @"bin\Debug\FSharp.PowerPack.dll";;
#r @"bin\Debug\Machine.dll";
#r @"bin\Debug\VirtualMachine.dll";

#load "AST.fs"
#load "Parser.fs"
#load "Lexer.fs"
#load "TypeCheck.fs"
#load "CodeGen.fs"
#load "CodeGenOpt.fs"
#load "Util.fs"

open GuardedCommands.Frontend.AST
open GuardedCommands.Util
open ParserUtil
open CompilerUtil

type 'a Tree = Node of ('a * 'a Tree list);;
type Extent = (float*float) list;;

let moveextent (e : Extent, x) = List.map (fun (p,q) -> (p+x,q+x)) e;;

let movetree (Node((label, x), subtrees), x' : float) = Node((label, x+x'), subtrees)

let rec merge = function 
    | ([], []) -> []
    | (ps, []) -> ps
    | ([], qs) -> qs
    | ((p,_)::ps, (_,q)::qs) -> (p,q)::merge(ps, qs)

// rewrite or something!
let mergelist es = List.fold (fun acc e -> merge (acc, e)) [] es ;;

let rmax (p : float, q : float) = if p > q then p else q

let rec fit = function
    | ((_,p)::ps, (q,_)::qs) -> rmax(fit (ps,qs), p-q + 1.0)
    | (_,_) -> 0.0

let fitlistl es = 
    let rec fitlistl' = function
        | (acc, []) -> []
        | (acc, (e::es)) -> let x = fit(acc, e)
                            x::fitlistl' (merge (acc, moveextent(e,x)), es)
    fitlistl'([], es)

let fitlistr es =
    let rec fitlistr' = function
        | (acc, []) -> []
        | (acc, e::es) -> let x = fit(e,acc) * -1.0
                          x::fitlistr' (merge (moveextent(e,x), acc), es)
    List.rev(fitlistr' ([], (List.rev es)))

let mean (x, y) = (x+y) / 2.0
let fitlist es = List.map(fun (x,y) -> mean(x, y)) (List.zip (fitlistl es) (fitlistr es))

let design tree = 
    let rec design' (Node(label, subtrees)) =
        let (trees, extents) = List.unzip (List.map(fun s -> design' s) subtrees)
        let positions = fitlist extents
        let ptrees = List.map(fun x -> movetree x) (List.zip trees positions)
        let pextents = List.map(fun x -> moveextent x) (List.zip extents positions)
        let resultextent = (0.0, 0.0) :: mergelist pextents
        let resulttree = Node((label, 0.0), ptrees)
        (resulttree, resultextent)
    fst(design' tree)


let l = parseFromFile "Ex5.gc"

let rec exp = function
    | N _ -> Node("N", [])
    | B _ -> Node("B", [])
    | Access _ ->  Node("Access", [])
    | Addr _ -> Node("Addr", [])
    | Apply(_, e) -> Node("Apply", List.map (fun x -> exp x) e)

and Access = function   
    | AVar _ -> Node("AVar", []) 
    | AIndex (_, e) -> Node("AIndex", [exp e])
    | ADeref e -> Node("ADeref", [exp e])
and Stm = function
    | PrintLn _ -> Node("PrintLn", [])
    | Ass (_, e) -> Node("Ass", [exp e])
    | Return(Some(e)) -> Node("Return", [exp e])
    | Call(_, e) -> Node("Call", List.map(fun x -> exp x) e)
    | Block([], stms) -> Node("Block", List.map(fun x -> Stm x) stms)
    | Block(decs, stms) -> Node("Block", (List.map(fun x -> Stm x) stms) @ (List.map(fun x -> Stm x) stms))     // Ændre sidste Stm til Dec...
and Dec = function
    | VarDec(t,_) -> Node("VarDec", )
    | FunDec(t,_) -> 
and Type = function
    | ITyp -> Node("int")
    | BTyp -> Node("bool")
    | ATyp  
    | PTyp of Typ                   (* Type pointer                *)
    | FTyp of Typ list * Typ option (* Type function and procedure *)

// TODO create function to convert l to the type 'a Tree
// let d = design l