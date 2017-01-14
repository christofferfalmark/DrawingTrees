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

let rec ExpTree = function
    | N _ -> Node("N", [])
    | B _ -> Node("B", [])
    | Access _ ->  Node("Access", [])
    | Addr _ -> Node("Addr", [])
    | Apply(_, e) -> Node("Apply", List.map (fun x -> ExpTree x) e)

and AccessTree = function   
    | AVar _ -> Node("AVar", []) 
    | AIndex (_, e) -> Node("AIndex", [ExpTree e])
    | ADeref e -> Node("ADeref", [ExpTree e])

and StmTree = function
    | PrintLn _ -> Node("PrintLn", [])
    | Ass (_, e) -> Node("Ass", [ExpTree e])
    | Return(Some(e)) -> Node("Return", [ExpTree e])
    | Return(None) -> Node("Return", [])
    | Call(_, e) -> Node("Call", List.map(fun x -> ExpTree x) e)
    | Block([], stms) -> Node("Block", List.map(fun x -> StmTree x) stms)
    | Block(decs, stms) -> Node("Block", (List.map(fun x -> StmTree x) stms) @ (List.map(fun x -> DecTree x) decs)) 
    | Alt (gc) -> Node("Alt", GCTree gc)
    | Do (gc) -> Node("Alt", GCTree gc)

and TypeTree = function
    | ITyp              -> Node("int", [])
    | BTyp              -> Node("bool", [])
    | ATyp(t, _)        -> Node("ATyp", [TypeTree t])
    | PTyp(t)           -> Node("PTyp", [TypeTree t])
    | FTyp(tl, Some(t)) -> Node("FTyp", List.map (fun x -> TypeTree x) tl @ [TypeTree t])
    | FTyp(tl, None) -> Node("FTyp", List.map (fun x -> TypeTree x) tl)

and DecTree = function
    | VarDec(t,_) -> Node("VarDec", [TypeTree t])
    | FunDec(Some(t),_, decl, stm) -> Node("FunDec", List.map (fun x -> DecTree x) decl @ [StmTree stm])
    | FunDec(None, _, _, _) -> Node("FunDec", [])

and GCTree = function
    | GC((e:Exp, s:Stm list)::l) -> [(ExpTree e)] @ (List.map(fun x -> StmTree x) s)
    | _ -> []