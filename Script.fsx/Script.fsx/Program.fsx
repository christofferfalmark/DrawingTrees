
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
open System.Text
open System.IO

type 'a Tree = Node of ('a * 'a Tree list);;
type Extent = (float*float) list;;

let moveextent (e : Extent, x) = List.map (fun (p,q) -> (p+x,q+x)) e;;

let movetree (Node((label, x), subtrees), x' : float) = Node((label, x+x'), subtrees)

let rec merge = function 
    | ([], []) -> []
    | (ps, []) -> ps
    | ([], qs) -> qs
    | ((p,_)::ps, (_,q)::qs) -> (p,q)::merge(ps, qs)

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

let rec ExpTree = function
    | N t -> Node("N", [Node(string(t), [])])
    | B t -> Node("B", [Node(string(t), [])])
    | Access a ->  Node("Access", [AccessTree a])
    | Addr a -> Node("Addr", [AccessTree a])
    | Apply(s, e) -> Node("Apply", [Node(s, [])] @ List.map (fun x -> ExpTree x) e)

and AccessTree = function   
    | AVar s -> Node("AVar", [Node(s, [])]) 
    | AIndex (a, e) -> Node("AIndex", [AccessTree a] @ [ExpTree e])
    | ADeref e -> Node("ADeref", [ExpTree e])

and StmTree = function
    | PrintLn e -> Node("PrintLn", [ExpTree e])
    | Ass (a, e) -> Node("Ass", [AccessTree a] @ [ExpTree e])
    | Return(Some(e)) -> Node("Return", [ExpTree e])
    | Return(None) -> Node("Return", [])
    | Call(s, e) -> Node("Apply", [Node(s, [])] @ List.map (fun x -> ExpTree x) e)
    | Block([], stms) -> Node("Block", List.map(fun x -> StmTree x) stms)
    | Block(decs, stms) -> Node("Block", (List.map(fun x -> StmTree x) stms) @ (List.map(fun x -> DecTree x) decs)) 
    | Alt (gc) -> Node("Alt", GCTree gc)
    | Do (gc) -> Node("Do", GCTree gc)

and TypeTree = function
    | ITyp              -> Node("int", [])
    | BTyp              -> Node("bool", [])
    | ATyp(t, _)        -> Node("ATyp", [TypeTree t])
    | PTyp(t)           -> Node("PTyp", [TypeTree t])
    | FTyp(tl, Some(t)) -> Node("FTyp", List.map (fun x -> TypeTree x) tl @ [TypeTree t])
    | FTyp(tl, None) -> Node("FTyp", List.map (fun x -> TypeTree x) tl)

and DecTree = function
    | VarDec(t,s) -> Node("VarDec", [Node(s, [])] @ [TypeTree t])
    | FunDec(Some(t),_, decl, stm) -> Node("FunDec", List.map (fun x -> DecTree x) decl @ [StmTree stm])
    | FunDec(None, _, _, _) -> Node("FunDec", [])

and GCTree = function
    | GC((e:Exp, s:Stm list)::l) -> [Node("GC", [(ExpTree e)] @ (List.map(fun x -> StmTree x) s))]
    | _ -> []

and decListToTree = function
    | []       -> []
    | d::dl-> (DecTree d) :: decListToTree dl

and stmListToTree = function
    | []       -> []
    | s::sl -> (StmTree s) :: stmListToTree sl

and pToTree (P(decs,stms):Program) = Node("P", decListToTree decs @ stmListToTree stms)

let height = 50.0
let padding = 10.0
let width = 50.0
let root = (0.0, 0.0)

let coordinate pos level = ((pos * width) + fst root, snd root - (level * height))

let moveTo level pos = string((pos * width) + fst root) + " " + string(snd root - (level * height)) + " moveto\n"

let printLabel level pos s = (moveTo level pos) + "("+ s + ") dup stringwidth pop 2 div neg 0 rmoveto show" + "\n"

let doAction x y action = string x + " " + string y + " " + action + "\n"

let rec printTree level = function
    | Node((s, pos), [])        -> "stroke\n" + (printLabel level pos s)
    | Node((s, pos), subtrees)  -> "stroke\n" + (printLabel level pos s) +
                                   subTree(subtrees, level+1.0, pos)
and subTree = function
    | ([], level, pos) -> ""
    | (Node((s, pos), subtree)::l, level, parent) -> let (px,py) = coordinate parent (level-1.0)
                                                     let (x, y) = coordinate (pos+parent) level
                                                     doAction px (py-padding) "moveto" + 
                                                     doAction px (py-20.0) "lineto" +
                                                     doAction x (py-20.0) "lineto" +
                                                     doAction x (py-30.0) "lineto" + 
                                                     printTree level (Node((s, pos+parent), subtree)) +
                                                     subTree(l, level, parent)

let header = "%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 10 scalefont setfont\n"

let PSFileWrite path tree = File.WriteAllText (path, header + (printTree 1.0 tree) + "\nshowpage");;
PSFileWrite "fact.ps" (design (pToTree (parseFromFile "fact.gc")))




