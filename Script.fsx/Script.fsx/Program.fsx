
System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

#I @"C:\Users\Christoffer\Dropbox\DTU Master\3. Semester E16\02257 Applied functional programming\Project 2\Compiler\GuardedCommands\GuardedCommands"
//#I @"..\..\..\GuardedCommands\GuardedCommands"
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

// moveextent : Extent * float -> Extent
let moveextent (e : Extent, x) = List.map (fun (p,q) -> (p+x,q+x)) e;;

// movetree : ('a * float) Tree * float -> ('a * float) Tree
let movetree (Node((label, x), subtrees), x' : float) = Node((label, x + x'), subtrees)

// merge : ('a * 'b) list * ('a * 'b) list -> ('a * 'b) list
let rec merge = function 
    | ([], []) -> []
    | (ps, []) -> ps
    | ([], qs) -> qs
    | ((p,_)::ps, (_,q)::qs) -> (p,q)::merge(ps, qs)

// mergelist : ('a * 'b) list list -> ('a * 'b) list
let mergelist es = List.fold (fun acc e -> merge (acc, e)) [] es ;;

// rmax : float * float -> float
let rmax (p, q) = if p > q then p else q

// fit : ('a * float) list * (float * 'b) list -> float
let rec fit = function
    | ((_,p)::ps, (q,_)::qs) -> rmax(fit (ps,qs), p-q + 1.0)
    | (_,_) -> 0.0

// fitlistl : Extent list -> float list
let fitlistl es = 
    let rec fitlistl' = function
        | (acc, []) -> []
        | (acc, (e::es)) -> let x = fit(acc, e)
                            x::fitlistl' (merge (acc, moveextent(e,x)), es)
    fitlistl'([], es)

// fitlistr : Extent list -> float list
let fitlistr es =
    let rec fitlistr' = function
        | (acc, []) -> []
        | (acc, e::es) -> let x = fit(e,acc) * -1.0
                          x::fitlistr' (merge (moveextent(e,x), acc), es)
    List.rev(fitlistr' ([], (List.rev es)))

// mean : float * float -> float
let mean (x, y) = (x+y) / 2.0

// fitlist Extent list -> float list
let fitlist es = List.map(fun (x,y) -> mean(x, y)) (List.zip (fitlistl es) (fitlistr es))

// 'a Tree -> ('a * float) Tree
let design tree = 
    // design' 'a Tree -> ('a * float) Tree * Extent
    let rec design' (Node(label, subtrees)) =
        let (trees, extents) = List.unzip (List.map(fun s -> design' s) subtrees)
        let positions = fitlist extents
        let ptrees = List.map(fun x -> movetree x) (List.zip trees positions)
        let pextents = List.map(fun x -> moveextent x) (List.zip extents positions)
        let resultextent = (0.0, 0.0) :: mergelist pextents
        let resulttree = Node((label, 0.0), ptrees)
        (resulttree, resultextent)
    fst(design' tree)

let rec expToTree = function
    | N n          -> Node(string n, [])
    | B b          -> Node(string b, [])
    | Access a     -> Node("Access", [accToTree a])
    | Addr a       -> Node("Addr", [accToTree a])
    | Apply(s,exp) -> Node("Apply", [sToTree s] @ List.map(fun e -> expToTree e) exp)

and accToTree = function
    | AVar s -> sToTree s
    | AIndex(acc,e) -> Node("AIndex", [accToTree acc] @ [expToTree e])
    | ADeref e -> Node("ADeref", [expToTree e])

and stmToTree = function
    | PrintLn e -> Node("Println", [expToTree e])
    | Alt gc -> Node("Alt", [gcToTree gc])
    | Do gc -> Node("Do", [gcToTree gc])
    | Ass(acc,e) -> Node("Ass", [accToTree acc] @ [expToTree e])
    | Block([], stms) -> Node("Block", stmsToTree stms)
    | Block(decs, stms) -> Node("Block", decsToTree decs @ stmsToTree stms)
    | Call(s, exps) -> Node("Call", expsToTree exps)
    | Return(Some e) -> Node("Return", [expToTree e])
    | Return(None) -> Node("Return", [])

and decToTree = function
    | VarDec(typ, s) -> Node("VarDec", [sToTree s] @ [typToTree typ])
    | FunDec(Some(typ), s, decs, stm) -> Node("FunDec", [sToTree s] @  [typToTree typ] @ decsToTree decs @ [stmToTree stm])
    | FunDec(None, s, decs, stm) -> Node("ProcDec", [sToTree s] @ decsToTree decs @ [stmToTree stm])

and typToTree = function
    | ITyp -> Node("ITyp", [])
    | BTyp -> Node("BTyp", [])
    | ATyp(typ,Some i)-> Node("ATyp", [])
    | ATyp(typ, None)-> Node("ATyp", [])
    | PTyp typ -> Node("PTyp", [typToTree typ])
    | FTyp (typs, Some(typ)) -> Node("FTyp", List.map(fun typ -> typToTree typ) typs @ [typToTree typ])
    | FTyp (typs, None) -> Node("FTyp", List.map(fun typ -> typToTree typ) typs)

and sToTree s = Node("\"" + s + "\"", [])
and expsToTree exps = List.map(fun exp -> expToTree exp) exps
and stmsToTree stms = List.map(fun stm -> stmToTree stm) stms
and decsToTree decs = List.map(fun dec -> decToTree dec) decs
and gcToTree (GC(gc)) = Node("GC", List.fold(fun r (e,stms) -> (expToTree e)::stmsToTree stms @ r) [] gc)
and pToTree (P(decs,stms):Program) = Node("P", decsToTree decs @ stmsToTree stms)


// Convert the Tree to a PostScript file.
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

// String.concat method:
let moveToConcat level pos = let x = string((pos*width) + fst root)
                             let y = string((snd root - (level * height)))
                             String.concat "" [x; " "; y ; " moveto\n"]
let printLabelConcat level pos s = String.concat "" [(moveToConcat level pos); "("; s; ") dup stringwidth pop 2 div neg 0 rmoveto show\n"]
let doActionConcat x y action = String.concat "" [" "; string x; " "; string y; " "; string action; "\n"]

let rec printTreeConcat level = function
    | Node((s, pos), [])        -> String.concat "" ["stroke\n"; printLabelConcat level pos s]
    | Node((s, pos), subtrees)  -> String.concat "" ["stroke\n"; printLabelConcat level pos s; subTreeConcat(subtrees, level+1.0, pos)]
and subTreeConcat = function
    | ([], level, pos) -> ""
    | (Node((s, pos), subtree)::l, level, parent)  ->  let (px,py) = coordinate parent (level-1.0)
                                                       let (x, y) = coordinate (pos+parent) level
                                                       let strs = [doActionConcat px (py-padding) "moveto"; doActionConcat px (py-20.0) "lineto"; doActionConcat x (py-20.0) "lineto"; doAction x (py-30.0) "lineto"; 
                                                                   printTreeConcat level (Node((s, pos+parent), subtree)); subTreeConcat (l, level, parent)]
                                                       String.concat "" strs

let header = "%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 10 scalefont setfont\n"

let writeToPS path tree = File.WriteAllText (path,  header + (printTree 1.0 tree) + "\nshowpage");;
let writeToPSConcat path tree = File.WriteAllText (path, String.concat "" [header; ((printTreeConcat 1.0 tree)); "\nshowpage"]);;
#time "on";;
writeToPS "1a_ex0.ps" (design (pToTree (parseFromFile "Ex0.gc")))
#time "on";;
writeToPSConcat "1b_ex0.ps" (design (pToTree (parseFromFile "Ex0.gc")))

