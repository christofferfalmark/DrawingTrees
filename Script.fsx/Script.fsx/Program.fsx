System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

#I @"C:\Users\Christoffer\Dropbox\DTU Master\3. Semester E16\02257 Applied functional programming\Project 2\Compiler\GuardedCommands\GuardedCommands"
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

(*
 * Cheat below.
*)

let lineHeight = 50.0;;
let lineWidth  = 60.0;;
let rootx = 0.0;;
let rooty = 0.0;;
let labelpadding = 10.0;
let labelToPSString label = "("+ label + ") dup stringwidth pop 2 div neg 0 rmoveto show";

let rec treePrint level = function
    | Node((label, pos), []) -> let  (x, y) = (calcOffset level pos)
                                (string x) + " " + (string y) + " moveto\n" + 
                                (labelToPSString label) + "\n"
    | Node((label, pos), st) -> let (abs_x, abs_y) = (calcOffset level pos)
                                (string abs_x) + " " + (string abs_y) + " moveto\n" + 
                                (labelToPSString label) + "\n"  + 
                                stPrint (st, level+1.0, pos)
and stPrint = function
    | ([], level, ppos)    -> ""
    | ((Node((l, p), st))::rest, level, ppos) -> let (p_x, p_y) = calcOffset level ppos
                                                string (p_x + p) + " " + string (p_y) + " moveto\n" +
                                                string (p_x + p) + " " + string (p_y + lineHeight) + " lineto\n" + 
                                                stPrint (st, level, ppos) +
                                                "stroke\n" +
                                                treePrint (level+1.0) ((Node((l, p), st')))
and calcOffset level pos = (rootx + (pos * lineWidth), rooty - (level * lineHeight))

   


let rec treePrint node level = 
  match node with 
  | Node ((label, reflPos),[])      -> let (abs_x, abs_y) = (absoluteOffset level reflPos)
                                       (string abs_x) + " " + (string abs_y) + " moveto\n" +
                                        (labelToPSString label) + "\n"
  | Node ((label, reflPos),subtree) -> let (abs_x, abs_y) = (absoluteOffset level reflPos)
                                       (string abs_x) + " " + (string abs_y) + " moveto\n" +
                                       (labelToPSString label) + "\n" +
                                       subtreePrint (subtree,level+1.0, reflPos)
and absoluteOffset level reflectPos = ((reflectPos * lineWidth) + rootx), (rooty - (level * lineHeight))
and subtreePrint = function
  | [],level,parentReflPos                                  -> ""
  | Node ((label, reflPos),subtree)::rest,level,parentReflPos -> let (abs_par_x, abs_par_y) = (absoluteOffset (level-1.0) parentReflPos)
                                                                 let (abs_x, abs_y) = (absoluteOffset level (reflPos+parentReflPos))
                                                                 let abs_x1 = abs_par_x + (reflPos*lineWidth)
                                                                 string (abs_par_x) + " " + string (abs_par_y-labelpadding) + " moveto\n" +
                                                                 string (abs_x1)     + " " + string (abs_par_y-labelpadding)     + " lineto\n" +
                                                                 string (abs_x1)     + " " + string (abs_y+labelpadding)     + " lineto\n" +
                                                                 " stroke\n" + 
                                                                 treePrint (Node ((label, reflPos+parentReflPos),subtree)) level + 
                                                                 subtreePrint (rest,level,parentReflPos);;


let PSheader = "%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 10  scalefont setfont\n";;
let PSfooter = "showpage";;
let writePStoFile path tree = File.WriteAllText (path, PSheader + (treePrint 1.0 tree) + PSfooter);;

let PSFileWrite path tree = File.WriteAllText (path, PSheader + (treePrint tree 1.0) + PSfooter);;

// let PSFileWrite path tree = File.WriteAllText (path, PSheader + (treePrint tree 1.0) + PSfooter);;
// let PSFileWriteSB path tree = File.WriteAllText (path, PSheader + (treePrintSB' tree) + PSfooter);;
// let PSFileWriteCon path tree = File.WriteAllText (path, PSheader + (treePrintCon tree 1.0) + PSfooter);;


#time "on";;

// =================================================
// Time testing 
// =================================================
let d1 = design (pToTree (parseFromFile "Ex0.gc"))
printf "%s" "Typical concatenation\n"
writePStoFile "1a_lol.ps" (d1)
// printf "%s" "StringBuilder concatenation\n"
// PSFileWriteSB "1b_lol.ps" (d1)
// printf "%s" "String.concat concatenation\n"
// PSFileWriteCon "1c_lol.ps" (d1))