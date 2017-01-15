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
    | Apply(s,exp) -> Node("Apply", (Node(s,[]))::List.map(fun e -> expToTree e) exp)
and accToTree = function
    | AVar s -> Node("AVar", [Node(s, [])])
    | AIndex(acc,e) -> Node("AIndex", [accToTree acc] @ [expToTree e])
    | ADeref e -> Node("ADeref", [expToTree e])
and stmToTree = function
    | PrintLn _ -> Node("Println", [])
    | Alt gc -> Node("Alt", [gcToTree gc])
    | Do gc -> Node("Do", [gcToTree gc])
    | Ass(acc,e) -> Node("Ass", [accToTree acc] @ [expToTree e])
    | Block([], stms) -> Node("Block", stmsToTree stms)
    | Block(decs, stms) -> Node("Block", decsToTree decs @ stmsToTree stms)
    | Call(s, exps) -> Node("Call", expsToTree exps)
    | Return(Some e) -> Node("Return", [expToTree e])
    | Return(None) -> Node("Return", [])
and decToTree = function
    | VarDec(typ, s) -> Node("VarDec", Node(s,[])::[typToTree typ])
    | FunDec(typ, s, decs, stm) -> Node("FunDec", [])
and typToTree = function
    | ITyp -> Node("ITyp", [])
    | BTyp -> Node("BTyp", [])
    | ATyp(typ,Some i)-> Node("ATyp", [])
    | ATyp(typ, None)-> Node("ATyp", [])
    | PTyp typ -> Node("PTyp", [typToTree typ])
    | FTyp (typs, Some(typ)) -> Node("FTyp", List.map(fun typ -> typToTree typ) typs @ [typToTree typ])
    | FTyp (typs, None) -> Node("FTyp", List.map(fun typ -> typToTree typ) typs)
and expsToTree exps = List.map(fun exp -> expToTree exp) exps
and stmsToTree stms = List.map(fun stm -> stmToTree stm) stms
and decsToTree decs = List.map(fun dec -> decToTree dec) decs
and gcToTree (GC(gc)) = Node("GC", List.fold(fun r (e,stms) -> (expToTree e)::stmsToTree stms @ r) [] gc)
and pToTree (P(decs,stms):Program) = Node("P", decsToTree decs @ stmsToTree stms)

let l = parseFromFile "Ex5.gc"
let p = pToTree l
let d = design p

(*
 * Cheat below.
*)

let lineHeight = 50.0;;
let lineWidth  = 60.0;;
let rootx = 0.0;;
let rooty = 0.0;;
let labelpadding = 10.0;
let labelToPSString label = "("+ label + ") dup stringwidth pop 2 div neg 0 rmoveto show";

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



let labelToPSStringSB (builder : StringBuilder) (label : string) = builder.Append "(" 
                                                                   builder.Append label 
                                                                   builder.Append ") dup stringwidth pop 2 div neg 0 rmoveto show"
                                                                   builder;;

let treePrintSB' tree = 
    let rec treePrintSB node level (sb : StringBuilder) =
        match node with 
        | Node ((label, reflPos),[])      -> let (abs_x, abs_y) = (absoluteOffsetSB level reflPos)
                                             sb.Append (string abs_x)
                                             sb.Append " " 
                                             sb.Append (string abs_y)
                                             sb.Append " moveto\n"
                                             let sb2 = (labelToPSStringSB sb label) 
                                             sb2.Append "\n"
                                             sb2
        | Node ((label, reflPos),subtree) -> let (abs_x, abs_y) = (absoluteOffset level reflPos)
                                             sb.Append (string abs_x) 
                                             sb.Append " " 
                                             sb.Append (string abs_y) 
                                             sb.Append " moveto\n" 
                                             let sb2 = (labelToPSStringSB sb label) 
                                             sb2.Append "\n" 
                                             let sb3 = (subtreePrintSB (subtree,level+1.0, reflPos, sb2))
                                             sb3
    and absoluteOffsetSB level reflectPos = ((reflectPos * lineWidth) + rootx), (rooty - (level * lineHeight))
    and subtreePrintSB = function
      | [],level,parentReflPos, sb                                  -> sb
      | Node ((label, reflPos),subtree)::rest,level,parentReflPos, sb -> let (abs_par_x, abs_par_y) = (absoluteOffsetSB (level-1.0) parentReflPos)
                                                                         let (abs_x, abs_y) = (absoluteOffsetSB level (reflPos+parentReflPos))
                                                                         let abs_x1 = abs_par_x + (reflPos*lineWidth)
                                                                         sb.Append (string (abs_par_x))
                                                                         sb.Append " " 
                                                                         sb.Append (string (abs_par_y-labelpadding)) 
                                                                         sb.Append " moveto\n" 
                                                                         sb.Append (string (abs_x1))
                                                                         sb.Append " " 
                                                                         sb.Append (string (abs_par_y-labelpadding))
                                                                         sb.Append " lineto\n" 
                                                                         sb.Append (string (abs_x1))
                                                                         sb.Append " " 
                                                                         sb.Append (string (abs_y+labelpadding))
                                                                         sb.Append " lineto\n" 
                                                                         sb.Append " stroke\n" 
                                                                         let sb2 = (treePrintSB (Node ((label, reflPos+parentReflPos),subtree)) level sb)
                                                                         let sb3 = (subtreePrintSB (rest,level,parentReflPos, sb2))
                                                                         sb3
    let sb = StringBuilder()
    let result = treePrintSB tree 1.0 sb
    result.ToString();;


let labelToPSStringCon label = let strings = seq["("; label; ") dup stringwidth pop 2 div neg 0 rmoveto show"]
                               String.concat "" strings;;


let rec treePrintCon node level = 
  match node with 
  | Node ((label, reflPos),[])      -> let (abs_x, abs_y) = (absoluteOffsetCon level reflPos)
                                       let strings = seq[(string abs_x); " "; (string abs_y); " moveto\n";
                                                         (labelToPSStringCon label); "\n"]
                                       String.concat "" strings
  | Node ((label, reflPos),subtree) -> let (abs_x, abs_y) = (absoluteOffsetCon level reflPos)
                                       let strings = seq[(string abs_x); " "; (string abs_y); " moveto\n";
                                                         (labelToPSStringCon label); "\n";
                                                          subtreePrintCon (subtree,level+1.0, reflPos)];
                                       String.concat "" strings
and absoluteOffsetCon level reflectPos = ((reflectPos * lineWidth) + rootx), (rooty - (level * lineHeight))
and subtreePrintCon = function
  | [],level,parentReflPos                                  -> ""
  | Node ((label, reflPos),subtree)::rest,level,parentReflPos -> let (abs_par_x, abs_par_y) = (absoluteOffsetCon (level-1.0) parentReflPos)
                                                                 let (abs_x, abs_y) = (absoluteOffset level (reflPos+parentReflPos))
                                                                 let abs_x1 = abs_par_x + (reflPos*lineWidth)
                                                                 let strings = seq[string (abs_par_x); " "; string (abs_par_y-labelpadding);
                                                                                 " moveto\n"; string (abs_x1); " "; string (abs_par_y-labelpadding);
                                                                                 " lineto\n"; string (abs_x1); " "; string (abs_y+labelpadding);
                                                                                 " lineto\n"; " stroke\n"; 
                                                                                 treePrintCon (Node ((label, reflPos+parentReflPos),subtree)) level;
                                                                                 subtreePrintCon (rest,level,parentReflPos)]
                                                                 let result = String.concat "" strings
                                                                 // printf "%s\n" result
                                                                 result;;

let PSheader = "%!\n<</PageSize[1400 1000]/ImagingBBox null>> setpagedevice\n1 1 scale\n700 999 translate\nnewpath\n/Times-Roman findfont 10  scalefont setfont\n";;
let PSfooter = "showpage";;


let PSFileWrite path tree = File.WriteAllText (path, PSheader + (treePrint tree 1.0) + PSfooter);;
let PSFileWriteSB path tree = File.WriteAllText (path, PSheader + (treePrintSB' tree) + PSfooter);;
let PSFileWriteCon path tree = File.WriteAllText (path, PSheader + (treePrintCon tree 1.0) + PSfooter);;

#time "on";;

//PSFileWrite "fig6.ps" (design fig6);;
//PSFileWrite "fig6a.ps" (design fig6a);;

// =================================================
// Time testing 
// =================================================
let l1 = parseFromFile "Ex5.gc"
let p1 = pToTree l1
let d1 = design p1
printf "%s" "Typical concatenation\n";;
PSFileWrite "1a_lol.ps" (d1);;
printf "%s" "StringBuilder concatenation\n";;
PSFileWriteSB "1b_lol.ps" (d1);;
printf "%s" "String.concat concatenation\n";;
PSFileWriteCon "1c_lol.ps" (d1);;
