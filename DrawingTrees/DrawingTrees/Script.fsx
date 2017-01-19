// Michael R. Hansen 05-01-2016

System.IO.Directory.SetCurrentDirectory __SOURCE_DIRECTORY__;;

// You must revise 4 pathes occurring in this file 
// The first three are:
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


open GuardedCommands.Util
open GuardedCommands.Frontend.TypeCheck
open GuardedCommands.Frontend.AST
open GuardedCommands.Backend.CodeGeneration

open ParserUtil
open CompilerUtil

open Machine
open VirtualMachine

// Test of programs covered by the first task (Section 3.7):
List.iter exec ["Ex1.gc"; "Ex2.gc";"Ex3.gc"; "Ex4.gc"; "Ex5.gc"; "Ex6.gc"; "Skip.gc"];;
exec "Ex5.gc"
// Test program that fails because of an illformed guarded command
// exec "ExGC_fail.gc"

// Test of programs covered by the second task (Section 4.3):
List.iter exec ["Ex7.gc"; "fact.gc"; "factRec.gc"; "factCBV.gc"];;

// Test of programs where the type-checker detects error(s) 
// exec "Ex7_Error.gc"

// Test of programs covered by the fourth task (Section 5.4):
// List.iter exec ["A0.gc"; "A1.gc"; "A2.gc"; "A3.gc"];;

(*
// Test of programs covered by the fifth task (Section 6.1):
List.iter exec ["A4.gc"; "Swap.gc"; "QuickSortV1.gc"];;

// Test of programs covered by the fifth task (Section 7.4):
List.iter exec ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"; "par2.gc"];;

// Test of programs covered by the fifth task using optimized compilation (Section 8.2):
List.iter execOpt ["par1.gc"; "factImpPTyp.gc"; "QuickSortV2.gc"; "par2.gc"];;

*)

