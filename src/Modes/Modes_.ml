open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_

(* # 1 "src/modes/Modes_.sig.ml" *)

(* # 1 "src/modes/Modes_.fun.ml" *)

(* # 1 "src/modes/Modes_.sml.ml" *)
open! Basis

(* structure ModeSyn  in Modesyn.sml *)
module ModeSyn = Modesyn.ModeSyn
module ModeTable = Modetable.MakeModeTable (TableInstances.IntRedBlackTree)
module ModeDec = Modedec.MakeModeDec (struct end)
module ModeCheck = Modecheck.MakeModeCheck (ModeTable) (Whnf) (Index) (Origins)
module ModePrint = Modeprint.MakeModePrint (Names) (Formatter) (Print)
