open! Table
open! Intsyn.Lambda_
open! Print.Print_
open! Names.Names_
open! Paths
open! Index.Index_

(* # 1 "src/modes/Modes_.sig.ml" *)

(* # 1 "src/modes/Modes_.fun.ml" *)

(* # 1 "src/modes/Modes_.sml.ml" *)

(* structure ModeSyn  in Modesyn.sml *)
module ModeSyn = Modesyn.ModeSyn
module ModeTable = Modetable.MakeModeTable (TableInstances.IntRedBlackTree)
module ModeDec = Modedec.MakeModeDec (struct end)
module ModeCheck = Modecheck.MakeModeCheck (ModeTable) (Whnf) (Index) (Origins)
module ModePrint = Modeprint.MakeModePrint (Names) (Formatter) (Print)
