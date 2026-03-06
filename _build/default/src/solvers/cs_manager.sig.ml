open! Basis;;
(* Constraint Solver Manager *);;
(* Author: Roberto Virga *);;
module type CS_MANAGER = sig
                         (* structure IntSyn : INTSYN *)
                         module Fixity : FIXITY
                         (*! structure ModeSyn : MODESYN !*)
                         type nonrec sigEntry =
                           IntSyn.conDec_ *
                           Fixity.fixity
                           option *
                           ModeSyn.modeSpine_
                           list
                         (* global signature entry *)
                         (* constant declaration plus optional precedence and mode information *)
                         type nonrec __0 = {
                           parse: string -> IntSyn.conDec_ option }
                         type nonrec fgnConDec = __0
                         (* foreign constant declaration *)
                         type nonrec __1 = { name: string ;
                           keywords: string ; needs: string list ;
                           fgnConst: fgnConDec option ;
                           init: (int * (sigEntry -> IntSyn.cid)) -> unit ;
                           reset: unit -> unit ; mark: unit -> unit ;
                           unwind: unit -> unit }
                         type nonrec solver = __1
                         (* constraint solver *)
                         exception Error of string 
                         (* solver handling functions *)
                         val setInstallFN : (sigEntry -> IntSyn.cid) -> unit
                         val installSolver : solver -> IntSyn.csid
                         val resetSolvers : unit -> unit
                         val useSolver : string -> unit
                         (* parsing foreign constatnts *)
                         val
                           parse : string ->
                                   (IntSyn.csid * IntSyn.conDec_)
                                   option
                         (* trailing operations *)
                         val reset : unit -> unit
                         val trail : (unit -> 'a) -> 'a
                         end;;
(* signature CS_MANAGER *);;