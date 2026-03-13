(* # 1 "src/lambda/order.sig.ml" *)
open! Basis
open Intsyn

(* Termination Order *)
(* Author: Carsten Schuermann *)
module type ORDER = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  type 'a order_ = Arg of 'a | Lex of 'a order_ list | Simul of 'a order_ list

  (* Orders                     *)
  (* O ::= x                    *)
  (*     | {O1 .. On}           *)
  (*     | [O1 .. On]           *)
  type predicate_ =
    | Less of int order_ * int order_
    | Leq of int order_ * int order_
    | Eq of int order_ * int order_

  (* Reduction Order            *)
  (* O < O'                     *)
  (* O <= O'                    *)
  (* O = O'                     *)
  type mutual_ =
    | Empty
    | Le of IntSyn.cid * mutual_
    | Lt of IntSyn.cid * mutual_

  (* Termination ordering       *)
  (* O ::= No order specified   *)
  (*     | mutual dependencies  *)
  (*     | lex order for  -     *)
  type tDec_ = TDec of int order_ * mutual_

  (* Termination declaration *)
  type rDec_ = RDec of predicate_ * mutual_

  (* Reduction declaration      *)
  val reset : unit -> unit
  val resetROrder : unit -> unit
  val install : IntSyn.cid * tDec_ -> unit
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * rDec_ -> unit
  val uninstallROrder : IntSyn.cid -> bool
  val selLookup : IntSyn.cid -> int order_
  val selLookupROrder : IntSyn.cid -> predicate_
  val mutLookup : IntSyn.cid -> mutual_
  val closure : IntSyn.cid -> IntSyn.cid list
end
(* signature ORDER *)

(* # 1 "src/lambda/order.fun.ml" *)
open! Basis
open Intsyn
open Table.Table_

(* Terminiation and Reduction Order *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module MakeOrder (Order__0 : sig
  module Table : TABLE with type key = int
end) : ORDER = struct
  open Order__0

  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  type 'a order_ = Arg of 'a | Lex of 'a order_ list | Simul of 'a order_ list

  (* Orders                     *)
  (* O ::= x                    *)
  (*     | {O1 .. On}           *)
  (*     | [O1 .. On]           *)
  type predicate_ =
    | Less of int order_ * int order_
    | Leq of int order_ * int order_
    | Eq of int order_ * int order_

  (* Mutual dependencies in call patterns:                            *)
  (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
  (* that the proof of ai can refer to                                *)
  (*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
  (* and to                                                           *)
  (*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
  (* then the ones of ai.                                             *)
  type mutual_ =
    | Empty
    | Le of IntSyn.cid * mutual_
    | Lt of IntSyn.cid * mutual_

  (* Mutual dependencies        *)
  (* C ::= .                    *)
  (*     |  <= (a) C            *)
  (*     |  > (a) C             *)
  type tDec_ = TDec of int order_ * mutual_

  (* Termination declaration    *)
  (* TDec ::= (O, C)            *)
  type rDec_ = RDec of predicate_ * mutual_

  (* Reduction declaration      *)
  (* RDec ::= (P, C)            *)
  open! struct
    module I = IntSyn

    let orderTable_ : tDec_ Table.table_ = Table.new_ 0
    let redOrderTable_ : rDec_ Table.table_ = Table.new_ 0
    let rec reset () = Table.clear orderTable_
    let rec resetROrder () = Table.clear redOrderTable_
    let rec install (cid, o_) = Table.insert orderTable_ (cid, o_)

    let rec uninstall cid =
      begin match Table.lookup orderTable_ cid with
      | None -> false
      | Some _ -> begin
          Table.delete orderTable_ cid;
          true
        end
      end

    let rec installROrder (cid, p_) = Table.insert redOrderTable_ (cid, p_)

    let rec uninstallROrder cid =
      begin match Table.lookup redOrderTable_ cid with
      | None -> false
      | Some _ -> begin
          Table.delete redOrderTable_ cid;
          true
        end
      end

    let rec lookup cid = Table.lookup orderTable_ cid
    let rec lookupROrder cid = Table.lookup redOrderTable_ cid

    let rec selLookup a =
      begin match lookup a with
      | None ->
          raise
            (Error
               ("No termination order assigned for "
               ^ I.conDecName (I.sgnLookup a)))
      | Some (TDec (s_, _)) -> s_
      end

    let rec selLookupROrder a =
      begin match lookupROrder a with
      | None ->
          raise
            (Error
               (("No reduction order assigned for "
                ^ I.conDecName (I.sgnLookup a))
               ^ "."))
      | Some (RDec (p_, _)) -> p_
      end

    let rec mutLookupROrder a =
      begin match lookupROrder a with
      | None ->
          raise
            (Error
               (("No order assigned for " ^ I.conDecName (I.sgnLookup a)) ^ "."))
      | Some (RDec (_, m_)) -> m_
      end

    let rec mutLookup a =
      begin match lookup a with
      | None ->
          raise
            (Error ("No order assigned for " ^ I.conDecName (I.sgnLookup a)))
      | Some (TDec (_, m_)) -> m_
      end

    let rec mutual a =
      let rec mutual' = function
        | Empty, a's -> a's
        | Le (a, m_), a's -> mutual' (m_, a :: a's)
        | Lt (a, m_), a's -> mutual' (m_, a :: a's)
      in
      mutual' (mutLookup a, [])

    let rec closure = function
      | [], a2s -> a2s
      | a :: a1s, a2s -> begin
          if List.exists (function a' -> a = a') a2s then closure (a1s, a2s)
          else closure (mutual a @ a1s, a :: a2s)
        end
  end

  (* mutual a = a's

       Invariant:
       If   a occurs in a call pattern (a1 P1) .. (an Pn)
       then a's = a1 .. an
    *)
  (* closure (a1s, a2s) = a3s

       Invariant:
       If   a1s  and a2s are lists of type families,
       then a3s is a list of type fmailies, which are mutual recursive to each other
       and include a1s and a2s.
    *)
  let reset = reset
  let resetROrder = resetROrder
  let install = install
  let uninstall = uninstall
  let installROrder = installROrder
  let uninstallROrder = uninstallROrder
  let selLookup = selLookup
  let selLookupROrder = selLookupROrder
  let mutLookup = mutLookup
  let closure = function a -> closure ([ a ], [])
end

(*! structure IntSyn' : INTSYN !*)
(* local *)
(* functor Order *)

(* # 1 "src/lambda/order.sml.ml" *)
open! Basis
open Table.Table_instances

module Order = MakeOrder (struct
  (*! structure IntSyn' = IntSyn !*) module Table = IntRedBlackTree
end)

include Order
(* -bp *)
(*
structure RedOrder = 
    RedOrder (! structure IntSyn' = IntSyn !
	      structure Table = IntRedBlackTree); 
*)
