open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_

(* # 1 "src/lambda/Order.sig.ml" *)
open! Basis
(** Termination and reduction order declarations for LF constants. *)

open Intsyn_

(* Termination Order *)
(* Author: Carsten Schuermann *)
include ORDER
(* signature ORDER *)

(* # 1 "src/lambda/Order.fun.ml" *)
open! Basis
open Intsyn_
open Table

(* Terminiation and Reduction Order *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module MakeOrder (M : sig
  module Table : TABLE with type key = int
end) : ORDER = struct
  open M

  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  type 'a order = Arg of 'a | Lex of 'a order list | Simul of 'a order list
  [@@deriving eq, ord, show]

  (* Orders                     *)
  (* O ::= x                    *)
  (*     | {O1 .. On}           *)
  (*     | [O1 .. On]           *)
  type predicate =
    | Less of int order * int order
    | Leq of int order * int order
    | Eq of int order * int order
  [@@deriving eq, ord, show]

  (* Mutual dependencies in call patterns:                            *)
  (* A call pattern   (a1 P1) .. (ai Pi) .. (an Pn)   expresses       *)
  (* that the proof of ai can refer to                                *)
  (*   ih a1 .. ai, as long as the arguments are strictly smaller     *)
  (* and to                                                           *)
  (*   ih a(i+1) .. an as long as the arguments are smaller or equal  *)
  (* then the ones of ai.                                             *)
  type mutual = Empty | Le of IntSyn.cid * mutual | Lt of IntSyn.cid * mutual
  [@@deriving eq, ord, show]

  (* Mutual dependencies        *)
  (* C ::= .                    *)
  (*     |  <= (a) C            *)
  (*     |  > (a) C             *)
  type tDec = TDec of int order * mutual [@@deriving eq, ord, show]

  (* Termination declaration    *)
  (* TDec ::= (O, C)            *)
  type rDec = RDec of predicate * mutual [@@deriving eq, ord, show]

  (* Reduction declaration      *)
  (* RDec ::= (P, C)            *)
  module I = IntSyn

  let orderTable : tDec Table.table = Table.new_ 0
  let redOrderTable : rDec Table.table = Table.new_ 0
  let reset () = Table.clear orderTable
  let reset_r_order () = Table.clear redOrderTable
  let install cid o_ = Table.insert orderTable (cid, o_)

  let uninstall cid =
    begin match Table.lookup orderTable cid with
    | None -> false
    | Some _ -> begin
        Table.delete orderTable cid;
        true
      end
    end

  let install_r_order cid p_ = Table.insert redOrderTable (cid, p_)

  let uninstall_r_order cid =
    begin match Table.lookup redOrderTable cid with
    | None -> false
    | Some _ -> begin
        Table.delete redOrderTable cid;
        true
      end
    end

  let lookup cid = Table.lookup orderTable cid
  let lookup_r_order cid = Table.lookup redOrderTable cid

  let sel_lookup a =
    begin match lookup a with
    | None ->
        raise
          (Error
             ("No termination order assigned for "
             ^ I.conDecName (I.sgnLookup a)))
    | Some (TDec (s_, _)) -> s_
    end

  let sel_lookup_r_order a =
    begin match lookup_r_order a with
    | None ->
        raise
          (Error
             (("No reduction order assigned for " ^ I.conDecName (I.sgnLookup a))
             ^ "."))
    | Some (RDec (p_, _)) -> p_
    end

  let mutLookupROrder a =
    begin match lookup_r_order a with
    | None ->
        raise
          (Error
             (("No order assigned for " ^ I.conDecName (I.sgnLookup a)) ^ "."))
    | Some (RDec (_, m_)) -> m_
    end

  let mut_lookup a =
    begin match lookup a with
    | None ->
        raise (Error ("No order assigned for " ^ I.conDecName (I.sgnLookup a)))
    | Some (TDec (_, m_)) -> m_
    end

  let mutual a =
    let rec mutual' = function
      | Empty, a's -> a's
      | Le (a, m_), a's -> mutual' (m_, a :: a's)
      | Lt (a, m_), a's -> mutual' (m_, a :: a's)
    in
    mutual' (mut_lookup a, [])

  let rec closure = function
    | [], a2s -> a2s
    | a :: a1s, a2s ->
        begin if List.exists (function a' -> a = a') a2s then closure (a1s, a2s)
        else closure (mutual a @ a1s, a :: a2s)
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
  let reset_r_order = reset_r_order
  let resetROrder = reset_r_order
  let install = install
  let uninstall = uninstall
  let install_r_order = install_r_order
  let installROrder = install_r_order
  let uninstall_r_order = uninstall_r_order
  let uninstallROrder = uninstall_r_order
  let sel_lookup = sel_lookup
  let selLookup = sel_lookup
  let sel_lookup_r_order = sel_lookup_r_order
  let selLookupROrder = sel_lookup_r_order
  let mut_lookup = mut_lookup
  let mutLookup = mut_lookup
  let closure a = closure ([ a ], [])
end

(*! structure IntSyn' : INTSYN !*)
(* local *)
(* functor Order *)

(* # 1 "src/lambda/Order.sml.ml" *)
open! Basis
open Table.TableInstances

module Key' = struct
  type key' = int

  let compare (a : key') (b : key') : Basis.order =
    if a < b then Less else if a > b then Greater else Equal
end

module Order = MakeOrder (struct
  module Table = RedBlackTree.RedBlackTree (Key')
end)

include Order

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)
