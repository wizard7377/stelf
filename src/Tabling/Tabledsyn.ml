open! Table.Table_
open! Intsyn.Lambda_
open! Names.Names_
open! Index.Index_

(* # 1 "src/tabling/Tabledsyn.sig.ml" *)

(* Tabled Syntax *)
(* Author: Brigitte Pientka *)
include TABLEDSYN
(* signature TABLEDSYN *)

(* # 1 "src/tabling/Tabledsyn.fun.ml" *)
open! Basis

(* Tabled Syntax *)
(* Author: Brigitte Pientka *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeTabledSyn
    (Names : NAMES)
    (Table : TABLE with type key = int)
    (Index : INDEX) : TABLEDSYN = struct
  (*
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module Index : INDEX
*)
  (*! structure IntSyn = IntSyn' !*)
  module Table = Table
  module Names = Names
  module Index = Index

  exception Error = Error

  type tabled = Yes | No_ [@@deriving eq, ord, show]

  (*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
  open! struct
    module I = IntSyn

    let tabledSignature : bool Table.table = Table.new_ 0
    let reset () = Table.clear tabledSignature
    let installTabled a = Table.insert tabledSignature (a, false)

    let installKeepTable a =
      begin
        ignore (Table.insertShadow tabledSignature (a, true));
        ()
      end

    let tabledLookup a =
      begin match Table.lookup tabledSignature a with
      | None -> false
      | Some _ -> true
      end

    let keepTable a =
      begin match Table.lookup tabledSignature a with
      | None -> false
      | Some true -> true
      | Some false -> false
      end
  end

  (* reset () = ()

       Effect: Resets tabled array
    *)
  (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
  (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
  (* Table.delete tabledSignature a; *)
  (* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)
  (* keepTable a = bool

       if we should keep the table for this predicate a
        then returns true
          otherwise false
    *)
  let reset = reset
  let installTabled (x : IntSyn.cid) = installTabled x
  let installKeepTable = installKeepTable
  let tabledLookup = tabledLookup
  let keepTable = keepTable
end
(*! sharing Index.IntSyn = IntSyn' !*)
(* functor TabledSyn *)

(* # 1 "src/tabling/Tabledsyn.sml.ml" *)
