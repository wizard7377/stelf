(* # 1 "src/tabling/tabledsyn.sig.ml" *)
open! Basis

(* Tabled Syntax *)
(* Author: Brigitte Pientka *)
include Tabledsyn_intf
(* signature TABLEDSYN *)

(* # 1 "src/tabling/tabledsyn.fun.ml" *)
open! Basis

(* Tabled Syntax *)
(* Author: Brigitte Pientka *)
module MakeTabledSyn (TabledSyn__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module Index : INDEX
end) : TABLEDSYN = struct
  (*! structure IntSyn = IntSyn' !*)
  module Table = TabledSyn__0.Table
  module Names = TabledSyn__0.Names
  module Index = TabledSyn__0.Index

  exception Error of string

  type tabled = Yes_ | No_ [@@deriving eq, ord, show]

  (*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
  open! struct
    module I = IntSyn

    let tabledSignature : bool Table.table = Table.new_ 0
    let rec reset () = Table.clear tabledSignature
    let rec installTabled a = Table.insert tabledSignature (a, false)

    let rec installKeepTable a =
      begin
        ignore (Table.insertShadow tabledSignature (a, true));
        ()
      end

    let rec tabledLookup a =
      begin match Table.lookup tabledSignature a with
      | None -> false
      | Some _ -> true
      end

    let rec keepTable a =
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

(* # 1 "src/tabling/tabledsyn.sml.ml" *)
