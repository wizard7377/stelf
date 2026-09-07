
(* # 1 "src/compress/Sgn.sig.ml" *)

(* # 1 "src/compress/Sgn.fun.ml" *)

(* # 1 "src/compress/Sgn.sml.ml" *)
open! Syntax
open! Basis
include SGN

module Sgn = struct
  open Syntax

  exception NoSuch of int

  type def = Def_none | Def_term of term | Def_type of tp

  (* o_ means ""original"", i.e. before compression *)
  type nonrec __0 = {
    name : string;
    classifier : class_;
    o_classifier : class_;
    def : def;
    o_def : def;
    abbreviation : bool;
  }

  type nonrec sigent = __0

  let sgn_size = 14000

  (* XXX *)
  let sigma : sigent option Array.array = Array.array (sgn_size, None)
  let all_modes : mode list option Array.array = Array.array (sgn_size, None)
  let all_ps : bool option Array.array = Array.array (sgn_size, None)

  let rec split arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | h :: tl, 0 -> ([], h, tl)
    | h :: tl, n ->
        let pre, thing, post = split tl (n - 1) in
        (h :: pre, thing, post)
    | [], n -> split [ None ] n
    end

  let clear () =
    begin
      Array.modify (function _ -> None) sigma;
      begin
        Array.modify (function _ -> None) all_modes;
        Array.modify (function _ -> None) all_ps
      end
    end

  let condec (s, a, oa) =
    {
      name = s;
      classifier = Tclass a;
      o_classifier = Tclass oa;
      def = Def_none;
      o_def = Def_none;
      abbreviation = false;
    }

  let tycondec s k ok =
    {
      name = s;
      classifier = Kclass k;
      o_classifier = Kclass ok;
      def = Def_none;
      o_def = Def_none;
      abbreviation = false;
    }

  let defn s a oa m om =
    {
      name = s;
      classifier = Tclass a;
      o_classifier = Tclass oa;
      def = Def_term m;
      o_def = Def_term om;
      abbreviation = false;
    }

  let tydefn s k ok a oa =
    {
      name = s;
      classifier = Kclass k;
      o_classifier = Kclass ok;
      def = Def_type a;
      o_def = Def_type oa;
      abbreviation = false;
    }

  let abbrev s a oa m om =
    {
      name = s;
      classifier = Tclass a;
      o_classifier = Tclass oa;
      def = Def_term m;
      o_def = Def_term om;
      abbreviation = true;
    }

  let tyabbrev s k ok a oa =
    {
      name = s;
      classifier = Kclass k;
      o_classifier = Kclass ok;
      def = Def_type a;
      o_def = Def_type oa;
      abbreviation = true;
    }

  let typeOfSigent (e : sigent) = Syntax.typeOf ((fun r -> r.classifier) e)
  let setter table n x = Array.update (table, n, Some x)
  let getter table id = Array.sub (table, id)
  let set_modes = setter all_modes
  let get_modes = getter all_modes
  let set_p = setter all_ps
  let get_p = getter all_ps

  (* `update` is still tupled in SGN: the name carries two different arities
     across signatures, so it is out of scope for the mechanical pass. *)
  let update (n, x) = setter sigma n x
  let sub = getter sigma

  let classifier id =
    try (fun r -> r.classifier) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let o_classifier id =
    try (fun r -> r.o_classifier) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let def id =
    try (fun r -> r.def) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let o_def id =
    try (fun r -> r.o_def) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let abbreviation id =
    try (fun r -> r.abbreviation) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)
end

include Sgn

let () =
  Printexc.register_printer (function NoSuch _ -> Some "NoSuch" | _ -> None)
