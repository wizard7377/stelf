(* # 1 "src/compress/sgn.sig.ml" *)

(* # 1 "src/compress/sgn.fun.ml" *)

(* # 1 "src/compress/sgn.sml.ml" *)
open! Syntax
open! Basis
include Sgn_intf
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

  let rec clear () =
    begin
      Array.modify (function _ -> None) sigma;
      begin
        Array.modify (function _ -> None) all_modes;
        Array.modify (function _ -> None) all_ps
      end
    end

  let rec condec (s, a, oa) =
    {
      name = s;
      classifier = Tclass_ a;
      o_classifier = Tclass_ oa;
      def = Def_none;
      o_def = Def_none;
      abbreviation = false;
    }

  let rec tycondec (s, k, ok) =
    {
      name = s;
      classifier = Kclass_ k;
      o_classifier = Kclass_ ok;
      def = Def_none;
      o_def = Def_none;
      abbreviation = false;
    }

  let rec defn (s, a, oa, m, om) =
    {
      name = s;
      classifier = Tclass_ a;
      o_classifier = Tclass_ oa;
      def = Def_term m;
      o_def = Def_term om;
      abbreviation = false;
    }

  let rec tydefn (s, k, ok, a, oa) =
    {
      name = s;
      classifier = Kclass_ k;
      o_classifier = Kclass_ ok;
      def = Def_type a;
      o_def = Def_type oa;
      abbreviation = false;
    }

  let rec abbrev (s, a, oa, m, om) =
    {
      name = s;
      classifier = Tclass_ a;
      o_classifier = Tclass_ oa;
      def = Def_term m;
      o_def = Def_term om;
      abbreviation = true;
    }

  let rec tyabbrev (s, k, ok, a, oa) =
    {
      name = s;
      classifier = Kclass_ k;
      o_classifier = Kclass_ ok;
      def = Def_type a;
      o_def = Def_type oa;
      abbreviation = true;
    }

  let rec typeOfSigent (e : sigent) = Syntax.typeOf ((fun r -> r.classifier) e)
  let rec setter table (n, x) = Array.update (table, n, Some x)
  let rec getter table id = Array.sub (table, id)
  let set_modes = setter all_modes
  let get_modes = getter all_modes
  let set_p = setter all_ps
  let get_p = getter all_ps
  let update = setter sigma
  let sub = getter sigma

  let rec classifier id =
    try (fun r -> r.classifier) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let rec o_classifier id =
    try (fun r -> r.o_classifier) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let rec def id =
    try (fun r -> r.def) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let rec o_def id =
    try (fun r -> r.o_def) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)

  let rec abbreviation id =
    try (fun r -> r.abbreviation) (Option.valOf (sub id))
    with Option.Option -> raise (NoSuch id)
end

include Sgn
