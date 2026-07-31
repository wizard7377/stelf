open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_

(* # 1 "src/compress/Rep.sig.ml" *)

(* # 1 "src/compress/Rep.fun.ml" *)

(* # 1 "src/compress/Rep.sml.ml" *)
open! Syntax
open! Sgn
open! Reductio
open! Basis

exception Crap

let () = Printexc.register_printer (function Crap -> Some "Crap" | _ -> None)

module Rep = struct
  module I = IntSyn
  module S = Syntax

  let defSize x =
    begin match x with
    | Sgn.Def_term y -> S.size_term y
    | Sgn.Def_type y -> S.size_tp y
    end

  let cidSize cid =
    begin match I.sgnLookup cid with
    | I.ConDec (_, _, _, _, _, I.Type) ->
        S.size_tp (S.typeOf (Sgn.classifier cid))
    | I.ConDec (_, _, _, _, _, I.Kind) ->
        S.size_knd (S.kindOf (Sgn.classifier cid))
    | I.ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.def cid)
    | I.AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.def cid)
    | _ -> 0
    end

  let o_cidSize cid =
    begin match I.sgnLookup cid with
    | I.ConDec (_, _, _, _, _, I.Type) ->
        S.size_tp (S.typeOf (Sgn.o_classifier cid))
    | I.ConDec (_, _, _, _, _, I.Kind) ->
        S.size_knd (S.kindOf (Sgn.o_classifier cid))
    | I.ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.o_def cid)
    | I.AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.o_def cid)
    | _ -> 0
    end

  (* open SMLofNJ.Cont;; (* not available in OCaml *) *)
  (* val l : (Syntax.term * Syntax.tp) list ref = ref [] *)
  let k : Reductio.eq_c option ref = ref None

  exception Crap = Crap

  let sanityCheck cid =
    try
      begin match I.sgnLookup cid with
      | I.ConDec (_, _, _, _, _, I.Type) ->
          Reductio.check_plusconst_type (typeOf (Sgn.classifier cid))
      | I.ConDec (_, _, _, _, _, I.Kind) ->
          Reductio.check_kind ([], kindOf (Sgn.classifier cid))
      | I.ConDef (_, _, _, _, _, I.Type, _) ->
          let (Sgn.Def_term y) = Sgn.def cid in
          let (Syntax.Tclass z) = Sgn.classifier cid in
          Reductio.check ([], y, z)
          (*				     l := (y,z):: !l; *)
      | I.ConDef (_, _, _, _, _, I.Kind, _) ->
          let (Sgn.Def_type y) = Sgn.def cid in
          let (Syntax.Kclass z) = Sgn.classifier cid in
          Reductio.check_type Reductio.Con_lf (Syntax.explodeKind z, y)
      | I.AbbrevDef (_, _, _, _, _, I.Type) ->
          let (Sgn.Def_term y) = Sgn.def cid in
          let (Syntax.Tclass z) = Sgn.classifier cid in
          Reductio.check ([], y, z)
          (*				     l := (y,z):: !l; *)
      | I.AbbrevDef (_, _, _, _, _, I.Kind) ->
          let (Sgn.Def_type y) = Sgn.def cid in
          let (Syntax.Kclass z) = Sgn.classifier cid in
          Reductio.check_type Reductio.Con_lf (Syntax.explodeKind z, y)
      | _ -> true
      end
      (* we're not checking block declarations or anything else like that *)
    with Syntax.Syntax _ ->
      begin
        print ("--> " ^ Int.toString cid);
        raise Match
      end

  let gen_graph n autoCompress =
    ignore (autoCompress n);
    let rec sanity n =
      begin if n < 0 then true
      else
        sanity (n - 1)
        && begin if sanityCheck n then true
        else begin
          print (("insane: <" ^ Int.toString n) ^ ">\n");
          raise Crap
        end
        end
      end
    in
    ignore (sanity n);
    let pairs =
      List.tabulate (n + 1, function x -> (o_cidSize x, cidSize x))
    in
    let s =
      foldl
        (fun (x__op, y__op) -> x__op ^ y__op)
        ""
        (map
           (function x, y -> ((Int.toString x ^ " ") ^ Int.toString y) ^ "\n")
           pairs)
    in
    let f = TextIO.openOut "/tmp/graph" in
    ignore (TextIO.output (f, s));
    ignore (TextIO.closeOut f);
    ()

  (* DEBUG  handle Reductio.Matching2 s => (print ""doesn'tmatch""; k := SOME s); *)
  (* fun gg n = (Compress.sgnReset(); gen_graph n
	    (fn n => Compress.sgnAutoCompressUpTo n Compress.naiveModes)) *)
  (* Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) *)
  open Reductio
end
(*
fun autoCompress n modeFinder =
    let
	val rep = Stelf.Names.lookup ""represents""
	val rep_z = Stelf.Names.lookup ""represents_z""
	val rep_s = Stelf.Names.lookup ""represents_s"" 
    in
	Compress.sgnReset();
	Compress.sgnAutoCompressUpTo(n)
     Syntax.size_term (Option.valOf(#o_def (Compress.sgnLookup n))) 
    end
*)
