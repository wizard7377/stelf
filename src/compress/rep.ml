(* # 1 "src/compress/rep.sig.ml" *)

(* # 1 "src/compress/rep.fun.ml" *)

(* # 1 "src/compress/rep.sml.ml" *)
open! Syntax
open! Sgn
open! Reductio
open! Basis

module Rep = struct
  module I = IntSyn
  module S = Syntax

  let rec defSize x =
    begin match x with
    | Sgn.Def_term y -> S.size_term y
    | Sgn.Def_type y -> S.size_tp y
    end

  let rec cidSize cid =
    begin match I.sgnLookup cid with
    | I.ConDec (_, _, _, _, _, I.Type) ->
        S.size_tp (S.typeOf (Sgn.classifier cid))
    | I.ConDec (_, _, _, _, _, I.Kind) ->
        S.size_knd (S.kindOf (Sgn.classifier cid))
    | I.ConDef (_, _, _, _, _, _, _) -> defSize (Sgn.def cid)
    | I.AbbrevDef (_, _, _, _, _, _) -> defSize (Sgn.def cid)
    | _ -> 0
    end

  let rec o_cidSize cid =
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

  exception Crap

  let rec sanityCheck cid =
    try
      begin match I.sgnLookup cid with
      | I.ConDec (_, _, _, _, _, I.Type) ->
          Reductio.check_plusconst_type (typeOf (Sgn.classifier cid))
      | I.ConDec (_, _, _, _, _, I.Kind) ->
          Reductio.check_kind ([], kindOf (Sgn.classifier cid))
      | I.ConDef (_, _, _, _, _, I.Type, _) ->
          let (Sgn.Def_term y) = Sgn.def cid in
          let (Syntax.Tclass_ z) = Sgn.classifier cid in
          Reductio.check ([], y, z)
          (*				     l := (y,z):: !l; *)
      | I.ConDef (_, _, _, _, _, I.Kind, _) ->
          let (Sgn.Def_type y) = Sgn.def cid in
          let (Syntax.Kclass_ z) = Sgn.classifier cid in
          Reductio.check_type Reductio.Con_lf (Syntax.explodeKind z, y)
      | I.AbbrevDef (_, _, _, _, _, I.Type) ->
          let (Sgn.Def_term y) = Sgn.def cid in
          let (Syntax.Tclass_ z) = Sgn.classifier cid in
          Reductio.check ([], y, z)
          (*				     l := (y,z):: !l; *)
      | I.AbbrevDef (_, _, _, _, _, I.Kind) ->
          let (Sgn.Def_type y) = Sgn.def cid in
          let (Syntax.Kclass_ z) = Sgn.classifier cid in
          Reductio.check_type Reductio.Con_lf (Syntax.explodeKind z, y)
      | _ -> true
      end
      (* we're not checking block declarations or anything else like that *)
    with Syntax.Syntax _ ->
      begin
        print ("--> " ^ Int.toString cid);
        raise Match
      end

  let rec gen_graph n autoCompress =
    let _ = autoCompress n in
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
    let _ = sanity n in
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
    let _ = TextIO.output (f, s) in
    let _ = TextIO.closeOut f in
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
