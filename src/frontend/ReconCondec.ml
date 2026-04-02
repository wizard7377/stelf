(* # 1 "src/frontend/ReconCondec.sig.ml" *)
open! Basis

(* External Syntax for signature entries *)
(* Author: Frank Pfenning *)
include ReconCondec_intf
(* id : tm = tm | _ : tm = tm *)
(* signature EXTCONDEC *)
(* signature RECON_CONDEC *)

(* # 1 "src/frontend/ReconCondec.fun.ml" *)
open! Basis

module ReconConDec (ReconConDec__0 : sig
  (* Reconstruct signature entries *)
  (* Author: Frank Pfenning *)
  (* Modified: Roberto Virga, Jeff Polakow *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! structure Paths' : PATHS !*)
  module ReconTerm' : ReconTerm_intf.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
  (*! sharing ReconTerm'.Paths = Paths' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Strict : STRICT

  (*! sharing Strict.IntSyn = IntSyn' !*)
  (*! sharing Strict.Paths = Paths' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Timers : Timers.TIMERS
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Msg : MSG
end) : RECON_CONDEC = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  module Timers = ReconConDec__0.Timers
  module ExtSyn = ReconConDec__0.ReconTerm'

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type nonrec name = string

  (* Constant declarations *)
  type condec =
    | Condec_ of name * ExtSyn.term
    | Condef_ of name option * ExtSyn.term * ExtSyn.term option
    | Blockdef_ of string * (string list * string) list
    | Blockdec_ of name * ExtSyn.dec list * ExtSyn.dec list

  let rec condec (name, tm) = Condec_ (name, tm)
  let rec blockdec (name, ds1, ds2) = Blockdec_ (name, ds1, ds2)
  let rec blockdef (name, worlds) = Blockdef_ (name, worlds)
  let rec condef (nameOpt, tm1, tm2Opt) = Condef_ (nameOpt, tm1, tm2Opt)

  (* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
  (* should printing of result be moved to frontend? *)
  (* Wed May 20 08:08:50 1998 -fp *)
  let rec condecToConDec = function
    | Condec_ (name, tm), Paths.Loc (fileName, r), abbFlag ->
        let _ = Names.varReset IntSyn.Null in
        let _ = ExtSyn.resetErrors fileName in
        let (ExtSyn.JClass ((v_, oc), l_)) =
          Timers.time Timers.recon ExtSyn.recon (ExtSyn.jclass tm)
        in
        let _ = ExtSyn.checkErrors r in
        let i, v'_ =
          try Timers.time Timers.abstract Abstract.abstractDecImp v_
          with Abstract.Error msg ->
            raise (Abstract.Error (Paths.wrap (r, msg)))
        in
        let cd =
          Names.nameConDec
            (IntSyn.ConDec (name, None, i, IntSyn.Normal, v'_, l_))
        in
        let ocd = Paths.dec (i, oc) in
        let _ =
          begin if !Global.chatter >= 3 then
            Msg.message
              (Timers.time Timers.printing Print.conDecToString cd ^ "\n")
          else ()
          end
        in
        let _ =
          begin if !Global.doubleCheck then begin
            try Timers.time Timers.checking TypeCheck.check (v'_, IntSyn.Uni l_)
            with TypeCheck.Error msg ->
              Printf.eprintf "DOUBLE-CHECK FAIL on ConDec %s: %s\n%!" name msg;
              raise (TypeCheck.Error msg)
          end
          else ()
          end
        in
        (Some cd, Some ocd)
    | Condef_ (optName, tm1, tm2Opt), Paths.Loc (fileName, r), abbFlag ->
        let _ = Names.varReset IntSyn.Null in
        let _ = ExtSyn.resetErrors fileName in
        let f =
          begin match tm2Opt with
          | None -> ExtSyn.jterm tm1
          | Some tm2 -> ExtSyn.jof (tm1, tm2)
          end
        in
        let f' = Timers.time Timers.recon ExtSyn.recon f in
        let (u_, oc1), (v_, oc2Opt), l_ =
          begin match f' with
          | ExtSyn.JTerm ((u_, oc1), v_, l_) -> ((u_, oc1), (v_, None), l_)
          | ExtSyn.JOf ((u_, oc1), (v_, oc2), l_) ->
              ((u_, oc1), (v_, Some oc2), l_)
          end
        in
        let _ = ExtSyn.checkErrors r in
        let i, (u''_, v''_) =
          try Timers.time Timers.abstract Abstract.abstractDef (u_, v_)
          with Abstract.Error msg ->
            raise (Abstract.Error (Paths.wrap (r, msg)))
        in
        let name =
          begin match optName with None -> "_" | Some name -> name
          end
        in
        let ocd = Paths.def (i, oc1, oc2Opt) in
        let cd =
          begin if abbFlag then
            Names.nameConDec (IntSyn.AbbrevDef (name, None, i, u''_, v''_, l_))
          else begin
            Strict.check ((u''_, v''_), Some ocd);
            Names.nameConDec
              (IntSyn.ConDef
                 (name, None, i, u''_, v''_, l_, IntSyn.ancestor u''_))
          end
            (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
            (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)
          end
        in
        let _ =
          begin if !Global.chatter >= 3 then
            Msg.message
              (Timers.time Timers.printing Print.conDecToString cd ^ "\n")
          else ()
          end
        in
        let _ =
          begin if !Global.doubleCheck then begin
            (try
               Timers.time Timers.checking TypeCheck.check (v''_, IntSyn.Uni l_)
             with TypeCheck.Error msg ->
               let n = match optName with None -> "_" | Some n -> n in
               Printf.eprintf "DOUBLE-CHECK FAIL on ConDef %s (type): %s\n%!" n
                 msg;
               raise (TypeCheck.Error msg));
            try Timers.time Timers.checking TypeCheck.check (u''_, v''_)
            with TypeCheck.Error msg ->
              let n = match optName with None -> "_" | Some n -> n in
              Printf.eprintf "DOUBLE-CHECK FAIL on ConDef %s (term): %s\n%!" n
                msg;
              raise (TypeCheck.Error msg)
          end
          else ()
          end
        in
        let optConDec =
          begin match optName with None -> None | Some _ -> Some cd
          end
        in
        (optConDec, Some ocd)
    | Blockdec_ (name, lsome_, lblock_), Paths.Loc (fileName, r), abbFlag ->
        let rec makectx = function
          | [] -> IntSyn.Null
          | d_ :: l_ -> IntSyn.Decl (makectx l_, d_)
        in
        let rec ctxToList = function
          | IntSyn.Null, acc -> acc
          | IntSyn.Decl (g_, d_), acc -> ctxToList (g_, d_ :: acc)
        in
        let rec ctxAppend = function
          | g_, IntSyn.Null -> g_
          | g_, IntSyn.Decl (g'_, d_) -> IntSyn.Decl (ctxAppend (g_, g'_), d_)
        in
        let rec ctxBlockToString (g0_, (g1_, g2_)) =
          let _ = Names.varReset IntSyn.Null in
          let g0'_ = Names.ctxName g0_ in
          let g1'_ = Names.ctxLUName g1_ in
          let g2'_ = Names.ctxLUName g2_ in
          (((Print.ctxToString (IntSyn.Null, g0'_) ^ "\n")
           ^ begin match g1'_ with
           | IntSyn.Null -> ""
           | _ -> ("some " ^ Print.ctxToString (g0'_, g1'_)) ^ "\n"
           end)
          ^ "pi ")
          ^ Print.ctxToString (ctxAppend (g0'_, g1'_), g2'_)
        in
        let rec checkFreevars = function
          | IntSyn.Null, (g1_, g2_), r -> ()
          | g0_, (g1_, g2_), r ->
              let _ = Names.varReset IntSyn.Null in
              let g0'_ = Names.ctxName g0_ in
              let g1'_ = Names.ctxLUName g1_ in
              let g2'_ = Names.ctxLUName g2_ in
              error
                ( r,
                  "Free variables in context block after term reconstruction:\n"
                  ^ ctxBlockToString (g0'_, (g1'_, g2'_)) )
        in
        let gsome, gblock = (makectx lsome_, makectx lblock_) in
        let r' =
          begin match (ExtSyn.ctxRegion gsome, ExtSyn.ctxRegion gblock) with
          | Some r1, Some r2 -> Paths.join (r1, r2)
          | _, Some r2 -> r2
          end
        in
        let _ = Names.varReset IntSyn.Null in
        let _ = ExtSyn.resetErrors fileName in
        let j =
          ExtSyn.jwithctx (gsome, ExtSyn.jwithctx (gblock, ExtSyn.jnothing))
        in
        let (ExtSyn.JWithCtx (gsome_, ExtSyn.JWithCtx (gblock_, _))) =
          Timers.time Timers.recon ExtSyn.recon j
        in
        let _ = ExtSyn.checkErrors r in
        let g0_, [ gsome'_; gblock'_ ] =
          try Abstract.abstractCtxs [ gsome_; gblock_ ]
          with Constraints.Error c_ ->
            raise
              (error
                 ( r',
                   (("Constraints remain in context block after term \
                      reconstruction:\n"
                    ^ ctxBlockToString (IntSyn.Null, (gsome_, gblock_)))
                   ^ "\n")
                   ^ Print.cnstrsToString c_ ))
        in
        let _ = checkFreevars (g0_, (gsome'_, gblock'_), r') in
        let bd =
          IntSyn.BlockDec (name, None, gsome'_, ctxToList (gblock'_, []))
        in
        let _ =
          begin if !Global.chatter >= 3 then
            Msg.message
              (Timers.time Timers.printing Print.conDecToString bd ^ "\n")
          else ()
          end
        in
        (Some bd, None)
        (* closed nf *)
    | Blockdef_ (name, w_), Paths.Loc (fileName, r), abbFlag ->
        let w'_ = List.map (fun (ids, id) -> Names.Qid (ids, id)) w_ in
        let w''_ =
          List.map
            (function
              | qid -> begin
                  match Names.constLookup qid with
                  | None ->
                      raise
                        (Names.Error
                           (("Undeclared label "
                            ^ Names.qidToString (valOf (Names.constUndef qid)))
                           ^ "."))
                  | Some cid -> cid
                end)
            w'_
        in
        let bd = IntSyn.BlockDef (name, None, w''_) in
        let _ =
          begin if !Global.chatter >= 3 then
            Msg.message
              (Timers.time Timers.printing Print.conDecToString bd ^ "\n")
          else ()
          end
        in
        (Some bd, None)

  let rec internalInst _ = raise Match
  let rec externalInst _ = raise Match
end
(* functor ReconConDec *)

(* # 1 "src/frontend/ReconCondec.sml.ml" *)
