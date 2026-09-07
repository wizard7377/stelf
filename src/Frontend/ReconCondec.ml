open! Timing
open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths.Paths_
open! Print.Print_
open! Typecheck.Typecheck_
open! Msg.Msg_

(* # 1 "src/frontend/ReconCondec.sig.ml" *)

(* External Syntax for signature entries *)
(* Author: Frank Pfenning *)
include RECONCONDEC

(* id : tm = tm | _ : tm = tm *)
(* signature EXTCONDEC *)
(* signature RECON_CONDEC *)

(* # 1 "src/frontend/ReconCondec.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  module ReconTerm' : RECONTERM.RECON_TERM

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

  exception Error = Error

  (* error (r, msg) raises a syntax error within region r with text msg *)
  let error r msg = raise (Error (Paths.wrap r msg))

  type nonrec name = string

  (* Constant declarations *)
  type condec =
    | Condec_ of name * ExtSyn.term
    | Condef_ of name option * ExtSyn.term * ExtSyn.term option
    | Blockdef of string * (string list * string) list
    | Blockdec of name * ExtSyn.dec list * ExtSyn.dec list

  let condec (name, tm) = Condec_ (name, tm)
  let blockdec name ds1 ds2 = Blockdec (name, ds1, ds2)
  let blockdef name worlds = Blockdef (name, worlds)
  let condef nameOpt tm1 tm2Opt = Condef_ (nameOpt, tm1, tm2Opt)

  (* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
  (* should printing of result be moved to frontend? *)
  (* Wed May 20 08:08:50 1998 -fp *)
  let condecToConDec a1 b1 c1 = match a1, b1, c1 with
    | Condec_ (name, tm), Paths.Loc (fileName, r), abbFlag ->
        ignore (Names.varReset IntSyn.Null);
        ignore (ExtSyn.resetErrors fileName);
        let (ExtSyn.JClass ((v, oc), l)) =
          Timers.time Timers.recon ExtSyn.recon (ExtSyn.jclass tm)
        in
        ignore (ExtSyn.checkErrors r);
        let i, v' =
          try Timers.time Timers.abstract Abstract.abstractDecImp v
          with Abstract.Error msg ->
            raise (Abstract.Error (Paths.wrap r msg))
        in
        let cd =
          Names.nameConDec
            (IntSyn.ConDec (name, None, i, IntSyn.Normal, v', l))
        in
        let ocd = Paths.dec (i, oc) in
        ignore (Display.chatter_s 3 ~kind:Display.Response
            (Timers.time Timers.printing Print.conDecToString cd ^ "\n"));
        ignore begin if !Global.doubleCheck then
            begin try
              Timers.time Timers.checking TypeCheck.check (v', IntSyn.Uni l)
            with TypeCheck.Error msg ->
              Printf.eprintf "DOUBLE-CHECK FAIL on ConDec %s: %s\n%!" name msg;
              raise (TypeCheck.Error msg)
            end
          else ()
          end;
        (Some cd, Some ocd)
    | Condef_ (optName, tm1, tm2Opt), Paths.Loc (fileName, r), abbFlag ->
        ignore (Names.varReset IntSyn.Null);
        ignore (ExtSyn.resetErrors fileName);
        let f =
          begin match tm2Opt with
          | None -> ExtSyn.jterm tm1
          | Some tm2 -> ExtSyn.jof tm1 tm2
          end
        in
        let f' = Timers.time Timers.recon ExtSyn.recon f in
        let (u, oc1), (v, oc2Opt), l =
          begin match f' with
          | ExtSyn.JTerm ((u, oc1), v, l) -> ((u, oc1), (v, None), l)
          | ExtSyn.JOf ((u, oc1), (v, oc2), l) ->
              ((u, oc1), (v, Some oc2), l)
          end
        in
        ignore (ExtSyn.checkErrors r);
        let i, (u'', v'') =
          try Timers.time Timers.abstract (fun () -> Abstract.abstractDef u v) ()
          with Abstract.Error msg ->
            raise (Abstract.Error (Paths.wrap r msg))
        in
        let name =
          begin match optName with None -> "_" | Some name -> name
          end
        in
        let ocd = Paths.def i oc1 oc2Opt in
        let cd =
          begin if abbFlag then
            Names.nameConDec (IntSyn.AbbrevDef (name, None, i, u'', v'', l))
          else begin
            Strict.check ((u'', v''), Some ocd);
            Names.nameConDec
              (IntSyn.ConDef (name, None, i, u'', v'', l, IntSyn.ancestor u''))
          end
            (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
            (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)
          end
        in
        ignore (Display.chatter_s 3 ~kind:Display.Response
            (Timers.time Timers.printing Print.conDecToString cd ^ "\n"));
        ignore begin if !Global.doubleCheck then begin
            (try Timers.time Timers.checking TypeCheck.check (v'', IntSyn.Uni l)
             with TypeCheck.Error msg ->
               let n = match optName with None -> "_" | Some n -> n in
               Printf.eprintf "DOUBLE-CHECK FAIL on ConDef %s (type): %s\n%!" n
                 msg;
               raise (TypeCheck.Error msg));
            try Timers.time Timers.checking TypeCheck.check (u'', v'')
            with TypeCheck.Error msg ->
              let n = match optName with None -> "_" | Some n -> n in
              Printf.eprintf "DOUBLE-CHECK FAIL on ConDef %s (term): %s\n%!" n
                msg;
              raise (TypeCheck.Error msg)
          end
          else ()
          end;
        let optConDec =
          begin match optName with None -> None | Some _ -> Some cd
          end
        in
        (optConDec, Some ocd)
    | Blockdec (name, lsome, lblock), Paths.Loc (fileName, r), abbFlag ->
        let rec makectx = function
          | [] -> IntSyn.Null
          | d :: l -> IntSyn.Decl (makectx l, d)
        in
        let rec ctxToList (a, acc) = match a with
          | IntSyn.Null -> acc
          | IntSyn.Decl (g, d) -> ctxToList (g, d :: acc)
        in
        let rec ctxAppend (g, a) = match a with
          | IntSyn.Null -> g
          | IntSyn.Decl (g', d) -> IntSyn.Decl (ctxAppend (g, g'), d)
        in
        let ctxBlockToString (g0, (g1, g2)) =
          ignore (Names.varReset IntSyn.Null);
          let g0' = Names.ctxName g0 in
          let g1' = Names.ctxLUName g1 in
          let g2' = Names.ctxLUName g2 in
          (((Print.ctxToString IntSyn.Null g0' ^ "\n")
           ^ begin match g1' with
           | IntSyn.Null -> ""
           | _ -> ("some " ^ Print.ctxToString g0' g1') ^ "\n"
           end)
          ^ "pi ")
          ^ Print.ctxToString (ctxAppend (g0', g1')) g2'
        in
        let checkFreevars (g0, a, r) = match g0, a with
          | IntSyn.Null, (g1, g2) -> ()
          | g0, (g1, g2) ->
              ignore (Names.varReset IntSyn.Null);
              let g0' = Names.ctxName g0 in
              let g1' = Names.ctxLUName g1 in
              let g2' = Names.ctxLUName g2 in
              error
                r ("Free variables in context block after term reconstruction:\n"
                  ^ ctxBlockToString (g0', (g1', g2')))
        in
        let gsome, gblock = (makectx lsome, makectx lblock) in
        let r' =
          begin match (ExtSyn.ctxRegion gsome, ExtSyn.ctxRegion gblock) with
          | Some r1, Some r2 -> Paths.join r1 r2
          | _, Some r2 -> r2
          end
        in
        ignore (Names.varReset IntSyn.Null);
        ignore (ExtSyn.resetErrors fileName);
        let j =
          ExtSyn.jwithctx gsome (ExtSyn.jwithctx gblock ExtSyn.jnothing)
        in
        let (ExtSyn.JWithCtx (gsome, ExtSyn.JWithCtx (gblock, _))) =
          Timers.time Timers.recon ExtSyn.recon j
        in
        ignore (ExtSyn.checkErrors r);
        let g0, [ gsome'; gblock' ] =
          try Abstract.abstractCtxs [ gsome; gblock ]
          with Constraints.Error c ->
            raise
              (error
                 r' ((("Constraints remain in context block after term \
                      reconstruction:\n"
                    ^ ctxBlockToString (IntSyn.Null, (gsome, gblock)))
                   ^ "\n")
                   ^ Print.cnstrsToString c))
        in
        ignore (checkFreevars (g0, (gsome', gblock'), r'));
        let bd =
          IntSyn.BlockDec (name, None, gsome', ctxToList (gblock', []))
        in
        ignore (Display.chatter_s 3 ~kind:Display.Response
            (Timers.time Timers.printing Print.conDecToString bd ^ "\n"));
        (Some bd, None)
        (* closed nf *)
    | Blockdef (name, w), Paths.Loc (fileName, r), abbFlag ->
        let w' = List.map (fun (ids, id) -> Names.Qid (ids, id)) w in
        let w'' =
          List.map
            (function
              | qid ->
                  begin match Names.constLookup qid with
                  | None ->
                      raise
                        (Names.Error
                           (("Undeclared label "
                            ^ Names.qidToString (valOf (Names.constUndef qid)))
                           ^ "."))
                  | Some cid -> cid
                  end)
            w'
        in
        let bd = IntSyn.BlockDef (name, None, w'') in
        ignore (Display.chatter_s 3 ~kind:Display.Response
            (Timers.time Timers.printing Print.conDecToString bd ^ "\n"));
        (Some bd, None)

  let internalInst _ = raise Match
  let externalInst _ = raise Match
end
(* functor ReconConDec *)

(* # 1 "src/frontend/ReconCondec.sml.ml" *)
