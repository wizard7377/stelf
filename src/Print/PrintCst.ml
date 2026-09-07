open! Basis
open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Formatter__Formatter_

(** [PRINT], implemented as resugaring followed by pretty-printing.

    This is a shim, not a printer. All of the work happens in two libraries that
    know nothing about each other and nothing about this interface: [Resugar]
    turns internal syntax into a CST, [Pretty] turns a CST into modern STELF
    surface syntax. What is left here is the adapter -- snapshotting [PRINT]'s
    global refs into a [Resugar.Options.t], translating [Names.Fixity] into
    [Pretty.Fixity], and wrapping the result back up as a ForML [format] for the
    callers that compose one.

    Keeping the [PRINT] signature means none of the roughly sixty call sites
    change, and switching back is a one-line edit at the bottom of [Print_.ml].
*)

(* This library is built with [-open Basis], which puts the SML basis's
   [String] and [List] in scope. Everything below is new code written against
   [Format] and the OCaml standard library, so take those back. *)
module String = Stdlib.String
module List = Stdlib.List
module C = Cst.Make_Cst (Paths.Paths_)
module R = Resugar.Make_Resugar (C)
module P = Pretty.Make_Pretty (C)
module Tm = Resugar.Term.Make (C)
module V = C.View
module FX = Names.Fixity

module Print : PRINT.PRINT with module Formatter = Formatter = struct
  module Formatter = Formatter
  module F = Formatter

  let implicit = ref false
  let printInfix = ref false
  let printDepth = ref (None : int option)
  let printLength = ref (None : int option)
  let noShadow = ref false
  let showConstPath = ref true

  (* The refs stay where they were and keep working; each call takes a
     snapshot. That is what lets [Resugar] take its settings as an explicit
     record without any caller having to save and restore six globals. *)
  let opts () : Resugar.Options.t =
    {
      implicit = !implicit;
      print_infix = !printInfix;
      print_depth = !printDepth;
      print_length = !printLength;
      no_shadow = !noShadow;
      show_const_path = !showConstPath;
      arrow_sugar = !Global.printArrowSugar;
      eta_expand = true;
    }

  (* [Pretty] defines its own fixity type so that it does not depend on the
     signature; the translation lives here, on the side that already does. *)
  let to_pretty_fixity : FX.fixity -> Pretty.Fixity.t = function
    | FX.Nonfix -> Pretty.Fixity.Nonfix
    | FX.Infix (FX.Strength p, FX.Left) ->
        Pretty.Fixity.Infix (p, Pretty.Fixity.Left)
    | FX.Infix (FX.Strength p, FX.Right) ->
        Pretty.Fixity.Infix (p, Pretty.Fixity.Right)
    | FX.Infix (FX.Strength p, FX.None) ->
        Pretty.Fixity.Infix (p, Pretty.Fixity.Non)
    | FX.Prefix (FX.Strength p) -> Pretty.Fixity.Prefix p
    | FX.Postfix (FX.Strength p) -> Pretty.Fixity.Postfix p

  let env () : Pretty.env =
    {
      fixity =
        (fun (ns, name) ->
          to_pretty_fixity (Names.fixityLookup (Names.Qid (ns, name))));
      margin = !F.pagewidth;
    }

  (* Bridge into ForML, for the callers that compose a [format] rather than a
     string.

     [Formatter.string0 n s] is [Str (n, s)], and ForML's layout pass emits [s]
     verbatim while treating [n] as its width -- ForML itself uses a
     zero-width [Str] for newlines, so a multi-line [Str] is not an abuse.
     Per-line widths therefore stay exact. What is lost is re-flow: [Pretty]
     commits to a layout against [!pagewidth] before ForML sees it, so a block
     at deep ForML indentation can overrun. Every caller that composes formats
     is a diagnostic where exact wrapping is cosmetic; the string entry points
     below skip ForML entirely, which is where the layout actually matters. *)
  let to_format (render : Format.formatter -> unit) : F.format =
    let s = Format.asprintf "%t" render in
    match String.split_on_char '\n' s with
    | [ line ] -> F.string0 (String.length line) line
    | lines -> F.vbox (List.map (fun l -> F.string0 (String.length l) l) lines)

  let str (render : Format.formatter -> unit) : string =
    Format.asprintf "%t" render

  (* ---------------------------------------------------------------- *)

  let formatDec g_ d_ = to_format (P.decl (env ()) (R.dec (opts ()) g_ d_))

  let formatDecList g_ ds =
    to_format (P.decls (env ()) ~brackets:`Braces (R.dec_list (opts ()) g_ ds))

  (* The only entry point that needs a pending substitution on a declaration
     list, so it reaches past the assembled interface to [Term]. *)
  let formatDecList' g_ (ds, s) =
    to_format
      (P.decls (env ()) ~brackets:`Braces
         (Tm.dec_list_sub (opts ()) g_ (ds, s)))

  let formatExp g_ u_ = to_format (P.term (env ()) (R.exp (opts ()) g_ u_))

  let formatSpine g_ s_ =
    List.map (fun t -> to_format (P.term (env ()) t)) (R.spine (opts ()) g_ s_)

  let formatConDec condec_ =
    to_format (P.cmd (env ()) (R.con_dec (opts ()) ~hide:false condec_))

  let formatConDecI condec_ =
    to_format (P.cmd (env ()) (R.con_dec (opts ()) ~hide:true condec_))

  (* [=] and [;] are not STELF surface syntax, so constraint rendering is
     assembled here rather than being forced through the CST. That is exactly
     why [Resugar.cnstr] returns a [cnstr_form] instead of a term. *)
  let show_cnstr (form : R.cnstr_form) : string =
    let e = env () in
    match form with
    | R.Solved -> "Solved Constraint"
    | R.Eqn (a, b) -> P.term_to_string e a ^ " = " ^ P.term_to_string e b
    | R.Fgn [] -> "Empty Constraint"
    | R.Fgn ts -> String.concat "; " (List.map (P.term_to_string e) ts)

  let formatCnstr cnstr_ =
    to_format (fun fmt ->
        Format.pp_print_string fmt (show_cnstr (R.cnstr (opts ()) (ref cnstr_))))

  let formatCnstrs cnstrL =
    to_format (fun fmt ->
        match cnstrL with
        | [] -> Format.pp_print_string fmt "Empty Constraint"
        | _ ->
            Format.pp_print_string fmt
              (String.concat "; "
                 (List.map (fun c -> show_cnstr (R.cnstr (opts ()) c)) cnstrL)
              ^ "."))

  let formatCtx g0_ g_ =
    to_format (P.decls (env ()) ~brackets:`Braces (R.ctx (opts ()) g0_ g_))

  let decToString g_ d_ = str (P.decl (env ()) (R.dec (opts ()) g_ d_))
  let expToString g_ u_ = str (P.term (env ()) (R.exp (opts ()) g_ u_))

  let conDecToString condec_ =
    str (P.cmd (env ()) (R.con_dec (opts ()) ~hide:false condec_))

  let cnstrToString cnstr_ = show_cnstr (R.cnstr (opts ()) (ref cnstr_))

  let cnstrsToString cnstrL =
    match cnstrL with
    | [] -> "Empty Constraint"
    | _ ->
        String.concat "; "
          (List.map (fun c -> show_cnstr (R.cnstr (opts ()) c)) cnstrL)
        ^ "."

  let ctxToString g0_ g_ =
    str (P.decls (env ()) ~brackets:`Braces (R.ctx (opts ()) g0_ g_))

  let evarInstToString xnames =
    let e = env () in
    match R.evar_inst (opts ()) xnames with
    | [] -> "Empty Substitution."
    | xs ->
        String.concat "; "
          (List.map (fun (n, t) -> n ^ " = " ^ P.term_to_string e t) xs)
        ^ "."

  (* Pure IntSyn traversals, not printing: moved across unchanged from
     [Print_]. *)
  let rec collectEVars (a, xs_) = match a with
    | [] -> xs_
    | (u_, _) :: xnames ->
        collectEVars
          (xnames, Abstract.collectEVars IntSyn.Null (u_, IntSyn.id) xs_)

  let eqCnstr r1 r2 = r1 == r2

  let rec mergeConstraints (a, cnstrs2) = match a with
    | [] -> cnstrs2
    | cnstr :: cnstrs1 ->
        if List.exists (eqCnstr cnstr) cnstrs2 then
          mergeConstraints (cnstrs1, cnstrs2)
        else cnstr :: mergeConstraints (cnstrs1, cnstrs2)

  let rec collectConstraints = function
    | [] -> []
    | IntSyn.EVar ({ contents = None }, _, _, cnstrs) :: xs_ ->
        mergeConstraints (Constraints.simplify !cnstrs, collectConstraints xs_)
    | _ :: xs_ -> collectConstraints xs_

  let evarCnstrsToStringOpt xnames =
    let ys_ = collectEVars (xnames, []) in
    match collectConstraints ys_ with
    | [] -> None
    | cnstrL -> Some (cnstrsToString cnstrL)

  let formatWorlds (Tomega.Worlds cids) =
    let names = R.worlds (opts ()) cids in
    to_format (fun fmt ->
        Format.fprintf fmt "@[<hov 1>(%a)@]"
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ |@ ")
             (fun fmt (ns, n) ->
               Format.pp_print_string fmt (String.concat "." (ns @ [ n ]))))
          names)

  let worldsToString w_ = F.makestring_fmt (formatWorlds w_)

  let printSgn () =
    IntSyn.sgnApp (fun cid ->
        print_string (conDecToString (IntSyn.sgnLookup cid));
        print_string "\n")
end
