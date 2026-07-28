module Fixity = PRETTY.Fixity
module Lex = Lex

type env = PRETTY.env = {
  fixity : string list * string -> Fixity.t;
  margin : int;
}

module type PRETTY = PRETTY.PRETTY

let default : env = { fixity = (fun _ -> Fixity.Nonfix); margin = 80 }

(* Juxtaposition binds tighter than any declarable operator: [Modern.jux_op]
   sits at [Names.Fixity.inc maxPrec], and [maxPrec] is 9999. *)
let jux_prec = 10_000

(* One above juxtaposition, so nothing at all prints bare at this level. This
   is the precedence of a [parse_expr1] slot. *)
let atom_prec = jux_prec + 1

(** Which syntactic slot a term is being rendered into.

    These are the three slots the modern grammar actually has, and the rules
    below are read straight off [Modern.parse_expr]:

    - [Expr] is a full [parse_expr]. Everything prints bare here.
    - [Trail n] is the rightmost operand of an enclosing operator of effective
      precedence [n]. [parse_expr] ends with an optional [parse_expr_trail], so
      binders and arrow chains print bare here; [%the] does not, because
      [parse_expr_trail] has no [%the] alternative.
    - [Arg n] is any other operand. Only operator applications of precedence at
      least [n] print bare.

    A [parse_expr1] slot is [Arg atom_prec]: nothing but an atom fits. *)
type slot = Expr | Trail of int | Arg of int

(* The precedence a child must reach to print without parentheses, given the
   parent's precedence and whether the child sits on the parent's associative
   side. Equal precedence is bare only on that side. *)
let child_prec ~(parent : int) ~(associative : bool) : int =
  if associative then parent else parent + 1

(* Does a binder, lambda or arrow chain print bare in this slot? *)
let trail_ok : slot -> bool = function Expr | Trail _ -> true | Arg _ -> false

(* Does an operator application of precedence [p] print bare in this slot? *)
let prec_ok (p : int) : slot -> bool = function
  | Expr -> true
  | Trail n | Arg n -> p >= n

module Make_Pretty (Cst : Cst.CST) :
  PRETTY
    with type term = Cst.term
     and type decl = Cst.decl
     and type cmd = Cst.cmd = struct
  type term = Cst.term
  type decl = Cst.decl
  type cmd = Cst.cmd

  exception Unsupported of string

  module V = Cst.View
  module T = Cst.View.Term

  let esc = Lex.escape_ident

  (* A qualified name is written [%val ( a b c )] -- always with the
     parentheses, because the unparenthesised form takes a single identifier
     and cannot carry a namespace. Dots are not separators in this grammar. *)
  let pp_qualified fmt ((ns, name) : Cst.symbol) (form : Cst.qid_form) =
    let kw = match form with Cst.Val -> "%val" | Cst.Abs -> "%abs" in
    match ns with
    | [] -> Format.fprintf fmt "%s %s" kw (esc name)
    | _ ->
        Format.fprintf fmt "@[<hov 2>%s (%a %s)@]" kw
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
             (fun fmt c -> Format.pp_print_string fmt (esc c)))
          ns (esc name)

  (* [%val] is the universal escape hatch for a name that cannot be written
     bare: [Modern.classify] makes [Qualified] an atom unconditionally, so it
     opts a symbol out of operator status, out of the uppercase/lowercase
     lexical classes, and is the only spelling that carries a namespace.

     The cost, which no spelling avoids, is that a namespaced operator can
     never print infix. *)
  let bare_ok (env : env) ((ns, name) : Cst.symbol) ~(uppercase : bool) : bool =
    ns = [] && name <> ""
    && Lex.is_uppercase_ident name = uppercase
    && (not (uppercase && name = "_"))
    && env.fixity (ns, name) = Fixity.Nonfix

  let pp_ident (env : env) fmt (sym : Cst.symbol) ~(uppercase : bool) =
    if bare_ok env sym ~uppercase then
      Format.pp_print_string fmt (esc (snd sym))
    else pp_qualified fmt sym Cst.Val

  let pp_tag fmt (tag : Cst.internal_tag) =
    match tag with
    | Cst.Kind_tag -> Format.pp_print_string fmt "%%kind"
    | Cst.Subst_tag -> Format.pp_print_string fmt "%%subst"
    | Cst.Shift_tag n -> Format.fprintf fmt "^%d" n
    | Cst.Undef_tag -> Format.pp_print_string fmt "%%undef"
    | Cst.Proj_tag l -> Format.fprintf fmt "#%s" l
    | Cst.Cutoff_tag -> Format.pp_print_string fmt "%%"
    | Cst.Elided_tag -> Format.pp_print_string fmt "..."
    | Cst.Opaque_tag s -> Format.pp_print_string fmt s

  (* Wrap in parentheses when [cond]. The box goes inside, so a broken line
     indents under the open paren rather than under the enclosing construct. *)
  let parens cond fmt (body : Format.formatter -> unit) =
    if cond then Format.fprintf fmt "@[<hov 1>(%t)@]" body else body fmt

  let rec pp_term (env : env) (slot : slot) fmt (tm : term) : unit =
    match T.view tm with
    | T.Lowercase (_, sym) -> pp_ident env fmt sym ~uppercase:false
    | T.Uppercase (_, sym) -> pp_ident env fmt sym ~uppercase:true
    | T.Qualified (_, sym, form) -> pp_qualified fmt sym form
    | T.Text (_, s) -> Format.pp_print_string fmt (Lex.quote_text s)
    (* Neither of these has a surface form of its own; both re-parse as an
       ordinary variable of the matching lexical class, which is what they
       denote. *)
    | T.ExistVar (_, n) -> pp_ident env fmt ([], n) ~uppercase:true
    | T.FreeVar (_, n) -> pp_ident env fmt ([], n) ~uppercase:false
    | T.Omitted _ -> Format.pp_print_string fmt "_"
    | T.Typ _ -> Format.pp_print_string fmt "%type"
    (* [%(ns (M))] is an atom, unlike the [%local ns M] spelling, so it needs
       no parentheses of its own in any slot. *)
    | T.Local (_, ns, body) ->
        Format.fprintf fmt "@[<hov 2>%%(%a (%a))@]"
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
             (fun fmt c -> Format.pp_print_string fmt (esc c)))
          ns (pp_term env Expr) body
    | T.Foreign (_, body) -> pp_term env slot fmt body
    | T.Internal (_, tag, kids) ->
        (* Tagged so a terminal frontend can dim it; [Format] drops tags
           unless the formatter has them enabled, so plain output is clean. *)
        Format.fprintf fmt "@{<dim>";
        (match kids with
        | [] -> pp_tag fmt tag
        | _ ->
            Format.fprintf fmt "@[<hov 2>(%a" pp_tag tag;
            List.iter
              (fun k ->
                Format.fprintf fmt "@ %a" (pp_term env (Arg atom_prec)) k)
              kids;
            Format.fprintf fmt ")@]");
        Format.fprintf fmt "@}"
    | T.MacroParam (_, lvl, n) ->
        Format.fprintf fmt "@{<dim>%%%%arg%s.%d@}"
          (match lvl with None -> "" | Some j -> string_of_int j)
          n
    | T.Pi (_, ds, body) -> pp_binder env slot fmt ~brackets:`Braces ds body
    | T.Lam (_, ds, body) -> pp_binder env slot fmt ~brackets:`Brackets ds body
    | T.Arrow (_, a, b) -> pp_arrow env slot fmt (collect_arrow a b)
    | T.BackArrow (_, a, b) ->
        (* [BackArrow] reviews to [Arrow_ (loc, b, a)], so it denotes the same
           term as the forward arrow with the operands swapped. Rendering it
           forwards keeps one arrow-printing path. *)
        pp_arrow env slot fmt (collect_arrow b a)
    | T.HasType (_, body, ty) ->
        (* [%the] exists only at the head of [parse_expr]; there is no trailing
           form, so anything narrower than [Expr] needs parentheses. *)
        parens (slot <> Expr) fmt (fun fmt ->
            Format.fprintf fmt "@[<hov 2>%%the@ %a@ %a@]"
              (pp_term env (Arg atom_prec))
              ty (pp_term env Expr) body)
    | T.App (_, head, args) -> pp_app env slot fmt head args

  (* [%pi A %-> B %-> C] is one chain, not nested arrows: flattening lets the
     whole chain share a box and one [%pi]. *)
  and collect_arrow (a : term) (b : term) : term list =
    match T.view b with
    | T.Arrow (_, b1, b2) -> a :: collect_arrow b1 b2
    | T.BackArrow (_, b1, b2) -> a :: collect_arrow b2 b1
    | _ -> [ a; b ]

  and pp_arrow (env : env) (slot : slot) fmt (chain : term list) : unit =
    parens
      (not (trail_ok slot))
      fmt
      (fun fmt ->
        Format.fprintf fmt "@[<hov 2>%%pi@ ";
        List.iteri
          (fun i t ->
            if i > 0 then Format.fprintf fmt "@ %%-> ";
            (* Every element is a full [parse_expr] that stops at the next
               [%->], so only the last may trail. An arrow in domain position
               would swallow the rest of the chain. *)
            let s = if i = List.length chain - 1 then Expr else Arg atom_prec in
            pp_term env s fmt t)
          chain;
        Format.fprintf fmt "@]")

  and pp_binder (env : env) (slot : slot) fmt
      ~(brackets : [ `None | `Braces | `Brackets ]) (ds : decl list)
      (body : term) : unit =
    parens
      (not (trail_ok slot))
      fmt
      (fun fmt ->
        Format.fprintf fmt "@[<hov 2>%a@ %a@]" (pp_decls env ~brackets) ds
          (pp_term env Expr) body)

  and pp_app (env : env) (slot : slot) fmt (head : term) (args : term list) :
      unit =
    (* The head's declared fixity only applies when the application is
       saturated for that fixity. An over-applied operator falls back to
       juxtaposition, which is exactly how it re-parses: [Modern.infix_op]
       builds [App (App (op, [a]), [b])], and [Term.view] n-arises that back
       into a single flat [App], so a flat over-applied node is what a
       round trip produces. *)
    let fx =
      match T.view head with
      | T.Lowercase (_, sym) | T.Uppercase (_, sym) -> env.fixity sym
      | _ -> Fixity.Nonfix
    in
    match (fx, args) with
    | Fixity.Infix (p, assoc), [ a; b ] ->
        let lp = child_prec ~parent:p ~associative:(assoc = Fixity.Left) in
        let rp = child_prec ~parent:p ~associative:(assoc = Fixity.Right) in
        parens
          (not (prec_ok p slot))
          fmt
          (fun fmt ->
            Format.fprintf fmt "@[<hov 2>%a@ %a %a@]" (pp_term env (Arg lp)) a
              (pp_operator env) head
              (pp_term env (if trail_ok slot then Trail rp else Arg rp))
              b)
    | Fixity.Prefix p, [ a ] ->
        parens
          (not (prec_ok p slot))
          fmt
          (fun fmt ->
            Format.fprintf fmt "@[<hov 2>%a@ %a@]" (pp_operator env) head
              (pp_term env (if trail_ok slot then Trail p else Arg p))
              a)
    | Fixity.Postfix p, [ a ] ->
        parens
          (not (prec_ok p slot))
          fmt
          (fun fmt ->
            Format.fprintf fmt "@[<hov 2>%a@ %a@]" (pp_term env (Arg p)) a
              (pp_operator env) head)
    | _, [] -> pp_term env slot fmt head
    | _, _ ->
        parens
          (not (prec_ok jux_prec slot))
          fmt
          (fun fmt ->
            let last = List.length args - 1 in
            Format.fprintf fmt "@[<hov 2>%a" (pp_term env (Arg jux_prec)) head;
            List.iteri
              (fun i a ->
                (* Only the final argument may be a binder or arrow chain:
                   [parse_expr] accepts a trail exactly once, at the end. *)
                let s =
                  if i = last && trail_ok slot then Trail (jux_prec + 1)
                  else Arg atom_prec
                in
                Format.fprintf fmt "@ %a" (pp_term env s) a)
              args;
            Format.fprintf fmt "@]")

  (* An operator in operator position is written bare -- that is the one place
     its fixity is wanted -- so [pp_ident]'s [%val] guard must not fire. *)
  and pp_operator (env : env) fmt (head : term) : unit =
    match T.view head with
    | T.Lowercase (_, ([], name)) | T.Uppercase (_, ([], name)) ->
        Format.pp_print_string fmt (esc name)
    | _ -> pp_term env (Arg atom_prec) fmt head

  and pp_decl (env : env) fmt (d : decl) : unit =
    let names, ty =
      match V.Decl.view d with
      | V.Decl.Decl1 (_, names, ty, _) -> (names, ty)
      | V.Decl.Decl0 (_, names, ty) -> (names, ty)
    in
    let pp_name fmt = function
      | None -> Format.pp_print_string fmt "_"
      | Some n -> Format.pp_print_string fmt (esc n)
    in
    let omitted = match T.view ty with T.Omitted _ -> true | _ -> false in
    let pp_names fmt =
      match names with
      | [ n ] -> pp_name fmt n
      | _ ->
          Format.fprintf fmt "@[<hov 1>(%a)@]"
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
               pp_name)
            names
    in
    (* An omitted type is written by leaving the slot empty, not by writing
       [_]: a literal [_] would parse as an [Omitted] {e term}, which is a
       different thing from a binder with no annotation. *)
    if omitted then pp_names fmt
    else Format.fprintf fmt "@[<hov 2>%t@ %a@]" pp_names (pp_term env Expr) ty

  and pp_decls (env : env) ~(brackets : [ `None | `Braces | `Brackets ]) fmt
      (ds : decl list) : unit =
    let o, c =
      match brackets with
      | `None -> ("", "")
      | `Braces -> ("{", "}")
      | `Brackets -> ("[", "]")
    in
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
      (fun fmt d -> Format.fprintf fmt "%s%a%s" o (pp_decl env) d c)
      fmt ds

  let pp_cmd (env : env) fmt (c : cmd) : unit =
    let pp_id fmt s = Format.pp_print_string fmt (esc s) in
    let pp_ids fmt = function
      | [ id ] -> pp_id fmt id
      | ids ->
          Format.fprintf fmt "@[<hov 1>(%a)@]"
            (Format.pp_print_list
               ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
               pp_id)
            ids
    in
    match V.Cmd.view c with
    (* A sort of kind [type] has no binders at all, and the separator has to go
       with them or the line ends in a space. *)
    | V.Cmd.Sort (_, ids, []) ->
        Format.fprintf fmt "@[<hov 2>%%sort@ %a@]" pp_ids ids
    | V.Cmd.Sort (_, ids, ds) ->
        Format.fprintf fmt "@[<hov 2>%%sort@ %a@ %a@]" pp_ids ids
          (pp_decls env ~brackets:`Braces)
          ds
    | V.Cmd.Term (_, d) ->
        Format.fprintf fmt "@[<hov 2>%%term@ %a@]" (pp_decl env) d
    | V.Cmd.Define (_, d) -> (
        match V.Define.view d with
        | V.Define.Define (_, id, tm, ty) ->
            (* Surface order is [%def NAME TYPE TERM]; the view's order is
               (name, term, type). See [Modern.parse_define]. *)
            Format.fprintf fmt "@[<hov 2>%%def@ %s@ %a@ %a@]"
              (match id with None -> "_" | Some s -> esc s)
              (pp_term env (Arg atom_prec))
              (match ty with
              | Some ty -> ty
              | None -> T.review (T.Omitted (V.Loc.review V.Loc.Ghost)))
              (pp_term env Expr) tm)
    | V.Cmd.Inline (_, id, tm) ->
        Format.fprintf fmt "@[<hov 2>%%inline@ %a@ %a@]" pp_id id
          (pp_term env Expr) tm
    | V.Cmd.Block (_, id, items) ->
        Format.fprintf fmt "@[<hov 2>%%block@ %a" pp_id id;
        List.iter
          (fun it ->
            match V.BlockItem.view it with
            | V.BlockItem.Any (_, d) ->
                Format.fprintf fmt "@ [%a]" (pp_decl env) d
            | V.BlockItem.All (_, d) ->
                Format.fprintf fmt "@ {%a}" (pp_decl env) d)
          items;
        Format.fprintf fmt "@]"
    | V.Cmd.Union (_, id, ids) ->
        Format.fprintf fmt "@[<hov 2>%%union@ %a@ @[<hov 1>(%a)@]@]" pp_id id
          (Format.pp_print_list
             ~pp_sep:(fun fmt () -> Format.fprintf fmt "@ ")
             pp_id)
          ids
    | _ ->
        raise
          (Unsupported
             "Pretty.cmd: only the command forms produced by resugaring \
              (%sort, %term, %def, %inline, %block, %union) are rendered")

  (* [env.margin] applies only on the string-producing entry points, because
     it is only there that we own the formatter.

     [Format.pp_set_margin] is not a benign setter: it routes through
     [pp_set_max_indent] to [pp_rinit], which clears the formatter's queue and
     so discards anything already written. That makes set-and-restore around a
     caller's formatter silently drop output, and setting without restoring
     would mutate state the caller owns. Terms rendered into a caller's
     formatter therefore break at that formatter's margin, which is the
     behaviour a [Format] user expects from a [%a]-style printer anyway. *)
  let to_string (env : env) (body : Format.formatter -> unit) : string =
    let buf = Buffer.create 256 in
    let fmt = Format.formatter_of_buffer buf in
    Format.pp_set_margin fmt env.margin;
    body fmt;
    Format.pp_print_flush fmt ();
    Buffer.contents buf

  let term env tm fmt = pp_term env Expr fmt tm
  let decl env d fmt = pp_decl env fmt d
  let decls env ~brackets ds fmt = pp_decls env ~brackets fmt ds
  let cmd env c fmt = pp_cmd env fmt c
  let term_to_string env tm = to_string env (fun fmt -> pp_term env Expr fmt tm)
  let decl_to_string env d = to_string env (fun fmt -> pp_decl env fmt d)
  let cmd_to_string env c = to_string env (fun fmt -> pp_cmd env fmt c)
end
