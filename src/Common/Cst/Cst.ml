open Basis

module type CST = CST.CST

module Make_Cst (Paths : Paths.PATHS.PATHS) = struct
  module Paths = Paths

  (* Location type for source tracking - use simple int-based representation *)
  type loc = { start_pos : int; end_pos : int }
  [@@deriving show { with_path = false }, eq]

  (* Basic type aliases *)
  type name = string [@@deriving show { with_path = false }, eq]
  type namespace = string list [@@deriving show { with_path = false }, eq]
  type symbol = namespace * name [@@deriving show { with_path = false }, eq]

  (* Distinguishes [%val NAME] (shadow-aware: an open %scope's case label
     wins over an outer/toplevel declaration of the same name) from
     [%abs NAME] (toplevel-first: prefers the current %require group's own
     toplevel declaration, bypassing %scope shadowing, falling back to
     shadow-aware lookup only if no toplevel binding exists). See
     [Names.resolveQid]. Qualified forms ([%val ( NAME S )] /
     [%abs ( NAME S )]) are unaffected by this distinction. *)
  type qid_form = Val | Abs [@@deriving show { with_path = false }, eq]

  (* Location helpers *)
  let mk_loc (start : int) (end_ : int) : loc =
    { start_pos = start; end_pos = end_ }

  let loc_to_region (loc : loc) : Paths.region =
    Paths.Reg (loc.start_pos, loc.end_pos)

  let ghost : loc = { start_pos = 0; end_pos = 0 }

  (* Tags for printer-internal term nodes. These name the parts of the
     internal syntax that have no STELF surface form at all, so that
     resugaring can be a total function. Terms containing an [Internal_]
     node are deliberately unparseable -- they exist only to be printed. *)
  type internal_tag =
    | Kind_tag  (** [IntSyn.Uni Kind]: no surface syntax exists. *)
    | Subst_tag  (** Explicit substitution; children are its fronts. *)
    | Shift_tag of int  (** The [^n] tail of a substitution. *)
    | Undef_tag  (** An undefined substitution front. *)
    | Proj_tag of string  (** Block projection label, pre-rendered. *)
    | Cutoff_tag  (** [printDepth] was exceeded; prints [%%]. *)
    | Elided_tag  (** [printLength] was exceeded; prints [...]. *)
    | Opaque_tag of string  (** Verbatim token plus children; last resort. *)
  [@@deriving show { with_path = false }, eq]

  (* Mutual recursion: decl and term *)
  type decl = Dec_ of string option list * term * loc

  and term =
    | Arrow_ of loc * term * term
    | Pi_ of loc * decl * term
    | Lam_ of loc * decl * term
    | App_ of loc * term * term
    | Hastype_ of loc * term * term
    | Omitted_ of loc
    | Lcid_ of string list * string * loc
    | Ucid_ of string list * string * loc
    | Quid_ of string list * string * qid_form * loc
    | Scon_ of string * loc
    | Evar_ of string * loc
    | Fvar_ of string * loc
    | Typ_ of loc
    | MacroParam_ of loc * int option * int
    | Local_ of loc * namespace * term
    | Foreign_ of loc * term
        (** A term coming from a foreign/FFI representation. Transparent: it
            prints as just its child, so it round-trips through the parser. *)
    | Internal_ of loc * internal_tag * term list
        (** A printer-internal node with no surface syntax. See {!internal_tag}.
        *)
  [@@deriving eq]

  let rec pp_term (fmt : Format.formatter) (x : term) : unit =
    match x with
    | Arrow_ (l, t, u) -> Format.fprintf fmt "{%a} %a" pp_term t pp_term u
    | Pi_ (l, t, u) -> Format.fprintf fmt "{%a} %a" pp_decl t pp_term u
    | Lam_ (l, t, u) -> Format.fprintf fmt "[%a] %a" pp_decl t pp_term u
    | App_ (l, t, u) -> Format.fprintf fmt "(%a %a)" pp_term t pp_term u
    | Hastype_ (l, t, u) -> Format.fprintf fmt "%%the %a %a" pp_term t pp_term u
    | Omitted_ l -> Format.fprintf fmt "_"
    | Lcid_ (ns, name, l) -> Format.fprintf fmt "%s" name
    | Ucid_ (ns, name, l) -> Format.fprintf fmt "$%s" name
    | Quid_ (ns, name, form, l) ->
        let prefix = match form with Val -> "%val" | Abs -> "%abs" in
        Format.fprintf fmt "%s(%s.%s)" prefix (Stdlib.String.concat "." ns) name
    | Scon_ (str, l) -> Format.fprintf fmt "%%[%a%%]" Format.pp_print_string str
    | Evar_ (name, l) -> Format.fprintf fmt "_?%s" name
    | Fvar_ (name, l) -> Format.fprintf fmt "__%s" name
    | Typ_ l -> Format.fprintf fmt "%%type"
    | MacroParam_ (l, opt, n) ->
        Format.fprintf fmt "%%arg %d %d" (Stdlib.Option.value ~default:0 opt) n
    | Local_ (l, ns, t) ->
        Format.fprintf fmt "%%local %s %a"
          (Stdlib.String.concat "." ns)
          pp_term t
    | Foreign_ (l, t) -> Format.fprintf fmt "%%foreign %a" pp_term t
    | Internal_ (l, tag, ts) ->
        Format.fprintf fmt "%%internal(%a%a)" pp_internal_tag tag
          (fun fmt ->
            Stdlib.List.iter (fun t -> Format.fprintf fmt " %a" pp_term t))
          ts

  and pp_decl_name (fmt : Format.formatter) (n : name option) : unit =
    match n with
    | None -> Format.fprintf fmt "_"
    | Some name -> Format.fprintf fmt "%s" name

  and pp_decl (fmt : Format.formatter) (x : decl) : unit =
    match x with
    | Dec_ (names, t, l) -> (
        match names with
        | [] -> Format.fprintf fmt "%a" pp_term t
        | [ name ] -> Format.fprintf fmt "%a %a" pp_decl_name name pp_term t
        | names ->
            Format.fprintf fmt "(%a) %a"
              (Format.pp_print_list pp_decl_name)
              names pp_term t)

  and show_term (x : term) : string = Format.asprintf "%a" pp_term x
  and show_decl (x : decl) : string = Format.asprintf "%a" pp_decl x

  (* Constant/block declarations *)
  type conDec =
    | ConstantDecl_ of decl
    | BlockDecl_ of string * decl list * decl list
    | BlockDef_ of string * symbol list
    | ConstantDef_ of string * term * term option
  [@@deriving show { with_path = false }, eq]

  (* Query/Define/Solve payload types *)
  type query = Query_ of string option * term
  [@@deriving show { with_path = false }, eq]

  type define = Define_ of string option * term * term option
  [@@deriving show { with_path = false }, eq]

  type solve = Solve_ of string option * term
  [@@deriving show { with_path = false }, eq]

  (* Mode syntax *)
  type mode = Plus_ | Star_ | Minus_ | Minus1_
  [@@deriving show { with_path = false }, eq]

  type modeTerm =
    | ModeTermRoot_ of term
    | ModeTermPi_ of mode * decl * modeTerm
  [@@deriving show { with_path = false }, eq]

  type modeSpine = ModeSpineInternal_ of (mode * string option) list
  [@@deriving show { with_path = false }, eq]

  type modeDec = ModeDec_ of modeTerm
  [@@deriving show { with_path = false }, eq]

  (* Structure expressions and signature expressions *)
  type strexp = StrExp_ of symbol [@@deriving show { with_path = false }, eq]

  type inst =
    | ConInst_ of symbol * loc * term
    | StrInst_ of symbol * loc * strexp
  [@@deriving show { with_path = false }, eq]

  type sigexp = TheSig_ | SigId_ of string | WhereSig_ of sigexp * inst list
  [@@deriving show { with_path = false }, eq]

  type sigdef = SigDef_ of string option * sigexp
  [@@deriving show { with_path = false }, eq]

  type structDec =
    | StructDecl_ of string option * sigexp
    | StructDef_ of string option * strexp
  [@@deriving show { with_path = false }, eq]

  type structDef = StructDef_ of string option * strexp
  [@@deriving show { with_path = false }, eq]

  type fixity = Left_ | Right_ | Prefix_ | Postfix_ | Middle_ | FNone_
  [@@deriving show { with_path = false }, eq]

  type block_item = BlockSome_ of decl | BlockPi_ of decl
  [@@deriving show { with_path = false }, eq]

  type order =
    | Varg_ of loc * string list
    | Lex_ of loc * order list
    | Simul_ of loc * order list
  [@@deriving show { with_path = false }, eq]

  (* Top-level commands *)
  type cmd =
    | QueryCmd_ of int option * int option * int option * query
    | QueryTabledCmd_ of int option * int option * int option * query
    | AdhocQueryCmd_ of query
    | UniqueCmd_ of term
    | ModeCmd_ of modeDec
    | DefineCmd_ of define
    | DeclCmd_ of term
    | InlineCmd_ of string * term
    | SymbolCmd_ of string * string
    | FreezeCmd_ of string list
    | ThawCmd_ of string list
    | SortCmd_ of string list * decl list
    | TermCmd_ of decl
    | BlockCmd_ of string * block_item list
    | UnionCmd_ of string * string list
    | WorldsCmd_ of string list * term list
    | DeterministicCmd_ of string list
    | EvalCmd_ of cmd list
    | PrecCmd_ of fixity * int * string list
    | SolveCmd_ of solve
    | StopCmd_
    | QuitCmd_
    | HelpCmd_ of string option
    | GetCmd_ of string
    | SetCmd_ of string * string
    | VersionCmd_
    | TotalCmd_ of order list * term list
    | TerminatesCmd_ of order list * term list
    | CoversCmd_ of modeDec
    | NameCmd_ of string
    | ProseCmd_ of string
    | ReducesCmd_ of string * term list
    | Macro_ of int * string * cmd
        (** Defines a macro, taking its location, number of params, name, and
            the body *)
    | Seq_ of item list
        (** A sequence of commands, for use withthe module system*)
    | Require_ of string list  (** Ensure that the given path is loaded *)
    | Open_ of string list  (** Open a scope into the scope *)
    | Scope_ of string * cmd  (** Enter into a new scope *)
    | Use_ of string list * term list  (** Apply a macro *)

  and item = Outer of string | Cmd of cmd
  [@@deriving show { with_path = false }, eq]

  (* Term constructor module *)
  module Term = struct
    type nonrec t = term

    let lowercase ?fc:(loc = ghost) (namespace, name) =
      Lcid_ (namespace, name, loc)

    let uppercase ?fc:(loc = ghost) (namespace, name) =
      Ucid_ (namespace, name, loc)

    let qualified ?fc:(loc = ghost) ?(form = Val) (namespace, name) =
      Quid_ (namespace, name, form, loc)

    let text ?fc:(loc = ghost) str = Scon_ (str, loc)
    let exist_var ?fc:(loc = ghost) name = Evar_ (name, loc)
    let free_var ?fc:(loc = ghost) name = Fvar_ (name, loc)

    module Sugar = struct
      let arrow ?fc:(loc = ghost) tm1 tm2 = Arrow_ (loc, tm1, tm2)
      let backarrow ?fc:(loc = ghost) tm1 tm2 = Arrow_ (loc, tm2, tm1)
    end

    let pi ?fc:(loc = ghost) decls body =
      let rec fold_right f lst acc =
        match lst with [] -> acc | x :: xs -> f x (fold_right f xs acc)
      in
      match decls with
      | [] -> body
      | first :: rest ->
          let inner = fold_right (fun d acc -> Pi_ (ghost, d, acc)) rest body in
          Pi_ (loc, first, inner)

    let lam ?fc:(loc = ghost) decls body =
      let rec fold_right f lst acc =
        match lst with [] -> acc | x :: xs -> f x (fold_right f xs acc)
      in
      match decls with
      | [] -> body
      | first :: rest ->
          let inner =
            fold_right (fun d acc -> Lam_ (ghost, d, acc)) rest body
          in
          Lam_ (loc, first, inner)

    let app ?fc:(loc = ghost) head args =
      match args with
      | [] -> head
      | _ ->
          let rec fold_left f acc lst =
            match lst with [] -> acc | x :: xs -> fold_left f (f acc x) xs
          in
          let rev = List.rev args in
          let last = List.hd rev in
          let init = List.rev (List.tl rev) in
          let inner =
            fold_left (fun acc arg -> App_ (ghost, acc, arg)) head init
          in
          App_ (loc, inner, last)

    let has_type ?fc:(loc = ghost) tm ty = Hastype_ (loc, tm, ty)
    let[@warning "-16"] omitted ?fc:(loc = ghost) = Omitted_ loc
    let typ ?fc:(loc = ghost) () = Typ_ loc
  end

  (* Declaration constructor module *)
  module Decl = struct
    type nonrec t = decl

    let decl1 ?fc:(loc = ghost) names typ = Dec_ (names, typ, loc)
    let decl0 ?fc:(loc = ghost) names = Dec_ (names, Omitted_ ghost, loc)
  end

  (* Constant/block declaration constructor module *)
  module ConDec = struct
    type nonrec t = conDec

    let constant_decl ?fc:(loc = ghost) decl = ConstantDecl_ decl

    let block_decl ?fc:(loc = ghost) name decls1 decls2 =
      BlockDecl_ (name, decls1, decls2)

    let block_def ?fc:(loc = ghost) name symbols = BlockDef_ (name, symbols)

    let constant_def ?fc:(loc = ghost) name term1 term2_opt =
      ConstantDef_ (name, term1, term2_opt)
  end

  (* Mode constructor module *)
  module Mode = struct
    type nonrec mode = mode
    type nonrec modeTerm = modeTerm
    type nonrec modedec = modeDec

    let plus ?fc:(loc = ghost) () = Plus_
    let star ?fc:(loc = ghost) () = Star_
    let minus ?fc:(loc = ghost) () = Minus_
    let minus1 ?fc:(loc = ghost) () = Minus1_

    module Short = struct
      type nonrec modeTerm = modeTerm
      type nonrec modeSpine = modeSpine

      let mode_nil ?fc:(loc = ghost) () = ModeSpineInternal_ []

      let mode_app ?fc:(loc = ghost) (m, name_opt) (ModeSpineInternal_ spine) =
        ModeSpineInternal_ ((m, name_opt) :: spine)

      let mode_root ?fc:(loc = ghost) (ns, name) (ModeSpineInternal_ _spine) =
        ModeTermRoot_ (Quid_ (ns, name, Val, loc))

      let to_modeDec ?fc:(loc = ghost) mt = ModeDec_ mt
    end

    module Full = struct
      let mode_root ?fc:(loc = ghost) tm = ModeTermRoot_ tm
      let mode_pi ?fc:(loc = ghost) m d body = ModeTermPi_ (m, d, body)
      let to_modeDec ?fc:(loc = ghost) mt = ModeDec_ mt
    end
  end

  (* Module/signature constructor module *)
  module Struct = struct
    type nonrec strexp = strexp
    type nonrec inst = inst
    type nonrec sigexp = sigexp
    type nonrec sigdef = sigdef
    type nonrec structdec = structDec

    let str_exp ?fc:(loc = ghost) symbol = StrExp_ symbol

    let con_inst ?fc:(loc = ghost) (symbol, loc2) term =
      ConInst_ (symbol, loc2, term)

    let str_inst ?fc:(loc = ghost) (symbol, loc2) strexp =
      StrInst_ (symbol, loc2, strexp)

    let[@warning "-16"] thesig ?fc:(loc = ghost) = TheSig_
    let sig_id ?fc:(loc = ghost) name = SigId_ name
    let where_sig ?fc:(loc = ghost) sigexp insts = WhereSig_ (sigexp, insts)
    let sig_def ?fc:(loc = ghost) name_opt sigexp = SigDef_ (name_opt, sigexp)

    let struct_decl ?fc:(loc = ghost) name_opt sigexp =
      StructDecl_ (name_opt, sigexp)

    let struct_def ?fc:(loc = ghost) name_opt strexp : structDec =
      StructDef_ (name_opt, strexp)
  end

  (* Query/Define/Solve constructor module *)
  module Query = struct
    type nonrec query = query
    type nonrec define = define
    type nonrec solve = solve

    let query ?fc:(loc = ghost) name_opt term = Query_ (name_opt, term)

    let define ?fc:(loc = ghost) name_opt term1 term2_opt =
      Define_ (name_opt, term1, term2_opt)

    let solve ?fc:(loc = ghost) name_opt term = Solve_ (name_opt, term)
  end

  (* Command constructor module *)
  module Cmd = struct
    let query ?fc:(_ = ghost) ~n ~b ~d q = QueryCmd_ (n, b, d, q)
    let query_tabled ?fc:(_ = ghost) ~n ~b ~d q = QueryTabledCmd_ (n, b, d, q)
    let adhoc_query ?fc:(_ = ghost) q = AdhocQueryCmd_ q
    let unique ?fc:(_ = ghost) tm = UniqueCmd_ tm
    let mode ?fc:(_ = ghost) md = ModeCmd_ md
    let define ?fc:(_ = ghost) d = DefineCmd_ d
    let decl_cmd ?fc:(_ = ghost) tm = DeclCmd_ tm
    let inline ?fc:(_ = ghost) id tm = InlineCmd_ (id, tm)
    let symbol ?fc:(_ = ghost) id1 id2 = SymbolCmd_ (id1, id2)
    let freeze ?fc:(_ = ghost) ids = FreezeCmd_ ids
    let thaw ?fc:(_ = ghost) ids = ThawCmd_ ids
    let sort ?fc:(_ = ghost) ids decls = SortCmd_ (ids, decls)
    let term ?fc:(_ = ghost) d = TermCmd_ d
    let block ?fc:(_ = ghost) id items = BlockCmd_ (id, items)
    let union ?fc:(_ = ghost) id ids = UnionCmd_ (id, ids)
    let worlds ?fc:(_ = ghost) ids tms = WorldsCmd_ (ids, tms)
    let deterministic ?fc:(_ = ghost) ids = DeterministicCmd_ ids
    let eval ?fc:(_ = ghost) cmds = EvalCmd_ cmds
    let prec ?fc:(_ = ghost) fix n ids = PrecCmd_ (fix, n, ids)
    let solve ?fc:(_ = ghost) s = SolveCmd_ s
    let stop ?fc:(_ = ghost) () = StopCmd_

    module Repl = struct
      let quit ?fc:(_ = ghost) () = QuitCmd_
      let help ?fc:(_ = ghost) t = HelpCmd_ t
      let get ?fc:(_ = ghost) s = GetCmd_ s
      let set ?fc:(_ = ghost) s v = SetCmd_ (s, v)
      let version ?fc:(_ = ghost) () = VersionCmd_
    end

    let total ?fc:(_ = ghost) intros body = TotalCmd_ (intros, body)
    let terminates ?fc:(_ = ghost) intros body = TerminatesCmd_ (intros, body)
    let covers ?fc:(_ = ghost) md = CoversCmd_ md
    let name ?fc:(_ = ghost) id = NameCmd_ id
    let reduces ?fc:(_ = ghost) pred body = ReducesCmd_ (pred, body)
  end

  module Fixity = struct
    let left = Left_
    let right = Right_
    let prefix = Prefix_
    let postfix = Postfix_
    let middle = Middle_
    let none = FNone_
  end

  module BlockItem = struct
    let some d = BlockSome_ d
    let pi d = BlockPi_ d
  end

  module Thm = struct
    type nonrec order = order =
      | Varg_ of loc * string list
      | Lex_ of loc * order list
      | Simul_ of loc * order list

    let varg r names = Varg_ (r, names)
    let lex r orders = Lex_ (r, orders)
    let simul r orders = Simul_ (r, orders)

    type callpats = (string * string option list * loc) list

    let callpats callpats = callpats

    type tdecl = order * callpats

    let tdecl order callpats = (order, callpats)

    type predicate = string * loc

    let predicate s l = (s, l)

    type rdecl = predicate * order * order * callpats

    let rdecl predicate order1 order2 callpats =
      (predicate, order1, order2, callpats)

    type tableddecl = string * loc

    let tableddecl a b = (a, b)

    type keepTabledecl = string * loc

    let keepTabledecl a b = (a, b)

    type prove = int * tdecl

    let prove a b = (a, b)

    type establish = int * tdecl

    let establish a b = (a, b)

    type assert_ = callpats

    let assert_ assert__ = assert__

    type decs = decl list

    type theorem =
      | Top_
      | Exists_ of decs * theorem
      | Forall_ of decs * theorem
      | ForallStar_ of decs * theorem
      | ForallG_ of (decs * decs) list * theorem

    type theoremdec = string * theorem

    let null = []
    let decl decs decl = decs @ [ decl ]
    let top = Top_
    let exists decs theorem = Exists_ (decs, theorem)
    let forall decs theorem = Forall_ (decs, theorem)
    let forallStar decs theorem = ForallStar_ (decs, theorem)
    let forallG decs theorem = ForallG_ (decs, theorem)
    let dec (name, theorem) = (name, theorem)

    type wdecl = (string list * string) list * callpats

    let wdecl a b = (a, b)
  end

  open Lens

  module View :
    LENS.VIEW
      with type loc = loc
       and type qid_form = qid_form
       and type internal_tag = internal_tag
       and type Loc.t = loc
       and module Paths = Paths
       and type Term.t = term
       and type Decl.t = decl
       and type ConDec.t = conDec
       and type Mode.t = mode
       and type Mode.Term.t = modeTerm
       and type Mode.Dec.t = modeDec
       and type Struct.StrExp.t = strexp
       and type Struct.Inst.t = inst
       and type Struct.SigExp.t = sigexp
       and type Struct.SigDef.t = sigdef
       and type Struct.StructDec.t = structDec
       and type Query.t = query
       and type Solve.t = solve
       and type Define.t = define
       and type Fixity.t = fixity
       and type BlockItem.t = block_item
       and type Cmd.t = cmd = struct
    module Paths = Paths

    exception Lacking
    (** Module of paths and regions, which we allow to be shared *)

    type nonrec loc = loc
    (** Source Loc.tation carried by CST nodes. *)

    type name = string
    (** Unqualified identifier. *)

    type namespace = string list
    (** Qualified namespace path. *)

    type symbol = namespace * name
    (** Qualified symbol as [(namespace, name)]. *)

    type nonrec qid_form = qid_form =
      | Val
      | Abs
          (** Distinguishes [%val NAME] (shadow-aware lookup) from [%abs NAME]
              (toplevel-first lookup, falling back to shadow-aware). *)

    type nonrec internal_tag = internal_tag =
      | Kind_tag
      | Subst_tag
      | Shift_tag of int
      | Undef_tag
      | Proj_tag of string
      | Cutoff_tag
      | Elided_tag
      | Opaque_tag of string

    (** Create a Loc.tation from start and end lexer positions. *)
    let mk_loc = mk_loc

    (** Convert a source Loc.tation to a Paths region. *)
    let loc_to_region = loc_to_region

    (** Synthetic Loc.tation used for generated nodes. *)
    let ghost : loc = ghost

    module Loc = struct
      type t = loc
      type u = Loc of Fpath.t option * int * int | Ghost

      let view (x : t) : u =
        let path_opt = None in
        Loc (path_opt, x.start_pos, x.end_pos)

      let review (y : u) : t =
        match y with
        | Loc (path_opt, start_pos, end_pos) -> { start_pos; end_pos }
        | Ghost -> ghost

      let ( !> ) = view
      let ( !< ) = review
    end

    let ghost' : Loc.t = ghost

    module Term = struct
      type t = term

      type u =
        | Lowercase of Loc.t * symbol
        | Uppercase of Loc.t * symbol
        | Qualified of Loc.t * symbol * qid_form
        | Text of Loc.t * string
        | ExistVar of Loc.t * string
        | FreeVar of Loc.t * string
        | Pi of Loc.t * decl list * t
        | Lam of Loc.t * decl list * t
        | App of Loc.t * t * t list
        | HasType of Loc.t * t * t
        | Omitted of Loc.t
        | Typ of Loc.t
        | Arrow of Loc.t * t * t
        | BackArrow of Loc.t * t * t
        | Foreign of Loc.t * t
        | Internal of Loc.t * internal_tag * t list
        | MacroParam of Loc.t * int option * int
        | Local of Loc.t * namespace * t

      let view (x : t) : u =
        let rec collect_pis = function
          | Pi_ (_, d, body) ->
              let ds, b = collect_pis body in
              (d :: ds, b)
          | body -> ([], body)
        in
        let rec collect_lams = function
          | Lam_ (_, d, body) ->
              let ds, b = collect_lams body in
              (d :: ds, b)
          | body -> ([], body)
        in
        let rec collect_apps acc = function
          | App_ (_, f, arg) -> collect_apps (arg :: acc) f
          | head -> (head, acc)
        in
        match x with
        | Lcid_ (ns, name, loc) -> Lowercase (loc, (ns, name))
        | Ucid_ (ns, name, loc) -> Uppercase (loc, (ns, name))
        | Quid_ (ns, name, form, loc) -> Qualified (loc, (ns, name), form)
        | Scon_ (str, loc) -> Text (loc, str)
        | Evar_ (name, loc) -> ExistVar (loc, name)
        | Fvar_ (name, loc) -> FreeVar (loc, name)
        | Pi_ (loc, _, _) ->
            let decls, body = collect_pis x in
            Pi (loc, decls, body)
        | Lam_ (loc, _, _) ->
            let decls, body = collect_lams x in
            Lam (loc, decls, body)
        | App_ (loc, _, _) ->
            let head, args = collect_apps [] x in
            App (loc, head, args)
        | Hastype_ (loc, tm, ty) -> HasType (loc, tm, ty)
        | Omitted_ loc -> Omitted loc
        | Typ_ loc -> Typ loc
        | Arrow_ (loc, a, b) -> Arrow (loc, a, b)
        | Local_ (loc, ns, tm) -> Local (loc, ns, tm)
        | MacroParam_ (loc, lvl, n) -> MacroParam (loc, lvl, n)
        | Foreign_ (loc, tm) -> Foreign (loc, tm)
        | Internal_ (loc, tag, tms) -> Internal (loc, tag, tms)

      let review (y : u) : t =
        let rec fold_right f lst acc =
          match lst with [] -> acc | x :: xs -> f x (fold_right f xs acc)
        in
        let rec fold_left f acc = function
          | [] -> acc
          | x :: xs -> fold_left f (f acc x) xs
        in
        match y with
        | Lowercase (loc, (ns, name)) -> Lcid_ (ns, name, loc)
        | Uppercase (loc, (ns, name)) -> Ucid_ (ns, name, loc)
        | Qualified (loc, (ns, name), form) -> Quid_ (ns, name, form, loc)
        | Text (loc, str) -> Scon_ (str, loc)
        | ExistVar (loc, name) -> Evar_ (name, loc)
        | FreeVar (loc, name) -> Fvar_ (name, loc)
        | Pi (loc, decls, body) -> (
            match decls with
            | [] -> body
            | first :: rest ->
                let inner =
                  fold_right (fun d acc -> Pi_ (ghost, d, acc)) rest body
                in
                Pi_ (loc, first, inner))
        | Lam (loc, decls, body) -> (
            match decls with
            | [] -> body
            | first :: rest ->
                let inner =
                  fold_right (fun d acc -> Lam_ (ghost, d, acc)) rest body
                in
                Lam_ (loc, first, inner))
        | App (loc, head, args) -> (
            match List.rev args with
            | [] -> head
            | last :: rev_rest ->
                let inner =
                  fold_left
                    (fun acc arg -> App_ (ghost, acc, arg))
                    head (List.rev rev_rest)
                in
                App_ (loc, inner, last))
        | HasType (loc, tm, ty) -> Hastype_ (loc, tm, ty)
        | Omitted loc -> Omitted_ loc
        | Typ loc -> Typ_ loc
        | Arrow (loc, a, b) -> Arrow_ (loc, a, b)
        | BackArrow (loc, a, b) -> Arrow_ (loc, b, a)
        | Foreign (loc, tm) -> Foreign_ (loc, tm)
        | Internal (loc, tag, tms) -> Internal_ (loc, tag, tms)
        | Local (loc, ns, tm) -> Local_ (loc, ns, tm)
        | MacroParam (loc, lvl, n) -> MacroParam_ (loc, lvl, n)

      let ( !> ) = view
      let ( !< ) = review
    end

    module Decl = struct
      type t = decl

      type u =
        | Decl1 of Loc.t * string option list * term * term
        | Decl0 of Loc.t * string option list * term

      let view (x : t) : u =
        match x with
        | Dec_ (names, Omitted_ loc, dloc) -> Decl0 (dloc, names, Omitted_ loc)
        | Dec_ (names, typ, dloc) -> Decl1 (dloc, names, typ, Omitted_ ghost)

      let review (y : u) : t =
        match y with
        | Decl1 (loc, names, typ, _) -> Dec_ (names, typ, loc)
        | Decl0 (loc, names, typ) -> Dec_ (names, typ, loc)

      let ( !> ) = view
      let ( !< ) = review
    end

    (** Top-level declaration constructors. *)
    module ConDec = struct
      type t = conDec

      type u =
        | ConstantDecl of Loc.t * Decl.t
        | BlockDecl of Loc.t * string * Decl.t list * Decl.t list
        | BlockDef of Loc.t * string * symbol list
        | ConstantDef of Loc.t * string * Term.t * Term.t option

      let view (x : t) : u =
        match x with
        | ConstantDecl_ d -> ConstantDecl (ghost, d)
        | BlockDecl_ (n, ds1, ds2) -> BlockDecl (ghost, n, ds1, ds2)
        | BlockDef_ (n, syms) -> BlockDef (ghost, n, syms)
        | ConstantDef_ (n, tm, opt) -> ConstantDef (ghost, n, tm, opt)

      let review (y : u) : t =
        match y with
        | ConstantDecl (_, d) -> ConstantDecl_ d
        | BlockDecl (_, n, ds1, ds2) -> BlockDecl_ (n, ds1, ds2)
        | BlockDef (_, n, syms) -> BlockDef_ (n, syms)
        | ConstantDef (_, n, tm, opt) -> ConstantDef_ (n, tm, opt)

      let ( !> ) = view
      let ( !< ) = review
    end

    (** Mode syntax constructors. *)
    module Mode = struct
      type t = mode

      type u =
        | Plus of Loc.t
        | Star of Loc.t
        | Minus of Loc.t
        | Minus1 of Loc.t

      let view (x : t) : u =
        match x with
        | Plus_ -> Plus ghost
        | Star_ -> Star ghost
        | Minus_ -> Minus ghost
        | Minus1_ -> Minus1 ghost

      let review (y : u) : t =
        match y with
        | Plus _ -> Plus_
        | Star _ -> Star_
        | Minus _ -> Minus_
        | Minus1 _ -> Minus1_

      let ( !> ) = view
      let ( !< ) = review

      type t_mode = t

      module Spine = struct
        type t = modeSpine

        type u =
          | ModeNil of Loc.t
          | ModeApp of Loc.t * (t_mode * string option) * t

        let view (x : t) : u =
          match x with
          | ModeSpineInternal_ [] -> ModeNil ghost
          | ModeSpineInternal_ (x :: xs) ->
              ModeApp (ghost, x, ModeSpineInternal_ xs)

        let review (y : u) : t =
          match y with
          | ModeNil _ -> ModeSpineInternal_ []
          | ModeApp (_, entry, ModeSpineInternal_ xs) ->
              ModeSpineInternal_ (entry :: xs)

        let ( !> ) = view
        let ( !< ) = review
      end

      module Term = struct
        type t = modeTerm

        type u =
          | ModeTerm of Loc.t * symbol * Spine.t
          | ModePi of Loc.t * Decl.t * t * t

        let view (x : t) : u =
          match x with
          | ModeTermRoot_ tm ->
              let rec extract_head = function
                | Quid_ (ns, n, _, _) -> (ns, n)
                | Lcid_ (ns, n, _) -> ([], n)
                | App_ (_, f, _) -> extract_head f
                | _ -> raise Lacking
              in
              ModeTerm (ghost, extract_head tm, ModeSpineInternal_ [])
          | ModeTermPi_ (_, d, body) -> ModePi (ghost, d, body, body)

        let review (y : u) : t =
          let g = { start_pos = 0; end_pos = 0 } in
          match y with
          | ModeTerm (_, (ns, n), _) -> ModeTermRoot_ (Quid_ (ns, n, Val, g))
          | ModePi (_, d, body, _) -> ModeTermPi_ (Plus_, d, body)

        let ( !> ) = view
        let ( !< ) = review
      end

      module Dec = struct
        type t = modeDec
        type u = ModeDec of Loc.t * (t_mode * string option) list * Term.t

        let view (x : t) : u =
          let rec decompose = function
            | ModeTermPi_ (m, Dec_ (names, _, _), body) ->
                let n = match names with n :: _ -> n | [] -> None in
                let spine, root = decompose body in
                ((m, n) :: spine, root)
            | root -> ([], root)
          in
          match x with
          | ModeDec_ mt ->
              let spine, root = decompose mt in
              ModeDec (ghost, spine, root)

        let review (y : u) : t =
          let g = { start_pos = 0; end_pos = 0 } in
          match y with
          | ModeDec (_, spine, root) ->
              let rec build = function
                | [] -> root
                | (m, n) :: rest ->
                    ModeTermPi_ (m, Dec_ ([ n ], Omitted_ g, g), build rest)
              in
              ModeDec_ (build spine)

        let ( !> ) = view
        let ( !< ) = review
      end
    end

    (** Module/signature syntax constructors. *)
    module Struct = struct
      module StrExp = struct
        type t = strexp
        type u = StrExp of Loc.t * symbol

        let view (x : t) : u = match x with StrExp_ sym -> StrExp (ghost, sym)
        let review (y : u) : t = match y with StrExp (_, sym) -> StrExp_ sym
        let ( !> ) = view
        let ( !< ) = review
      end

      module Inst = struct
        type t = inst

        type u =
          | ConInst of Loc.t * symbol * Loc.t * Term.t
          | StrInst of Loc.t * symbol * Loc.t * StrExp.t

        let view (x : t) : u =
          match x with
          | ConInst_ (sym, _, tm) -> ConInst (ghost, sym, ghost, tm)
          | StrInst_ (sym, _, se) -> StrInst (ghost, sym, ghost, se)

        let review (y : u) : t =
          let g = { start_pos = 0; end_pos = 0 } in
          match y with
          | ConInst (_, sym, _, tm) -> ConInst_ (sym, g, tm)
          | StrInst (_, sym, _, se) -> StrInst_ (sym, g, se)

        let ( !> ) = view
        let ( !< ) = review
      end

      module SigExp = struct
        type t = sigexp

        type u =
          | Thesig of Loc.t
          | SigId of Loc.t * string
          | WhereSig of Loc.t * t * Inst.t list

        let view (x : t) : u =
          match x with
          | TheSig_ -> Thesig ghost
          | SigId_ str -> SigId (ghost, str)
          | WhereSig_ (se, insts) -> WhereSig (ghost, se, insts)

        let review (y : u) : t =
          match y with
          | Thesig _ -> TheSig_
          | SigId (_, str) -> SigId_ str
          | WhereSig (_, se, insts) -> WhereSig_ (se, insts)

        let ( !> ) = view
        let ( !< ) = review
      end

      module SigDef = struct
        type t = sigdef
        type u = SigDef of Loc.t * string option * SigExp.t

        let view (x : t) : u =
          match x with SigDef_ (n, se) -> SigDef (ghost, n, se)

        let review (y : u) : t =
          match y with SigDef (_, n, se) -> SigDef_ (n, se)

        let ( !> ) = view
        let ( !< ) = review
      end

      module StructDec = struct
        type t = structDec

        type u =
          | StructDecl of Loc.t * string option * SigExp.t
          | StructDef of Loc.t * string option * StrExp.t

        let view (x : t) : u =
          match x with
          | StructDecl_ (n, se) -> StructDecl (ghost, n, se)
          | StructDef_ (n, se) -> StructDef (ghost, n, se)

        let review (y : u) : t =
          match y with
          | StructDecl (_, n, se) -> StructDecl_ (n, se)
          | StructDef (_, n, se) -> StructDef_ (n, se)

        let ( !> ) = view
        let ( !< ) = review
      end
    end

    module Query = struct
      type t = query
      type u = Query of Loc.t * string option * Term.t

      let view (x : t) : u =
        match x with Query_ (n, tm) -> Query (ghost, n, tm)

      let review (y : u) : t = match y with Query (_, n, tm) -> Query_ (n, tm)
      let ( !> ) = view
      let ( !< ) = review
    end

    module Define = struct
      type t = define
      type u = Define of Loc.t * string option * Term.t * Term.t option

      let view (x : t) : u =
        match x with
        | Define_ (n, tm1, tm2_opt) -> Define (ghost, n, tm1, tm2_opt)

      let review (y : u) : t =
        match y with Define (_, n, tm1, tm2_opt) -> Define_ (n, tm1, tm2_opt)

      let ( !> ) = view
      let ( !< ) = review
    end

    module Solve = struct
      type t = solve
      type u = Solve of Loc.t * string option * Term.t

      let view (x : t) : u =
        match x with Solve_ (n, tm) -> Solve (ghost, n, tm)

      let review (y : u) : t = match y with Solve (_, n, tm) -> Solve_ (n, tm)
      let ( !> ) = view
      let ( !< ) = review
    end

    module Fixity = struct
      type t = fixity

      type u =
        | Left of Loc.t
        | Right of Loc.t
        | Prefix of Loc.t
        | Postfix of Loc.t
        | Middle of Loc.t
        | None of Loc.t

      let view (x : t) : u =
        match x with
        | Left_ -> Left ghost
        | Right_ -> Right ghost
        | Prefix_ -> Prefix ghost
        | Postfix_ -> Postfix ghost
        | Middle_ -> Middle ghost
        | FNone_ -> None ghost

      let review (y : u) : t =
        match y with
        | Left _ -> Left_
        | Right _ -> Right_
        | Prefix _ -> Prefix_
        | Postfix _ -> Postfix_
        | Middle _ -> Middle_
        | None _ -> FNone_

      let ( !> ) = view
      let ( !< ) = review
    end

    module BlockItem = struct
      type t = block_item
      type u = Any of Loc.t * Decl.t | All of Loc.t * Decl.t

      let view (x : t) : u =
        match x with
        | BlockSome_ d -> Any (ghost, d)
        | BlockPi_ d -> All (ghost, d)

      let review (y : u) : t =
        match y with Any (_, d) -> BlockSome_ d | All (_, d) -> BlockPi_ d

      let ( !> ) = view
      let ( !< ) = review
    end

    module Cmd = struct
      type t = cmd

      type u =
        | Query of Loc.t * int option * int option * int option * Query.t
        | QueryTabled of Loc.t * int option * int option * int option * Query.t
        | AdhocQuery of Loc.t * Query.t
        | Unique of Loc.t * Term.t
        | Mode of Loc.t * Mode.Dec.t
        | Define of Loc.t * Define.t
        | DeclCmd of Loc.t * Term.t
        | Inline of Loc.t * string * Term.t
        | Symbol of Loc.t * string * string
        | Freeze of Loc.t * string list
        | Thaw of Loc.t * string list
        | Sort of Loc.t * string list * Decl.t list
        | Term of Loc.t * Decl.t
        | Block of Loc.t * string * BlockItem.t list
        | Union of Loc.t * string * string list
        | Worlds of Loc.t * string list * Term.t list
        | Deterministic of Loc.t * string list
        | Eval of Loc.t * t list
        | Prec of Loc.t * Fixity.t * int * string list
        | Solve of Loc.t * Solve.t
        | Stop of Loc.t * unit
        | ReplQuit of Loc.t * unit
        | ReplHelp of Loc.t * string option
        | ReplGet of Loc.t * string
        | ReplSet of Loc.t * string * string
        | ReplVersion of Loc.t * unit
        | Total of Loc.t * Thm.order list * Term.t list
        | Terminates of Loc.t * Thm.order list * Term.t list
        | Covers of Loc.t * Mode.Dec.t
        | Name of Loc.t * string
        | Prose of Loc.t * string
        | Reduces of Loc.t * string * Term.t list
        | Macro of Loc.t * int * string * t
            (** Defines a macro, taking its location, number of params, name,
                and the body *)
        | Seq of Loc.t * item list
            (** A sequence of commands, for use withthe module system*)
        | Require of Loc.t * string list
            (** Ensure that the given path is loaded *)
        | Open of Loc.t * string list  (** Open a scope into the scope *)
        | Scope of Loc.t * string * t  (** Enter into a new scope *)
        | Use of Loc.t * string list * Term.t list  (** Apply a macro *)

      and item = Outer of string | Cmd of t

      let view (x : t) : u =
        match x with
        | QueryCmd_ (n, b, d, q) -> Query (ghost, n, b, d, q)
        | QueryTabledCmd_ (n, b, d, q) -> QueryTabled (ghost, n, b, d, q)
        | AdhocQueryCmd_ q -> AdhocQuery (ghost, q)
        | UniqueCmd_ tm -> Unique (ghost, tm)
        | ModeCmd_ md -> Mode (ghost, md)
        | DefineCmd_ d -> Define (ghost, d)
        | DeclCmd_ tm -> DeclCmd (ghost, tm)
        | InlineCmd_ (id, tm) -> Inline (ghost, id, tm)
        | SymbolCmd_ (id1, id2) -> Symbol (ghost, id1, id2)
        | FreezeCmd_ ids -> Freeze (ghost, ids)
        | ThawCmd_ ids -> Thaw (ghost, ids)
        | SortCmd_ (ids, decls) -> Sort (ghost, ids, decls)
        | TermCmd_ d -> Term (ghost, d)
        | BlockCmd_ (id, items) -> Block (ghost, id, items)
        | UnionCmd_ (id, ids) -> Union (ghost, id, ids)
        | WorldsCmd_ (ids, tm) -> Worlds (ghost, ids, tm)
        | DeterministicCmd_ ids -> Deterministic (ghost, ids)
        | EvalCmd_ cmds -> Eval (ghost, cmds)
        | PrecCmd_ (fix, n, ids) -> Prec (ghost, fix, n, ids)
        | SolveCmd_ s -> Solve (ghost, s)
        | StopCmd_ -> Stop (ghost, ())
        | QuitCmd_ -> ReplQuit (ghost, ())
        | HelpCmd_ t -> ReplHelp (ghost, t)
        | GetCmd_ s -> ReplGet (ghost, s)
        | SetCmd_ (s, v) -> ReplSet (ghost, s, v)
        | VersionCmd_ -> ReplVersion (ghost, ())
        | TotalCmd_ (orders, terms) -> Total (ghost, orders, terms)
        | TerminatesCmd_ (orders, terms) -> Terminates (ghost, orders, terms)
        | CoversCmd_ md -> Covers (ghost, md)
        | NameCmd_ id -> Name (ghost, id)
        | ProseCmd_ id -> Prose (ghost, id)
        | ReducesCmd_ (pred, body) -> Reduces (ghost, pred, body)
        | Open_ ids -> Open (ghost, ids)
        | Scope_ (id, cmd) -> Scope (ghost, id, cmd)
        | Use_ (ids, tms) -> Use (ghost, ids, tms)
        | Macro_ (n, id, cmd) -> Macro (ghost, n, id, cmd)
        | Seq_ _ -> failwith "Cmd.view: Seq_ is not representable in view"
        | Require_ ids -> Require (ghost, ids)

      let review (y : u) : t =
        match y with
        | Query (loc, n, b, d, q) -> QueryCmd_ (n, b, d, q)
        | QueryTabled (loc, n, b, d, q) -> QueryTabledCmd_ (n, b, d, q)
        | AdhocQuery (loc, q) -> AdhocQueryCmd_ q
        | Unique (loc, tm) -> UniqueCmd_ tm
        | Mode (loc, md) -> ModeCmd_ md
        | Define (loc, d) -> DefineCmd_ d
        | DeclCmd (loc, tm) -> DeclCmd_ tm
        | Inline (loc, id, tm) -> InlineCmd_ (id, tm)
        | Symbol (loc, id1, id2) -> SymbolCmd_ (id1, id2)
        | Freeze (loc, ids) -> FreezeCmd_ ids
        | Thaw (loc, ids) -> ThawCmd_ ids
        | Sort (_, ids, decls) -> SortCmd_ (ids, decls)
        | Term (loc, d) -> TermCmd_ d
        | Block (loc, id, items) -> BlockCmd_ (id, items)
        | Union (loc, id, ids) -> UnionCmd_ (id, ids)
        | Worlds (loc, ids, tm) -> WorldsCmd_ (ids, tm)
        | Deterministic (loc, ids) -> DeterministicCmd_ ids
        | Eval (loc, cmds) -> EvalCmd_ cmds
        | Prec (loc, fix, n, ids) -> PrecCmd_ (fix, n, ids)
        | Solve (loc, s) -> SolveCmd_ s
        | Stop (loc, ()) -> StopCmd_
        | ReplQuit (loc, ()) -> QuitCmd_
        | ReplHelp (loc, t) -> HelpCmd_ t
        | ReplGet (loc, s) -> GetCmd_ s
        | ReplSet (loc, s, v) -> SetCmd_ (s, v)
        | ReplVersion (loc, ()) -> VersionCmd_
        | Total (_, orders, terms) -> TotalCmd_ (orders, terms)
        | Terminates (_, orders, terms) -> TerminatesCmd_ (orders, terms)
        | Covers (_, md) -> CoversCmd_ md
        | Name (_, id) -> NameCmd_ id
        | Prose (_, id) -> ProseCmd_ id
        | Reduces (_, pred, body) -> ReducesCmd_ (pred, body)
        | Open (_, ids) -> Open_ ids
        | Scope (_, id, cmd) -> Scope_ (id, cmd)
        | Use (_, ids, tms) -> Use_ (ids, tms)
        | Macro (_, n, id, cmd) -> Macro_ (n, id, cmd)
        | Seq _ -> failwith "Cmd.review: Seq is not representable in review"
        | Require (_, ids) -> Require_ ids

      let ( !> ) = view
      let ( !< ) = review
    end

    module Thm = struct
      type t
      type u = |

      (* Aliases to capture Make_Cst.Thm types before inner 'module Thm' shadows the name *)
      type concrete_theorem = Thm.theorem
      type concrete_theoremdec = Thm.theoremdec
      type concrete_wdecl = Thm.wdecl

      module Order = struct
        type t = Thm.order

        type u =
          | Varg of Loc.t * string list
          | Lex of Loc.t * t list
          | Simul of Loc.t * t list

        let view (x : t) : u =
          match x with
          | Thm.Varg_ (l, names) -> Varg (l, names)
          | Thm.Lex_ (l, orders) -> Lex (l, orders)
          | Thm.Simul_ (l, orders) -> Simul (l, orders)

        let review (y : u) : t =
          match y with
          | Varg (l, names) -> Thm.Varg_ (l, names)
          | Lex (l, orders) -> Thm.Lex_ (l, orders)
          | Simul (l, orders) -> Thm.Simul_ (l, orders)

        let ( !> ) = view
        let ( !< ) = review
      end

      module CallPats = struct
        type t = Thm.callpats
        type u = CallPats of (string * string option list * Loc.t) list

        let view (x : t) : u = CallPats x
        let review (y : u) : t = match y with CallPats cp -> cp
        let ( !> ) = view
        let ( !< ) = review
      end

      module TDecl = struct
        type t = Thm.tdecl
        type u = TDecl of Order.t * CallPats.t

        let view (x : t) : u =
          let o, cp = x in
          TDecl (o, cp)

        let review (y : u) : t = match y with TDecl (o, cp) -> (o, cp)
        let ( !> ) = view
        let ( !< ) = review
      end

      module Predicate = struct
        type t = Thm.predicate
        type u = Predicate of string * Loc.t

        let view (x : t) : u =
          let s, l = x in
          Predicate (s, l)

        let review (y : u) : t = match y with Predicate (s, l) -> (s, l)
        let ( !> ) = view
        let ( !< ) = review
      end

      module RDecl = struct
        type t = Thm.rdecl
        type u = RDecl of Predicate.t * Order.t * Order.t * CallPats.t

        let view (x : t) : u =
          let p, o1, o2, cp = x in
          RDecl (p, o1, o2, cp)

        let review (y : u) : t =
          match y with RDecl (p, o1, o2, cp) -> (p, o1, o2, cp)

        let ( !> ) = view
        let ( !< ) = review
      end

      module TabledDecl = struct
        type t = Thm.tableddecl
        type u = TabledDecl of string * Loc.t

        let view (x : t) : u =
          let s, l = x in
          TabledDecl (s, l)

        let review (y : u) : t = match y with TabledDecl (s, l) -> (s, l)
        let ( !> ) = view
        let ( !< ) = review
      end

      module KeepTableDecl = struct
        type t = Thm.keepTabledecl
        type u = KeepTableDecl of string * Loc.t

        let view (x : t) : u =
          let s, l = x in
          KeepTableDecl (s, l)

        let review (y : u) : t = match y with KeepTableDecl (s, l) -> (s, l)
        let ( !> ) = view
        let ( !< ) = review
      end

      module Prove = struct
        type t = Thm.prove
        type u = Prove of int * TDecl.t

        let view (x : t) : u =
          let n, td = x in
          Prove (n, td)

        let review (y : u) : t = match y with Prove (n, td) -> (n, td)
        let ( !> ) = view
        let ( !< ) = review
      end

      module Establish = struct
        type t = Thm.establish
        type u = Establish of int * TDecl.t

        let view (x : t) : u =
          let n, td = x in
          Establish (n, td)

        let review (y : u) : t = match y with Establish (n, td) -> (n, td)
        let ( !> ) = view
        let ( !< ) = review
      end

      module Assert = struct
        type t = Thm.assert_
        type u = Assert of CallPats.t

        let view (x : t) : u = Assert x
        let review (y : u) : t = match y with Assert cp -> cp
        let ( !> ) = view
        let ( !< ) = review
      end

      module Decs = struct
        type t = Thm.decs
        type u = DecsNil of Loc.t | DecsList of t * Decl.t list

        let view (x : t) : u =
          match x with
          | [] -> DecsNil ghost
          | d :: rest -> DecsList (rest, [ d ])

        let review (y : u) : t =
          match y with
          | DecsNil _ -> []
          | DecsList (rest, decls) -> rest @ decls

        let ( !> ) = view
        let ( !< ) = review
      end

      module Thm = struct
        type t = concrete_theorem

        type u =
          | Top of Loc.t
          | Exists of Loc.t * Decs.t * t
          | Forall of Loc.t * Decs.t * t
          | ForallStar of Loc.t * Decs.t * t
          | ForallG of Loc.t * (Decs.t * Decs.t) list * t

        let view (x : t) : u =
          match x with
          | Thm.Top_ -> Top ghost
          | Thm.Exists_ (ds, body) -> Exists (ghost, ds, body)
          | Thm.Forall_ (ds, body) -> Forall (ghost, ds, body)
          | Thm.ForallStar_ (ds, body) -> ForallStar (ghost, ds, body)
          | Thm.ForallG_ (pairs, body) -> ForallG (ghost, pairs, body)

        let review (y : u) : t =
          match y with
          | Top _ -> Thm.Top_
          | Exists (_, ds, body) -> Thm.Exists_ (ds, body)
          | Forall (_, ds, body) -> Thm.Forall_ (ds, body)
          | ForallStar (_, ds, body) -> Thm.ForallStar_ (ds, body)
          | ForallG (_, pairs, body) -> Thm.ForallG_ (pairs, body)

        let ( !> ) = view
        let ( !< ) = review
      end

      let view (x : t) : u = assert false
      let review (y : u) : t = assert false
      let ( !> ) = view
      let ( !< ) = review

      module ThmDec = struct
        type t = concrete_theoremdec
        type u = ThmDec of string * Thm.t

        let view (x : t) : u =
          let name, thm = x in
          ThmDec (name, thm)

        let review (y : u) : t = match y with ThmDec (name, thm) -> (name, thm)
        let ( !> ) = view
        let ( !< ) = review
      end

      module WDecl = struct
        type t = concrete_wdecl
        type u = WDecl of (string list * string) list * CallPats.t

        let view (x : t) : u =
          let pairs, cp = x in
          WDecl (pairs, cp)

        let review (y : u) : t = match y with WDecl (pairs, cp) -> (pairs, cp)
        let ( !> ) = view
        let ( !< ) = review
      end
    end
  end
end

module Cst : CST = Make_Cst (Paths.Paths_)
