(** The core term resugarer.

    Ported from the term-formatting half of [Print.Print_], with every
    typographic decision removed. What is left is the semantic content that was
    tangled up with layout there: normalisation, naming, implicit-argument
    elision, and eta-expansion.

    The one structural difference from the original is over-application. Where
    [Print_.opargsExplicit] parenthesises the saturated prefix and applies the
    rest to it, this emits a single flat application node. That is what makes
    output round-trip: [Modern.infix_op] builds [App (App (op, [a]), [b])] and
    [Cst.View.Term.view] n-arises that straight back into one [App], so the flat
    node is exactly what re-parsing the printed form yields. *)

module I = Intsyn.IntSyn
module Whnf = Intsyn.Lambda_.Whnf
module N = Names.Names_
module FX = Names.Names_.Fixity

module Make (Cst : Cst.CST) = struct
  module V = Cst.View
  module T = Cst.View.Term

  let g_loc : Cst.loc = V.Loc.review V.Loc.Ghost
  let internal tag kids = T.review (T.Internal (g_loc, tag, kids))
  let lower sym = T.review (T.Lowercase (g_loc, sym))
  let upper name = T.review (T.Uppercase (g_loc, ([], name)))
  let omitted () = T.review (T.Omitted g_loc)

  let dec_of names ty =
    V.Decl.review (V.Decl.Decl1 (g_loc, names, ty, omitted ()))

  (* ---------------------------------------------------------------- *)
  (* Spine arithmetic, ported unchanged from [Print_].                  *)
  (* ---------------------------------------------------------------- *)

  type arg_status = Too_few | Exact of I.spine | Too_many of I.spine * I.spine

  let sclo' status s =
    match status with
    | Too_few -> Too_few
    | Exact s_ -> Exact (I.SClo (s_, s))
    | Too_many (s_, s') -> Too_many (I.SClo (s_, s), I.SClo (s', s))

  let sclo'' status s =
    match status with
    | Too_few -> Too_few
    | Exact s -> Exact s
    | Too_many (s_, s') -> Too_many (s_, I.SClo (s', s))

  (* [drop_imp i s n] drops [i] leading implicit arguments from [s] and then
     reports whether exactly [n] remain. *)
  let rec drop_imp (i, s_, n) =
    match (i, s_, n) with
    | 0, s, 0 -> Exact s
    | 0, s_, n ->
        let rec check = function
          | I.Nil, 0 -> Exact s_
          | I.Nil, _ -> Too_few
          | (I.App _ as s'), 0 -> Too_many (s_, s')
          | I.App (_, s'), k -> check (s', k - 1)
          | I.SClo (s', s), k -> sclo'' (check (s', k)) s
        in
        check (s_, n)
    | i, I.App (_, s), n -> drop_imp (i - 1, s, n)
    | i, I.SClo (s_, s), n -> sclo' (drop_imp (i, s_, n)) s
    | _, I.Nil, _ -> Too_few

  let rec is_nil = function
    | I.Nil -> true
    | I.App _ -> false
    | I.SClo (s, _) -> is_nil s

  (* Turn a substitution into the spine that applying it corresponds to, so an
     existential variable's substitution can be shown as its arguments. *)
  let sub_to_spine (depth, s) =
    let rec go (a, s_) = match a with
      | I.Shift k ->
          if k < depth then go (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
          else s_
      | I.Dot (I.Idx k, s) -> go (s, I.App (I.Root (I.BVar k, I.Nil), s_))
      | I.Dot (I.Exp u, s) -> go (s, I.App (u, s_))
      | I.Dot (I.Undef, s) -> go (s, I.App (I.Root (I.BVar 0, I.Nil), s_))
      | I.Dot ((I.Block _ | I.Axp _), s) ->
          go (s, I.App (I.Root (I.BVar 0, I.Nil), s_))
    in
    go (s, I.Nil)

  (* ---------------------------------------------------------------- *)
  (* Constant naming                                                    *)
  (* ---------------------------------------------------------------- *)

  let fixity_con = function
    | I.Const cid | I.Def cid | I.NSDef cid -> N.getFixity cid
    | _ -> FX.Nonfix

  let imp_con = function
    | I.Const cid | I.Skonst cid | I.Def cid | I.NSDef cid -> I.constImp cid
    | _ -> 0

  let arg_number = function
    | FX.Nonfix -> 0
    | FX.Infix _ -> 2
    | FX.Prefix _ | FX.Postfix _ -> 1

  (* The namespace path to fall back on when a constant's own name no longer
     reaches it -- a %scope that has closed, so its components stopped being
     bare-visible while remaining perfectly reachable as members of the
     structure.

     [None] means either that nothing is wrong (the canonical name resolves
     here) or that nothing can be done (the constant was declared at top
     level and shadowed, so there is no namespace to name it through). *)
  let const_path (opts : Options.t) cid : N.qid option =
    if opts.no_shadow then None
    else
      let qid = N.conDecQid (I.sgnLookup cid) in
      if N.constLookup qid = Some cid then None else N.constPath cid

  (* A namespaced symbol carries its own escape hatch: [Pretty] has to spell
     it [%( ns c )], which resolves [c] as a member of [ns] and never consults
     what the bare name means at the point of use. That is exactly the
     question the [%c%] marker raises and cannot answer, so supplying the path
     is the whole fix -- nothing here needs to know how it will be written. *)
  let const_sym (opts : Options.t) cid : Cst.symbol =
    let (N.Qid (ids, id)) =
      match const_path opts cid with
      | Some qid -> qid
      | None ->
          (* [constQid] decorates an unreachable name as [%c%]. That is a
             note to the reader rather than syntax, but there is nowhere
             better to put it: the constant was declared at top level and
             shadowed, so no namespace names it. *)
          if opts.no_shadow then N.conDecQid (I.sgnLookup cid)
          else N.constQid cid
    in
    if opts.show_const_path then (ids, id) else ([], id)

  let parm_name (cid, i) =
    let _, gblock = I.constBlock cid in
    let rec nth = function
      | d :: _, 1 -> d
      | _ :: l, j -> nth (l, j - 1)
      | [], _ -> I.Dec (None, I.Uni I.Type)
    in
    match nth (gblock, i) with
    | I.Dec (Some pname, _) -> pname
    | _ -> string_of_int i

  let proj_name (g, a) = match a with
    | I.Proj (I.Bidx k, i) -> (
        match I.ctxLookup g k with
        | I.BDec (Some bname, (cid, _)) -> bname ^ "_" ^ parm_name (cid, i)
        | I.BDec (None, (cid, _)) -> "_" ^ parm_name (cid, i)
        | _ -> "_" ^ string_of_int i)
    | I.Proj (I.LVar (_, _, (cid, _)), i) -> "_" ^ parm_name (cid, i)
    | I.Proj (I.Inst _, _) -> "*"
    | _ -> "*"

  (* A variable's node has to match the lexical class of its name, or the
     printer is forced to escape it as [%val] and it comes back as a constant
     reference instead of a variable. [Names] hands out uppercase names freely
     -- [decEName] names implicit binders [X], [Y], and [decLUName] names
     anonymous ones [_0] -- so the choice is made from the name itself, the
     same way [Modern.parse_id] classifies one.

     Constants are the opposite case and stay [Lowercase] unconditionally: a
     constant named [Nat] written bare {e would} re-parse as a variable, so
     there the escape is exactly what is wanted. *)
  let variable name =
    if
      String.length name > 0
      && (name.[0] = '_' || (name.[0] >= 'A' && name.[0] <= 'Z'))
    then upper name
    else lower ([], name)

  (* Existential and free variables come out as plain identifiers rather than
     as [ExistVar]/[FreeVar] nodes: those have no surface syntax, whereas an
     uppercase identifier is exactly how the parser spells a variable. *)
  let head (opts : Options.t) (g : I.dctx) (h : I.head) : Cst.term =
    match h with
    | I.BVar n -> variable (N.bvarName g n)
    | I.Const cid | I.Skonst cid | I.Def cid | I.NSDef cid ->
        lower (const_sym opts cid)
    | I.FVar (name, _, _) -> variable name
    | I.Proj _ -> internal (Cst.Proj_tag (proj_name (g, h))) []
    | I.FgnConst (_, conDec) -> lower ([], I.conDecName conDec)

  (* ---------------------------------------------------------------- *)
  (* Elision counters                                                   *)
  (* ---------------------------------------------------------------- *)

  let exceeded n = function None -> false | Some m -> n >= m
  let elide l = function None -> false | Some l' -> l > l'
  let addots l = function None -> false | Some l' -> l = l'

  (* ---------------------------------------------------------------- *)
  (* The driver                                                         *)
  (* ---------------------------------------------------------------- *)

  (* [d] is the nesting depth against [print_depth]. It counts spine arguments
     and substitution entries only, never binders -- preserve that or every
     cutoff moves. *)
  let rec exp_sub (opts : Options.t) g d (u, s) : Cst.term =
    (* Strictly before the [whnf]: an ill-typed term can make [whnf] diverge,
       and this cutoff is what stops it. *)
    if exceeded d opts.print_depth then internal Cst.Cutoff_tag []
    else exp_w opts g d (Whnf.whnf (u, s))

  and exp_w (opts : Options.t) g d (u, s) : Cst.term =
    match (u, s) with
    | I.Uni I.Type, _ -> T.review (T.Typ g_loc)
    | I.Uni I.Kind, _ -> internal Cst.Kind_tag []
    (* A maximal run of anonymous, provably non-dependent [Pi]s becomes one
       arrow chain. The context still has to be extended at every hop, or the
       codomain's indices shift. *)
    | I.Pi (((I.Dec (None, _) as d_), I.No), v2), _ when opts.arrow_sugar ->
        let hops, gf, final = arrow_hops g (I.Pi ((d_, I.No), v2), s) in
        let doms =
          List.map
            (fun (gi, (vi, si)) -> exp_sub opts gi (d + 1) (vi, si))
            hops
        in
        let cod = exp_sub opts gf (d + 1) final in
        let rec chain = function
          | [] -> cod
          | x :: rest -> T.review (T.Arrow (g_loc, x, chain rest))
        in
        chain doms
    (* [ADec] binds an anonymous approximate variable; the original prints it
       as a lambda over [_] and so does this. *)
    | I.Pi (((I.ADec _ as d_), _), v2), _ ->
        let body = exp_sub opts (I.Decl (g, d_)) d (v2, I.dot1 s) in
        T.review (T.Lam (g_loc, [ dec_of [ None ] (omitted ()) ], body))
    | I.Pi ((d_, _), v2), _ ->
        (* Name the binder before descending, or the body's [bvarName] lookups
           find an unnamed declaration. *)
        let d' = N.decLUName g d_ in
        let dec = dec_sub opts g (d', s) in
        let body = exp_sub opts (I.Decl (g, d')) d (v2, I.dot1 s) in
        T.review (T.Pi (g_loc, [ dec ], body))
    | I.Lam (d_, u), _ ->
        let d' = N.decLUName g d_ in
        let dec = dec_sub opts g (d', s) in
        let body = exp_sub opts (I.Decl (g, d')) d (u, I.dot1 s) in
        T.review (T.Lam (g_loc, [ dec ], body))
    | I.Root (h, sp), _ -> root opts g d (h, sp) s
    | (I.EVar _ as x), s -> evar opts g d x s (fun n -> n)
    | (I.AVar _ as x), s -> evar opts g d x s (fun n -> n ^ "_")
    | I.FgnExp (cs, fe), s ->
        T.review
          (T.Foreign
             ( g_loc,
               exp_sub opts g d (I.FgnExpStd.ToInternal.apply cs fe (), s)
             ))
    (* Unreachable after [whnf]; kept so the function is total rather than
       raising from inside a printer. *)
    | u, _ -> internal (Cst.Opaque_tag "%%opaque") [ leaf u ]

  and leaf _ = internal (Cst.Opaque_tag "?") []

  and evar opts g d x s decorate =
    let node = variable (decorate (N.evarName g x)) in
    if opts.implicit then T.review (T.App (g_loc, node, [ sub opts g d s ]))
    else
      let args =
        spine_sub opts g d 0 (sub_to_spine (I.ctxLength g, s), I.id)
      in
      if args = [] then node else T.review (T.App (g_loc, node, args))

  (* An explicit substitution has no surface form, so it comes out tagged. *)
  and sub opts g d s =
    let rec go l s =
      if elide l opts.print_length then [ internal Cst.Elided_tag [] ]
      else
        match s with
        | I.Shift k -> [ internal (Cst.Shift_tag k) [] ]
        | I.Dot (I.Idx k, s) -> variable (N.bvarName g k) :: go (l + 1) s
        | I.Dot (I.Exp u, s) ->
            exp_sub opts g (d + 1) (u, I.id) :: go (l + 1) s
        | I.Dot (I.Undef, s) -> internal Cst.Undef_tag [] :: go (l + 1) s
        | I.Dot (I.Axp u, s) ->
            exp_sub opts g (d + 1) (u, I.id) :: go (l + 1) s
        | I.Dot (I.Block _, s) ->
            internal (Cst.Opaque_tag "%%block") [] :: go (l + 1) s
    in
    internal Cst.Subst_tag (go 0 s)

  and root opts g d (h, sp) s : Cst.term =
    let op = head opts g h in
    let apply args =
      if args = [] then op else T.review (T.App (g_loc, op, args))
    in
    if opts.implicit && not opts.print_infix then
      apply (spine_sub opts g d 0 (sp, s))
    else if opts.implicit then
      (* [print_infix] keeps operator rendering for declared infixes while
         still showing implicit arguments. *)
      match fixity_con h with
      | FX.Infix _ -> explicit opts g d (h, sp) s op
      | _ -> apply (spine_sub opts g d 0 (sp, s))
    else explicit opts g d (h, sp) s op

  and explicit opts g d (h, sp) s op : Cst.term =
    let apply args =
      if args = [] then op else T.review (T.App (g_loc, op, args))
    in
    match drop_imp (imp_con h, sp, arg_number (fixity_con h)) with
    | Exact s' -> apply (spine_sub opts g d 0 (s', s))
    | Too_few when opts.eta_expand ->
        (* Under-applied: eta-expand so the operator reaches its arity, then
           start over on the expansion. *)
        exp_sub opts g d (Whnf.etaExpandRoot (I.Root (h, sp)), s)
    | Too_few -> apply (spine_sub opts g d 0 (sp, s))
    | Too_many (s', s'') ->
        (* One flat node, not a parenthesised saturated prefix -- see the
           header. The two denote the same term; only this one round-trips.
           The length counter carries across the join so [print_length] counts
           the arguments as the single list they are printed as. *)
        let saturated = spine_sub opts g d 0 (s', s) in
        apply (saturated @ spine_sub opts g d (List.length saturated) (s'', s))

  and spine_sub opts g d l (sp, s) : Cst.term list =
    match sp with
    | I.Nil -> []
    | I.SClo (sp, s') -> spine_sub opts g d l (sp, I.comp s' s)
    | I.App (u, sp) ->
        if elide l opts.print_length then []
        else if addots l opts.print_length then [ internal Cst.Elided_tag [] ]
        else
          exp_sub opts g (d + 1) (u, s) :: spine_sub opts g d (l + 1) (sp, s)

  (* Collect a maximal run of anonymous non-dependent [Pi]s, each paired with
     the context and substitution it must be resugared under. *)
  and arrow_hops g (u, s) =
    match Whnf.whnf (u, s) with
    | I.Pi (((I.Dec (None, v1) as d), I.No), v2), s' ->
        let hops, gf, final = arrow_hops (I.Decl (g, d)) (v2, I.dot1 s') in
        ((g, (v1, s')) :: hops, gf, final)
    | other -> ([], g, other)

  and dec_sub opts g (d, s) : Cst.decl =
    match d with
    | I.Dec (x, v) -> dec_of [ x ] (exp_sub opts g 0 (v, s))
    | I.BDec (x, (cid, t)) ->
        (* A block binder's classifier is a list of declarations, which the
           CST has no term form for; it goes out as an internal node wrapping
           the corresponding binder chain. *)
        let _, gblock = I.constBlock cid in
        let decs = dec_list_sub opts g (gblock, I.comp t s) in
        dec_of [ x ]
          (internal (Cst.Opaque_tag "%%block")
             [ T.review (T.Pi (g_loc, decs, omitted ())) ])
    | I.ADec (x, _) -> dec_of [ x ] (omitted ())
    | I.NDec x -> dec_of [ x ] (omitted ())

  (* Successive declarations scope over each other, so each one is resugared
     in the context extended by its predecessors. *)
  and dec_list_sub opts g (ds, s) : Cst.decl list =
    match ds with
    | [] -> []
    | d :: rest ->
        dec_sub opts g (d, s)
        :: dec_list_sub opts (I.Decl (g, d)) (rest, I.dot1 s)

  let exp opts g u = exp_sub opts g 0 (u, I.id)
  let spine opts g sp = spine_sub opts g 0 0 (sp, I.id)
  let dec opts g d = dec_sub opts g (d, I.id)
  let dec_list opts g ds = dec_list_sub opts g (ds, I.id)
end
