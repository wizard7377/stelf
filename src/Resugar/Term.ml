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
    | Too_many (s_, s'_) -> Too_many (I.SClo (s_, s), I.SClo (s'_, s))

  let sclo'' status s =
    match status with
    | Too_few -> Too_few
    | Exact s_ -> Exact s_
    | Too_many (s_, s'_) -> Too_many (s_, I.SClo (s'_, s))

  (* [drop_imp i s n] drops [i] leading implicit arguments from [s] and then
     reports whether exactly [n] remain. *)
  let rec drop_imp (i, s_, n) =
    match (i, s_, n) with
    | 0, s_, 0 -> Exact s_
    | 0, s_, n ->
        let rec check = function
          | I.Nil, 0 -> Exact s_
          | I.Nil, _ -> Too_few
          | (I.App _ as s'_), 0 -> Too_many (s_, s'_)
          | I.App (_, s'_), k -> check (s'_, k - 1)
          | I.SClo (s'_, s), k -> sclo'' (check (s'_, k)) s
        in
        check (s_, n)
    | i, I.App (_, s_), n -> drop_imp (i - 1, s_, n)
    | i, I.SClo (s_, s), n -> sclo' (drop_imp (i, s_, n)) s
    | _, I.Nil, _ -> Too_few

  let rec is_nil = function
    | I.Nil -> true
    | I.App _ -> false
    | I.SClo (s_, _) -> is_nil s_

  (* Turn a substitution into the spine that applying it corresponds to, so an
     existential variable's substitution can be shown as its arguments. *)
  let sub_to_spine (depth, s) =
    let rec go (a, s_) = match a with
      | I.Shift k ->
          if k < depth then go (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
          else s_
      | I.Dot (I.Idx k, s) -> go (s, I.App (I.Root (I.BVar k, I.Nil), s_))
      | I.Dot (I.Exp u_, s) -> go (s, I.App (u_, s_))
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
    let _, gblock_ = I.constBlock cid in
    let rec nth = function
      | d_ :: _, 1 -> d_
      | _ :: l_, j -> nth (l_, j - 1)
      | [], _ -> I.Dec (None, I.Uni I.Type)
    in
    match nth (gblock_, i) with
    | I.Dec (Some pname, _) -> pname
    | _ -> string_of_int i

  let proj_name = function
    | g_, I.Proj (I.Bidx k, i) -> (
        match I.ctxLookup g_ k with
        | I.BDec (Some bname, (cid, _)) -> bname ^ "_" ^ parm_name (cid, i)
        | I.BDec (None, (cid, _)) -> "_" ^ parm_name (cid, i)
        | _ -> "_" ^ string_of_int i)
    | _, I.Proj (I.LVar (_, _, (cid, _)), i) -> "_" ^ parm_name (cid, i)
    | _, I.Proj (I.Inst _, _) -> "*"
    | _, _ -> "*"

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
  let head (opts : Options.t) (g_ : I.dctx) (h_ : I.head) : Cst.term =
    match h_ with
    | I.BVar n -> variable (N.bvarName g_ n)
    | I.Const cid | I.Skonst cid | I.Def cid | I.NSDef cid ->
        lower (const_sym opts cid)
    | I.FVar (name, _, _) -> variable name
    | I.Proj _ -> internal (Cst.Proj_tag (proj_name (g_, h_))) []
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
  let rec exp_sub (opts : Options.t) g_ d (u_, s) : Cst.term =
    (* Strictly before the [whnf]: an ill-typed term can make [whnf] diverge,
       and this cutoff is what stops it. *)
    if exceeded d opts.print_depth then internal Cst.Cutoff_tag []
    else exp_w opts g_ d (Whnf.whnf (u_, s))

  and exp_w (opts : Options.t) g_ d (u_, s) : Cst.term =
    match (u_, s) with
    | I.Uni I.Type, _ -> T.review (T.Typ g_loc)
    | I.Uni I.Kind, _ -> internal Cst.Kind_tag []
    (* A maximal run of anonymous, provably non-dependent [Pi]s becomes one
       arrow chain. The context still has to be extended at every hop, or the
       codomain's indices shift. *)
    | I.Pi (((I.Dec (None, _) as d_), I.No), v2_), _ when opts.arrow_sugar ->
        let hops, gf_, final = arrow_hops g_ (I.Pi ((d_, I.No), v2_), s) in
        let doms =
          List.map
            (fun (gi_, (vi_, si)) -> exp_sub opts gi_ (d + 1) (vi_, si))
            hops
        in
        let cod = exp_sub opts gf_ (d + 1) final in
        let rec chain = function
          | [] -> cod
          | x :: rest -> T.review (T.Arrow (g_loc, x, chain rest))
        in
        chain doms
    (* [ADec] binds an anonymous approximate variable; the original prints it
       as a lambda over [_] and so does this. *)
    | I.Pi (((I.ADec _ as d_), _), v2_), _ ->
        let body = exp_sub opts (I.Decl (g_, d_)) d (v2_, I.dot1 s) in
        T.review (T.Lam (g_loc, [ dec_of [ None ] (omitted ()) ], body))
    | I.Pi ((d_, _), v2_), _ ->
        (* Name the binder before descending, or the body's [bvarName] lookups
           find an unnamed declaration. *)
        let d'_ = N.decLUName g_ d_ in
        let dec = dec_sub opts g_ (d'_, s) in
        let body = exp_sub opts (I.Decl (g_, d'_)) d (v2_, I.dot1 s) in
        T.review (T.Pi (g_loc, [ dec ], body))
    | I.Lam (d_, u_), _ ->
        let d'_ = N.decLUName g_ d_ in
        let dec = dec_sub opts g_ (d'_, s) in
        let body = exp_sub opts (I.Decl (g_, d'_)) d (u_, I.dot1 s) in
        T.review (T.Lam (g_loc, [ dec ], body))
    | I.Root (h_, sp_), _ -> root opts g_ d (h_, sp_) s
    | (I.EVar _ as x_), s -> evar opts g_ d x_ s (fun n -> n)
    | (I.AVar _ as x_), s -> evar opts g_ d x_ s (fun n -> n ^ "_")
    | I.FgnExp (cs, fe), s ->
        T.review
          (T.Foreign
             ( g_loc,
               exp_sub opts g_ d (I.FgnExpStd.ToInternal.apply cs fe (), s)
             ))
    (* Unreachable after [whnf]; kept so the function is total rather than
       raising from inside a printer. *)
    | u_, _ -> internal (Cst.Opaque_tag "%%opaque") [ leaf u_ ]

  and leaf _ = internal (Cst.Opaque_tag "?") []

  and evar opts g_ d x_ s decorate =
    let node = variable (decorate (N.evarName g_ x_)) in
    if opts.implicit then T.review (T.App (g_loc, node, [ sub opts g_ d s ]))
    else
      let args =
        spine_sub opts g_ d 0 (sub_to_spine (I.ctxLength g_, s), I.id)
      in
      if args = [] then node else T.review (T.App (g_loc, node, args))

  (* An explicit substitution has no surface form, so it comes out tagged. *)
  and sub opts g_ d s =
    let rec go l s =
      if elide l opts.print_length then [ internal Cst.Elided_tag [] ]
      else
        match s with
        | I.Shift k -> [ internal (Cst.Shift_tag k) [] ]
        | I.Dot (I.Idx k, s) -> variable (N.bvarName g_ k) :: go (l + 1) s
        | I.Dot (I.Exp u_, s) ->
            exp_sub opts g_ (d + 1) (u_, I.id) :: go (l + 1) s
        | I.Dot (I.Undef, s) -> internal Cst.Undef_tag [] :: go (l + 1) s
        | I.Dot (I.Axp u_, s) ->
            exp_sub opts g_ (d + 1) (u_, I.id) :: go (l + 1) s
        | I.Dot (I.Block _, s) ->
            internal (Cst.Opaque_tag "%%block") [] :: go (l + 1) s
    in
    internal Cst.Subst_tag (go 0 s)

  and root opts g_ d (h_, sp_) s : Cst.term =
    let op = head opts g_ h_ in
    let apply args =
      if args = [] then op else T.review (T.App (g_loc, op, args))
    in
    if opts.implicit && not opts.print_infix then
      apply (spine_sub opts g_ d 0 (sp_, s))
    else if opts.implicit then
      (* [print_infix] keeps operator rendering for declared infixes while
         still showing implicit arguments. *)
      match fixity_con h_ with
      | FX.Infix _ -> explicit opts g_ d (h_, sp_) s op
      | _ -> apply (spine_sub opts g_ d 0 (sp_, s))
    else explicit opts g_ d (h_, sp_) s op

  and explicit opts g_ d (h_, sp_) s op : Cst.term =
    let apply args =
      if args = [] then op else T.review (T.App (g_loc, op, args))
    in
    match drop_imp (imp_con h_, sp_, arg_number (fixity_con h_)) with
    | Exact s'_ -> apply (spine_sub opts g_ d 0 (s'_, s))
    | Too_few when opts.eta_expand ->
        (* Under-applied: eta-expand so the operator reaches its arity, then
           start over on the expansion. *)
        exp_sub opts g_ d (Whnf.etaExpandRoot (I.Root (h_, sp_)), s)
    | Too_few -> apply (spine_sub opts g_ d 0 (sp_, s))
    | Too_many (s'_, s''_) ->
        (* One flat node, not a parenthesised saturated prefix -- see the
           header. The two denote the same term; only this one round-trips.
           The length counter carries across the join so [print_length] counts
           the arguments as the single list they are printed as. *)
        let saturated = spine_sub opts g_ d 0 (s'_, s) in
        apply (saturated @ spine_sub opts g_ d (List.length saturated) (s''_, s))

  and spine_sub opts g_ d l (sp_, s) : Cst.term list =
    match sp_ with
    | I.Nil -> []
    | I.SClo (sp_, s') -> spine_sub opts g_ d l (sp_, I.comp s' s)
    | I.App (u_, sp_) ->
        if elide l opts.print_length then []
        else if addots l opts.print_length then [ internal Cst.Elided_tag [] ]
        else
          exp_sub opts g_ (d + 1) (u_, s) :: spine_sub opts g_ d (l + 1) (sp_, s)

  (* Collect a maximal run of anonymous non-dependent [Pi]s, each paired with
     the context and substitution it must be resugared under. *)
  and arrow_hops g_ (u_, s) =
    match Whnf.whnf (u_, s) with
    | I.Pi (((I.Dec (None, v1_) as d_), I.No), v2_), s' ->
        let hops, gf_, final = arrow_hops (I.Decl (g_, d_)) (v2_, I.dot1 s') in
        ((g_, (v1_, s')) :: hops, gf_, final)
    | other -> ([], g_, other)

  and dec_sub opts g_ (d_, s) : Cst.decl =
    match d_ with
    | I.Dec (x, v_) -> dec_of [ x ] (exp_sub opts g_ 0 (v_, s))
    | I.BDec (x, (cid, t)) ->
        (* A block binder's classifier is a list of declarations, which the
           CST has no term form for; it goes out as an internal node wrapping
           the corresponding binder chain. *)
        let _, gblock_ = I.constBlock cid in
        let decs = dec_list_sub opts g_ (gblock_, I.comp t s) in
        dec_of [ x ]
          (internal (Cst.Opaque_tag "%%block")
             [ T.review (T.Pi (g_loc, decs, omitted ())) ])
    | I.ADec (x, _) -> dec_of [ x ] (omitted ())
    | I.NDec x -> dec_of [ x ] (omitted ())

  (* Successive declarations scope over each other, so each one is resugared
     in the context extended by its predecessors. *)
  and dec_list_sub opts g_ (ds, s) : Cst.decl list =
    match ds with
    | [] -> []
    | d_ :: rest ->
        dec_sub opts g_ (d_, s)
        :: dec_list_sub opts (I.Decl (g_, d_)) (rest, I.dot1 s)

  let exp opts g_ u_ = exp_sub opts g_ 0 (u_, I.id)
  let spine opts g_ sp_ = spine_sub opts g_ 0 0 (sp_, I.id)
  let dec opts g_ d_ = dec_sub opts g_ (d_, I.id)
  let dec_list opts g_ ds = dec_list_sub opts g_ (ds, I.id)
end
