(** Signature entries, constraints and instantiations.

    A [conDec] resugars to a [Cst.cmd] -- the command that would declare it --
    rather than to a [Cst.conDec]. [Cst.conDec] carries no implicit-argument
    count, no source location, and its [ConstantDecl_] cannot distinguish a
    [%sort] from a [%term]; [Cst.View.Cmd] has exactly the cases the parser
    produces. *)

module I = Intsyn.IntSyn
module N = Names.Names_

module Make (Cst : Cst.CST) = struct
  module V = Cst.View
  module T = Cst.View.Term
  module Tm = Term.Make (Cst)
  module Dl = Decl.Make (Cst)

  type cnstr_form = Solved | Eqn of Cst.term * Cst.term | Fgn of Cst.term list

  let g_loc : Cst.loc = V.Loc.review V.Loc.Ghost
  let omitted () = T.review (T.Omitted g_loc)

  let dec_of names ty =
    V.Decl.review (V.Decl.Decl1 (g_loc, names, ty, omitted ()))

  let name_of (d : I.conDec) : string =
    let (N.Qid (_, id)) = N.conDecQid d in
    id

  (* Skip the leading implicit binders, naming each as it goes. [decEName], not
     [decLUName]: an implicit binder stands for something the elaborator will
     infer, so it gets an existential name. *)
  let rec skip_imp = function
    | 0, g_, v_ -> (g_, v_)
    | i, g_, I.Pi ((d_, _), v_) ->
        skip_imp (i - 1, I.Decl (g_, N.decEName (g_, d_)), v_)
    | _, g_, v_ -> (g_, v_)

  let rec skip_imp2 = function
    | 0, g_, v_, u_ -> (g_, v_, u_)
    | i, g_, I.Pi ((_, _), v_), I.Lam (d'_, u_) ->
        skip_imp2 (i - 1, I.Decl (g_, N.decEName (g_, d'_)), v_, u_)
    | _, g_, v_, u_ -> (g_, v_, u_)

  (* A kind is a chain of binders ending in [type]. The trailing universe is
     dropped: [%sort] supplies it, and there is no surface syntax for writing
     it explicitly in that position. *)
  let rec kind_binders (opts : Options.t) g_ v_ : Cst.decl list =
    match v_ with
    | I.Uni _ -> []
    | I.Pi ((d_, _), v2_) ->
        let d'_ = N.decLUName (g_, d_) in
        Tm.dec opts g_ d'_ :: kind_binders opts (I.Decl (g_, d'_)) v2_
    (* Not a well-formed kind. Emitting it as an anonymous binder keeps the
       function total and the output parseable. *)
    | _ -> [ dec_of [ None ] (Tm.exp opts g_ v_) ]

  let con_dec (opts : Options.t) ~(hide : bool) (d : I.conDec) : Cst.cmd =
    (* One reset for every case, not one per branch: forgetting it in a single
       branch yields binder names that drift between renderings of the same
       declaration. *)
    N.varReset I.Null;
    let name = name_of d in
    match d with
    | I.ConDec (_, _, imp, _, v_, l_) -> (
        let g_, v_ =
          if hide then skip_imp (imp, I.Null, v_) else (I.Null, v_)
        in
        match l_ with
        | I.Kind ->
            V.Cmd.review (V.Cmd.Sort (g_loc, [ name ], kind_binders opts g_ v_))
        | I.Type ->
            V.Cmd.review
              (V.Cmd.Term (g_loc, dec_of [ Some name ] (Tm.exp opts g_ v_))))
    | I.ConDef (_, _, imp, u_, v_, _, _) ->
        let g_, v_, u_ =
          if hide then skip_imp2 (imp, I.Null, v_, u_) else (I.Null, v_, u_)
        in
        (* The view's field order is (name, term, type); the surface order is
           [%def NAME TYPE TERM]. See [Modern.parse_define]. *)
        V.Cmd.review
          (V.Cmd.Define
             ( g_loc,
               V.Define.review
                 (V.Define.Define
                    ( g_loc,
                      Some name,
                      Tm.exp opts g_ u_,
                      Some (Tm.exp opts g_ v_) )) ))
    | I.AbbrevDef (_, _, imp, u_, v_, _) ->
        let g_, v_, u_ =
          if hide then skip_imp2 (imp, I.Null, v_, u_) else (I.Null, v_, u_)
        in
        (* [%inline] takes a single term, so the type rides along as an
           ascription. [HasType]'s view order is (term, type). *)
        V.Cmd.review
          (V.Cmd.Inline
             ( g_loc,
               name,
               T.review
                 (T.HasType (g_loc, Tm.exp opts g_ u_, Tm.exp opts g_ v_)) ))
    | I.BlockDec (_, _, gsome_, lblock_) ->
        (* [some] parameters are written [[x A]] and block hypotheses [{x A}];
           see [Modern.parse_block_item]. *)
        let some = Dl.ctx opts I.Null gsome_ in
        let block = Tm.dec_list opts gsome_ lblock_ in
        V.Cmd.review
          (V.Cmd.Block
             ( g_loc,
               name,
               List.map
                 (fun d -> V.BlockItem.review (V.BlockItem.Any (g_loc, d)))
                 some
               @ List.map
                   (fun d -> V.BlockItem.review (V.BlockItem.All (g_loc, d)))
                   block ))
    | I.BlockDef (_, _, w_) ->
        V.Cmd.review
          (V.Cmd.Union
             (g_loc, name, List.map (fun cid -> snd (Tm.const_sym opts cid)) w_))
    | I.SkoDec (_, _, imp, v_, _) ->
        (* There is no [%skolem] command, so this deliberately does not round
           trip; it exists so that dumping a signature containing Skolem
           constants is possible at all. *)
        let g_, v_ =
          if hide then skip_imp (imp, I.Null, v_) else (I.Null, v_)
        in
        V.Cmd.review
          (V.Cmd.Term
             ( g_loc,
               dec_of [ Some name ]
                 (T.review
                    (T.Internal
                       (g_loc, Cst.Opaque_tag "%%skolem", [ Tm.exp opts g_ v_ ])))
             ))

  (* [IntSyn.cnstr] is already a [cnstr_ ref]; the payload is what carries the
     three shapes. *)
  let cnstr (opts : Options.t) (c : I.cnstr) : cnstr_form =
    match !c with
    | I.Solved -> Solved
    | I.Eqn (g_, u1_, u2_) ->
        let g'_ = N.ctxLUName g_ in
        Eqn (Tm.exp opts g'_ u1_, Tm.exp opts g'_ u2_)
    | I.FgnCnstr (cs, inner) ->
        Fgn
          (List.map
             (fun (g_, u_) -> Tm.exp opts (N.ctxLUName g_) u_)
             (I.FgnCnstrStd.ToInternal.apply (cs, inner) ()))

  let cnstrs opts cs = List.map (cnstr opts) cs
  let worlds opts cids = List.map (Tm.const_sym opts) cids

  (* An existential variable's solution is only meaningful under the context it
     was created in, so it is abstracted over that context first. *)
  let rec abstract_lam = function
    | I.Null, u_ -> u_
    | I.Decl (g_, d_), u_ -> abstract_lam (g_, I.Lam (d_, u_))

  let evar_inst (opts : Options.t) (xs : (I.exp * string) list) :
      (string * Cst.term) list =
    List.map
      (fun (u_, name) ->
        let u'_ =
          match u_ with
          | I.EVar (_, g_, _, _) -> abstract_lam (g_, u_)
          | _ -> u_
        in
        (name, Tm.exp opts I.Null u'_))
      xs
end
