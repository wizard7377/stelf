open! Syntax;;
open! Sgn;;
open! Reductio;;
open! Basis;;
module Compress(Compress__0: sig module Global : GLOBAL end) = struct
                                                                 module I = IntSyn;;
                                                                 module S = Syntax;;
                                                                 module Sgn = Sgn;;
                                                                 exception Unimp
                                                                 ;;
                                                                 exception NoModes
                                                                 ;;
                                                                 (* modes are not appropriate for the given I.ConDec *);;
                                                                 let debug =
                                                                   ref (-1);;
                                                                 let
                                                                   rec sgnReset
                                                                   () =
                                                                   Sgn.clear
                                                                   ();;
                                                                 (* xlate_type : IntSyn.Exp -> Syntax.tp *);;
                                                                 let
                                                                   rec xlate_type
                                                                   =
                                                                   function 
                                                                    | I.Pi
                                                                    ((I.Dec
                                                                    (_, e1),
                                                                    _), e2)
                                                                    -> (S.TPi
                                                                    (S.minus_,
                                                                    xlate_type
                                                                    e1,
                                                                    xlate_type
                                                                    e2))
                                                                    | I.Root
                                                                    (I.Const
                                                                    cid, sp)
                                                                    -> (S.TRoot
                                                                    (cid,
                                                                    xlate_spine
                                                                    sp))
                                                                    | I.Root
                                                                    (I.Def
                                                                    cid, sp)
                                                                    -> (S.TRoot
                                                                    (cid,
                                                                    xlate_spine
                                                                    sp))
                                                                    | I.Root
                                                                    (I.NSDef
                                                                    cid, sp)
                                                                    -> (S.TRoot
                                                                    (cid,
                                                                    xlate_spine
                                                                    sp))
                                                                    | I.Lam
                                                                    (_, t)
                                                                    -> xlate_type
                                                                    t(* ditto *)(* assuming cids of consts and defs to be disjoint *)
                                                                 and
                                                                   xlate_spine
                                                                   =
                                                                   function 
                                                                    | nil_
                                                                    -> []
                                                                    | I.App
                                                                    (e, s)
                                                                    -> (xlate_spinelt
                                                                    e
                                                                    :: xlate_spine
                                                                    s)
                                                                 and
                                                                   xlate_spinelt
                                                                   e =
                                                                   (S.Elt
                                                                    (xlate_term
                                                                    e))
                                                                 and
                                                                   xlate_term
                                                                   =
                                                                   function 
                                                                    | I.Root
                                                                    (I.Const
                                                                    cid, sp)
                                                                    -> (S.ATerm
                                                                    ((S.ARoot
                                                                    ((S.Const
                                                                    cid),
                                                                    xlate_spine
                                                                    sp))))
                                                                    | I.Root
                                                                    (I.Def
                                                                    cid, sp)
                                                                    -> (S.ATerm
                                                                    ((S.ARoot
                                                                    ((S.Const
                                                                    cid),
                                                                    xlate_spine
                                                                    sp))))
                                                                    | I.Root
                                                                    (I.NSDef
                                                                    cid, sp)
                                                                    -> (S.ATerm
                                                                    ((S.ARoot
                                                                    ((S.Const
                                                                    cid),
                                                                    xlate_spine
                                                                    sp))))
                                                                    | I.Root
                                                                    (I.BVar
                                                                    vid, sp)
                                                                    -> (S.ATerm
                                                                    ((S.ARoot
                                                                    ((S.Var
                                                                    (vid - 1)),
                                                                    xlate_spine
                                                                    sp))))
                                                                    | I.Lam
                                                                    (_, e)
                                                                    -> (S.NTerm
                                                                    ((S.Lam
                                                                    (xlate_term
                                                                    e))))(* ditto *)(* assuming cids of consts and defs to be disjoint *);;
                                                                 (* for type definitions, simply strip off the lambdas and leave
                                                   the variables free*);;
                                                                 (* xlate_kind : IntSyn.Exp -> Syntax.knd *);;
                                                                 let
                                                                   rec xlate_kind
                                                                   =
                                                                   function 
                                                                    | I.Pi
                                                                    ((I.Dec
                                                                    (_, e1),
                                                                    _), e2)
                                                                    -> (S.KPi
                                                                    (S.minus_,
                                                                    xlate_type
                                                                    e1,
                                                                    xlate_kind
                                                                    e2))
                                                                    | I.Uni
                                                                    type_
                                                                    -> S.type_;;
                                                                 open!
                                                                   struct
                                                                    open
                                                                    Syntax;;
                                                                    end;;
                                                                 (* simple skeletal form of types
     omits all dependencies, type constants *);;
                                                                 type
                                                                   simple_tp =
                                                                   | Base 
                                                                   | Arrow of
                                                                    simple_tp *
                                                                    simple_tp ;;
                                                                 let
                                                                   rec simplify_tp
                                                                   =
                                                                   function 
                                                                    | TPi
                                                                    (_, t1,
                                                                    t2)
                                                                    -> (Arrow
                                                                    (simplify_tp
                                                                    t1,
                                                                    simplify_tp
                                                                    t2))
                                                                    | TRoot _
                                                                    -> Base;;
                                                                 let
                                                                   rec simplify_knd
                                                                   =
                                                                   function 
                                                                    | KPi
                                                                    (_, t1,
                                                                    k2)
                                                                    -> (Arrow
                                                                    (simplify_tp
                                                                    t1,
                                                                    simplify_knd
                                                                    k2))
                                                                    | type_
                                                                    -> Base;;
                                                                 (* hereditarily perform some eta-expansions on
     a (term, type, spine, etc.) in a context
    (and if not synthesizing) at a simple type.

    The only type of eta-expansion performed is when we
    encounter
    x . (M_1, M_2, ... M_n)
    for a variable x, and M_1, ..., M_n have fewer lambda abstractions
    than their (skeletal) type would suggest.

    The complication with doing full eta-expansion is that if
    we were to wrap lambda abstractions around terms that occur
    in a synthesizing position, we would need to add ascriptions,
    and thus carry full types around everywhere.

    Fortunately, this weakened form of eta-expansion is all
    we need to reconcile the discrepancy between what twelf
    maintains as an invariant, and full eta-longness. *);;
                                                                 let
                                                                   rec eta_expand_term
                                                                   arg__1
                                                                   arg__2
                                                                   arg__3 =
                                                                   begin
                                                                   match 
                                                                   (arg__1,
                                                                    arg__2,
                                                                    arg__3)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_, NTerm
                                                                    t, t_)
                                                                    -> 
                                                                    nTerm_
                                                                    (eta_expand_nterm
                                                                    g_
                                                                    t
                                                                    t_)
                                                                   | 
                                                                   (g_, ATerm
                                                                    t, t_)
                                                                    -> 
                                                                    aTerm_
                                                                    (eta_expand_aterm
                                                                    g_
                                                                    t)
                                                                   end
                                                                 and
                                                                   eta_expand_nterm
                                                                   arg__4
                                                                   arg__5
                                                                   arg__6 =
                                                                   begin
                                                                   match 
                                                                   (arg__4,
                                                                    arg__5,
                                                                    arg__6)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_, Lam
                                                                    t, Arrow
                                                                    (t1, t2))
                                                                    -> 
                                                                    lam_
                                                                    (eta_expand_term
                                                                    ((t1
                                                                    :: g_))
                                                                    t
                                                                    t2)
                                                                   | 
                                                                   (g_, NRoot
                                                                    (h, s),
                                                                    t_)
                                                                    -> 
                                                                    nRoot_
                                                                    (h,
                                                                    eta_expand_spine
                                                                    g_
                                                                    s
                                                                    t_)
                                                                   | 
                                                                   (g_, Lam
                                                                    t, Base)
                                                                    -> 
                                                                    raise
                                                                    (syntax_
                                                                    "Lambda occurred where term of base type expected")
                                                                   end
                                                                 and
                                                                   eta_expand_aterm
                                                                   arg__7
                                                                   arg__8 =
                                                                   begin
                                                                   match 
                                                                   (arg__7,
                                                                    arg__8)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_, ARoot
                                                                    (Const n,
                                                                    s))
                                                                    -> 
                                                                    let stp =
                                                                    simplify_tp
                                                                    (typeOf
                                                                    (Sgn.o_classifier
                                                                    n))
                                                                    in 
                                                                    aRoot_
                                                                    (const_ n,
                                                                    eta_expand_spine
                                                                    g_
                                                                    s
                                                                    stp)
                                                                   | 
                                                                   (g_, ARoot
                                                                    (Var n,
                                                                    s))
                                                                    -> 
                                                                    let stp =
                                                                    List.nth
                                                                    (g_, n)
                                                                    in 
                                                                    aRoot_
                                                                    (var_ n,
                                                                    eta_expand_var_spine
                                                                    g_
                                                                    s
                                                                    stp)
                                                                   | 
                                                                   (g_, ERoot
                                                                    _)
                                                                    -> 
                                                                    raise
                                                                    (syntax_
                                                                    "invariant violated in eta_expand_aterm")
                                                                   end
                                                                 and
                                                                   eta_expand_tp
                                                                   arg__9
                                                                   arg__10 =
                                                                   begin
                                                                   match 
                                                                   (arg__9,
                                                                    arg__10)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_, TRoot
                                                                    (n, s))
                                                                    -> 
                                                                    let stp =
                                                                    simplify_knd
                                                                    (kindOf
                                                                    (Sgn.o_classifier
                                                                    n))
                                                                    in 
                                                                    tRoot_
                                                                    (n,
                                                                    eta_expand_spine
                                                                    g_
                                                                    s
                                                                    stp)
                                                                   | 
                                                                   (g_, TPi
                                                                    (m, a, b))
                                                                    -> 
                                                                    tPi_
                                                                    (m,
                                                                    eta_expand_tp
                                                                    g_
                                                                    a,
                                                                    eta_expand_tp
                                                                    ((simplify_tp
                                                                    a :: g_))
                                                                    b)
                                                                   end
                                                                 and
                                                                   eta_expand_knd
                                                                   arg__11
                                                                   arg__12 =
                                                                   begin
                                                                   match 
                                                                   (arg__11,
                                                                    arg__12)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_,
                                                                    type_)
                                                                    -> type_
                                                                   | 
                                                                   (g_, KPi
                                                                    (m, a, b))
                                                                    -> 
                                                                    kPi_
                                                                    (m,
                                                                    eta_expand_tp
                                                                    g_
                                                                    a,
                                                                    eta_expand_knd
                                                                    ((simplify_tp
                                                                    a :: g_))
                                                                    b)
                                                                   end
                                                                 and
                                                                   eta_expand_spine
                                                                   arg__13
                                                                   arg__14
                                                                   arg__15 =
                                                                   begin
                                                                   match 
                                                                   (arg__13,
                                                                    arg__14,
                                                                    arg__15)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_, [],
                                                                    Base)
                                                                    -> []
                                                                   | 
                                                                   (g_,
                                                                    (Elt m
                                                                    :: tl),
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> 
                                                                    (elt_
                                                                    (eta_expand_term
                                                                    g_
                                                                    m
                                                                    t1)
                                                                    :: 
                                                                    eta_expand_spine
                                                                    g_
                                                                    tl
                                                                    t2)
                                                                   | 
                                                                   (g_,
                                                                    (AElt m
                                                                    :: tl),
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> 
                                                                    (aElt_
                                                                    (eta_expand_aterm
                                                                    g_
                                                                    m)
                                                                    :: 
                                                                    eta_expand_spine
                                                                    g_
                                                                    tl
                                                                    t2)
                                                                   | 
                                                                   (g_,
                                                                    (Ascribe
                                                                    (m, a)
                                                                    :: tl),
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> 
                                                                    (ascribe_
                                                                    (eta_expand_nterm
                                                                    g_
                                                                    m
                                                                    t1,
                                                                    eta_expand_tp
                                                                    g_
                                                                    a)
                                                                    :: 
                                                                    eta_expand_spine
                                                                    g_
                                                                    tl
                                                                    t2)
                                                                   | 
                                                                   (g_,
                                                                    (omit_
                                                                    :: tl),
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> 
                                                                    (omit_
                                                                    :: 
                                                                    eta_expand_spine
                                                                    g_
                                                                    tl
                                                                    t2)
                                                                   | 
                                                                   (_, _, _)
                                                                    -> 
                                                                    raise
                                                                    (syntax_
                                                                    "Can't figure out how to eta expand spine")
                                                                   end(* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
                                                                 and
                                                                   eta_expand_var_spine
                                                                   arg__16
                                                                   arg__17
                                                                   arg__18 =
                                                                   begin
                                                                   match 
                                                                   (arg__16,
                                                                    arg__17,
                                                                    arg__18)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_, [],
                                                                    _) -> []
                                                                   | 
                                                                   (g_,
                                                                    (Elt m
                                                                    :: tl),
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> 
                                                                    (elt_
                                                                    (eta_expand_immediate
                                                                    (eta_expand_term
                                                                    g_
                                                                    m
                                                                    t1, t1))
                                                                    :: 
                                                                    eta_expand_spine
                                                                    g_
                                                                    tl
                                                                    t2)
                                                                   | 
                                                                   (_, _, _)
                                                                    -> 
                                                                    raise
                                                                    (syntax_
                                                                    "Can't figure out how to eta expand var-headed spine")
                                                                   end(* in fact this spine may not be eta-long yet *)
                                                                 and
                                                                   eta_expand_immediate
                                                                   =
                                                                   function 
                                                                    | (m,
                                                                    Base)
                                                                    -> m
                                                                    | (NTerm
                                                                    (Lam m),
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> nTerm_
                                                                    (lam_
                                                                    (eta_expand_immediate
                                                                    (m, t2)))
                                                                    | (m,
                                                                    Arrow
                                                                    (t1, t2))
                                                                    -> let
                                                                    variable
                                                                    =
                                                                    eta_expand_immediate
                                                                    (aTerm_
                                                                    (aRoot_
                                                                    (var_ 0,
                                                                    [])), t1)
                                                                    in nTerm_
                                                                    (lam_
                                                                    (eta_expand_immediate
                                                                    (apply_to
                                                                    (shift m,
                                                                    variable),
                                                                    t2)))
                                                                 and apply_to
                                                                   =
                                                                   function 
                                                                    | (ATerm
                                                                    (ARoot
                                                                    (h, s)),
                                                                    m)
                                                                    -> aTerm_
                                                                    (aRoot_
                                                                    (h,
                                                                    s @
                                                                    [elt_ m]))
                                                                    | (NTerm
                                                                    (NRoot
                                                                    (h, s)),
                                                                    m)
                                                                    -> nTerm_
                                                                    (nRoot_
                                                                    (h,
                                                                    s @
                                                                    [elt_ m]))
                                                                    | _
                                                                    -> raise
                                                                    (syntax_
                                                                    "Invariant violated in apply_to");;
                                                                 (* the behavior here is that we are eta-expanding all of the elements of the spine, not the head of *this* spine *);;
                                                                 (* here's where the actual expansion takes place *);;
                                                                 let typeOf =
                                                                   S.typeOf;;
                                                                 let kindOf =
                                                                   S.kindOf;;
                                                                 exception Debug
                                                                 of
                                                                 S.spine *
                                                                 S.tp *
                                                                 S.tp
                                                                 ;;
                                                                 (* val compress_type : Syntax.tp list -> Syntax.mode list option * Syntax.tp -> Syntax.tp *);;
                                                                 (* the length of the mode list, if there is one, should correspond to the number of pis in the input type.
    however, as indicated in the XXX comment below, it seems necessary to treat SOME of empty list
    as if it were NONE. This doesn't seem right. *);;
                                                                 let
                                                                   rec compress_type
                                                                   g_ s =
                                                                   compress_type'
                                                                   g_
                                                                   s(* if !debug < 0
                          then *)
                                                                 and
                                                                   compress_type'
                                                                   arg__19
                                                                   arg__20 =
                                                                   begin
                                                                   match 
                                                                   (arg__19,
                                                                    arg__20)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_,
                                                                    (None,
                                                                    S.TPi
                                                                    (_, a, b)))
                                                                    -> 
                                                                    (S.TPi
                                                                    (S.minus_,
                                                                    compress_type
                                                                    g_
                                                                    (None, a),
                                                                    compress_type
                                                                    ((a
                                                                    :: g_))
                                                                    (None, b)))
                                                                   | 
                                                                   (g_,
                                                                    (Some
                                                                    ((m
                                                                    :: ms)),
                                                                    S.TPi
                                                                    (_, a, b)))
                                                                    -> 
                                                                    (S.TPi
                                                                    (m,
                                                                    compress_type
                                                                    g_
                                                                    (None, a),
                                                                    compress_type
                                                                    ((a
                                                                    :: g_))
                                                                    ((Some
                                                                    ms), b)))
                                                                   | 
                                                                   (g_,
                                                                    (Some [],
                                                                    S.TRoot
                                                                    (cid, sp)))
                                                                    -> 
                                                                    (S.TRoot
                                                                    (cid,
                                                                    compress_type_spine
                                                                    g_
                                                                    (sp,
                                                                    kindOf
                                                                    (Sgn.o_classifier
                                                                    cid),
                                                                    kindOf
                                                                    (Sgn.classifier
                                                                    cid))))
                                                                   | 
                                                                   (g_,
                                                                    (None,
                                                                    (S.TRoot
                                                                    _ as a)))
                                                                    -> 
                                                                    compress_type
                                                                    g_
                                                                    ((Some
                                                                    []), a)
                                                                   | 
                                                                   (g_,
                                                                    (Some [],
                                                                    (S.TPi _
                                                                    as a)))
                                                                    -> 
                                                                    compress_type
                                                                    g_
                                                                    (None, a)
                                                                   end
                                                                 and
                                                                   compress_type_spine
                                                                   arg__21
                                                                   arg__22 =
                                                                   begin
                                                                   match 
                                                                   (arg__21,
                                                                    arg__22)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_,
                                                                    ([], w,
                                                                    wstar))
                                                                    -> []
                                                                   | 
                                                                   (g_,
                                                                    ((S.Elt m
                                                                    :: sp),
                                                                    S.KPi
                                                                    (_, a, v),
                                                                    S.KPi
                                                                    (mode,
                                                                    astar,
                                                                    vstar)))
                                                                    -> 
                                                                    let mstar
                                                                    =
                                                                    compress_term
                                                                    g_
                                                                    (m, a)
                                                                    in 
                                                                    let sstar
                                                                    =
                                                                    compress_type_spine
                                                                    g_
                                                                    (sp,
                                                                    S.subst_knd
                                                                    ((S.TermDot
                                                                    (m, a,
                                                                    S.id_)))
                                                                    v,
                                                                    S.subst_knd
                                                                    ((S.TermDot
                                                                    (mstar,
                                                                    astar,
                                                                    S.id_)))
                                                                    vstar)
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    (mode,
                                                                    mstar)
                                                                    with 
                                                                    
                                                                    | 
                                                                    (omit_,
                                                                    _)
                                                                    -> 
                                                                    (S.omit_
                                                                    :: sstar)
                                                                    | 
                                                                    (minus_,
                                                                    _)
                                                                    -> 
                                                                    ((S.Elt
                                                                    mstar)
                                                                    :: sstar)
                                                                    | 
                                                                    (plus_,
                                                                    S.ATerm
                                                                    t)
                                                                    -> 
                                                                    ((S.AElt
                                                                    t)
                                                                    :: sstar)
                                                                    | 
                                                                    (plus_,
                                                                    S.NTerm
                                                                    t)
                                                                    -> 
                                                                    ((S.Ascribe
                                                                    (t,
                                                                    compress_type
                                                                    g_
                                                                    (None, a)))
                                                                    :: sstar)
                                                                    end
                                                                   end
                                                                 and
                                                                   compress_spine
                                                                   arg__23
                                                                   arg__24 =
                                                                   begin
                                                                   match 
                                                                   (arg__23,
                                                                    arg__24)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_,
                                                                    ([], w,
                                                                    wstar))
                                                                    -> []
                                                                   | 
                                                                   (g_,
                                                                    ((S.Elt m
                                                                    :: sp),
                                                                    S.TPi
                                                                    (_, a, v),
                                                                    S.TPi
                                                                    (mode,
                                                                    astar,
                                                                    vstar)))
                                                                    -> 
                                                                    let mstar
                                                                    =
                                                                    compress_term
                                                                    g_
                                                                    (m, a)
                                                                    in 
                                                                    let sstar
                                                                    =
                                                                    compress_spine
                                                                    g_
                                                                    (sp,
                                                                    S.subst_tp
                                                                    ((S.TermDot
                                                                    (m, a,
                                                                    S.id_)))
                                                                    v,
                                                                    S.subst_tp
                                                                    ((S.TermDot
                                                                    (mstar,
                                                                    astar,
                                                                    S.id_)))
                                                                    vstar)
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    (mode,
                                                                    mstar)
                                                                    with 
                                                                    
                                                                    | 
                                                                    (omit_,
                                                                    _)
                                                                    -> 
                                                                    (S.omit_
                                                                    :: sstar)
                                                                    | 
                                                                    (minus_,
                                                                    _)
                                                                    -> 
                                                                    ((S.Elt
                                                                    mstar)
                                                                    :: sstar)
                                                                    | 
                                                                    (plus_,
                                                                    S.ATerm
                                                                    t)
                                                                    -> 
                                                                    ((S.AElt
                                                                    t)
                                                                    :: sstar)
                                                                    | 
                                                                    (plus_,
                                                                    S.NTerm
                                                                    t)
                                                                    -> 
                                                                    ((S.Ascribe
                                                                    (t,
                                                                    compress_type
                                                                    g_
                                                                    (None, a)))
                                                                    :: sstar)
                                                                    end
                                                                   end
                                                                 and
                                                                   compress_term
                                                                   arg__25
                                                                   arg__26 =
                                                                   begin
                                                                   match 
                                                                   (arg__25,
                                                                    arg__26)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_,
                                                                    (S.ATerm
                                                                    (S.ARoot
                                                                    (S.Var n,
                                                                    sp)), _))
                                                                    -> 
                                                                    let a =
                                                                    S.ctxLookup
                                                                    (g_, n)
                                                                    in 
                                                                    let astar
                                                                    =
                                                                    compress_type
                                                                    g_
                                                                    (None, a)
                                                                    in 
                                                                    (S.ATerm
                                                                    ((S.ARoot
                                                                    ((S.Var
                                                                    n),
                                                                    compress_spine
                                                                    g_
                                                                    (sp, a,
                                                                    astar)))))
                                                                   | 
                                                                   (g_,
                                                                    (S.ATerm
                                                                    (S.ARoot
                                                                    (S.Const
                                                                    n, sp)),
                                                                    _))
                                                                    -> 
                                                                    let a =
                                                                    typeOf
                                                                    (Sgn.o_classifier
                                                                    n)
                                                                    in 
                                                                    let astar
                                                                    =
                                                                    typeOf
                                                                    (Sgn.classifier
                                                                    n)
                                                                    in 
                                                                    let
                                                                    term_former
                                                                    =
                                                                    begin
                                                                    match 
                                                                    Sgn.get_p
                                                                    n
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    false
                                                                    -> 
                                                                    fun x
                                                                    -> 
                                                                    S.nTerm_
                                                                    (S.nRoot_
                                                                    x)
                                                                    | 
                                                                    _
                                                                    -> 
                                                                    fun x
                                                                    -> 
                                                                    S.aTerm_
                                                                    (S.aRoot_
                                                                    x)
                                                                    end
                                                                    in 
                                                                    term_former
                                                                    ((S.Const
                                                                    n),
                                                                    compress_spine
                                                                    g_
                                                                    (sp, a,
                                                                    astar))
                                                                   | 
                                                                   (g_,
                                                                    (S.NTerm
                                                                    (S.Lam t),
                                                                    S.TPi
                                                                    (_, a, b)))
                                                                    -> 
                                                                    (S.NTerm
                                                                    ((S.Lam
                                                                    (compress_term
                                                                    ((a
                                                                    :: g_))
                                                                    (t, b)))))
                                                                   end;;
                                                                 (* else  (if !debug = 0 then raise Debug(G, s) else ();
                                debug := !debug - 1; compress_type' G s) *);;
                                                                 (* XXX sketchy *);;
                                                                 (* XXX: optimization: don't compute mstar if omit? *);;
                                                                 let
                                                                   rec compress_kind
                                                                   arg__27
                                                                   arg__28 =
                                                                   begin
                                                                   match 
                                                                   (arg__27,
                                                                    arg__28)
                                                                   with 
                                                                   
                                                                   | 
                                                                   (g_,
                                                                    (None,
                                                                    S.KPi
                                                                    (_, a, k)))
                                                                    -> 
                                                                    (S.KPi
                                                                    (S.minus_,
                                                                    compress_type
                                                                    g_
                                                                    (None, a),
                                                                    compress_kind
                                                                    ((a
                                                                    :: g_))
                                                                    (None, k)))
                                                                   | 
                                                                   (g_,
                                                                    (Some
                                                                    ((m
                                                                    :: ms)),
                                                                    S.KPi
                                                                    (_, a, k)))
                                                                    -> 
                                                                    (S.KPi
                                                                    (m,
                                                                    compress_type
                                                                    g_
                                                                    (None, a),
                                                                    compress_kind
                                                                    ((a
                                                                    :: g_))
                                                                    ((Some
                                                                    ms), k)))
                                                                   | 
                                                                   (g_,
                                                                    (Some [],
                                                                    type_))
                                                                    -> S.type_
                                                                   | 
                                                                   (g_,
                                                                    (None,
                                                                    type_))
                                                                    -> S.type_
                                                                   end;;
                                                                 (* compress : cid * IntSyn.ConDec -> ConDec *);;
                                                                 let
                                                                   rec compress
                                                                   =
                                                                   function 
                                                                    | (cid,
                                                                    IntSyn.ConDec
                                                                    (name,
                                                                    None, _,
                                                                    normal_,
                                                                    a, type_))
                                                                    -> let x
                                                                    =
                                                                    xlate_type
                                                                    a
                                                                    in let x
                                                                    =
                                                                    eta_expand_tp
                                                                    []
                                                                    x
                                                                    in let
                                                                    modes =
                                                                    Sgn.get_modes
                                                                    cid
                                                                    in Sgn.condec
                                                                    (name,
                                                                    compress_type
                                                                    []
                                                                    (modes,
                                                                    x), x)
                                                                    | (cid,
                                                                    IntSyn.ConDec
                                                                    (name,
                                                                    None, _,
                                                                    normal_,
                                                                    k, kind_))
                                                                    -> let x
                                                                    =
                                                                    xlate_kind
                                                                    k
                                                                    in let
                                                                    modes =
                                                                    Sgn.get_modes
                                                                    cid
                                                                    in Sgn.tycondec
                                                                    (name,
                                                                    compress_kind
                                                                    []
                                                                    (modes,
                                                                    x), x)
                                                                    | (cid,
                                                                    IntSyn.ConDef
                                                                    (name,
                                                                    None, _,
                                                                    m, a,
                                                                    type_, _))
                                                                    -> let m
                                                                    =
                                                                    xlate_term
                                                                    m
                                                                    in let a
                                                                    =
                                                                    xlate_type
                                                                    a
                                                                    in let
                                                                    astar =
                                                                    compress_type
                                                                    []
                                                                    (None, a)
                                                                    in let
                                                                    mstar =
                                                                    compress_term
                                                                    []
                                                                    (m, a)
                                                                    in Sgn.defn
                                                                    (name,
                                                                    astar, a,
                                                                    mstar, m)
                                                                    | (cid,
                                                                    IntSyn.ConDef
                                                                    (name,
                                                                    None, _,
                                                                    a, k,
                                                                    kind_, _))
                                                                    -> let a
                                                                    =
                                                                    xlate_type
                                                                    a
                                                                    in let k
                                                                    =
                                                                    xlate_kind
                                                                    k
                                                                    in let
                                                                    kstar =
                                                                    compress_kind
                                                                    []
                                                                    (None, k)
                                                                    in let
                                                                    astar =
                                                                    compress_type
                                                                    (Syntax.explodeKind
                                                                    kstar)
                                                                    (None, a)
                                                                    in Sgn.tydefn
                                                                    (name,
                                                                    kstar, k,
                                                                    astar, a)
                                                                    | (cid,
                                                                    IntSyn.AbbrevDef
                                                                    (name,
                                                                    None, _,
                                                                    m, a,
                                                                    type_))
                                                                    -> let m
                                                                    =
                                                                    xlate_term
                                                                    m
                                                                    in let a
                                                                    =
                                                                    xlate_type
                                                                    a
                                                                    in let
                                                                    astar =
                                                                    compress_type
                                                                    []
                                                                    (None, a)
                                                                    in let
                                                                    mstar =
                                                                    compress_term
                                                                    []
                                                                    (m, a)
                                                                    in Sgn.abbrev
                                                                    (name,
                                                                    astar, a,
                                                                    mstar, m)
                                                                    | (cid,
                                                                    IntSyn.AbbrevDef
                                                                    (name,
                                                                    None, _,
                                                                    a, k,
                                                                    kind_))
                                                                    -> let a
                                                                    =
                                                                    xlate_type
                                                                    a
                                                                    in let k
                                                                    =
                                                                    xlate_kind
                                                                    k
                                                                    in let
                                                                    kstar =
                                                                    compress_kind
                                                                    []
                                                                    (None, k)
                                                                    in let
                                                                    astar =
                                                                    compress_type
                                                                    (Syntax.explodeKind
                                                                    kstar)
                                                                    (None, a)
                                                                    in Sgn.tyabbrev
                                                                    (name,
                                                                    kstar, k,
                                                                    astar, a)
                                                                    | _
                                                                    -> raise
                                                                    Unimp;;
                                                                 let
                                                                   rec sgnLookup
                                                                   cid =
                                                                   let c =
                                                                    Sgn.sub
                                                                    cid
                                                                    in 
                                                                    begin
                                                                    match c
                                                                    with 
                                                                    
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    let c' =
                                                                    compress
                                                                    (cid,
                                                                    I.sgnLookup
                                                                    cid)
                                                                    in 
                                                                    let _ =
                                                                    Sgn.update
                                                                    (cid, c')
                                                                    in 
                                                                    let _ =
                                                                    print
                                                                    ((Int.toString
                                                                    cid) ^
                                                                    "\n")
                                                                    in c'
                                                                    | 
                                                                    Some x
                                                                    -> x
                                                                    end;;
                                                                 (*  val sgnApp  = IntSyn.sgnApp

  fun sgnCompress () = sgnApp (ignore o sgnLookup) *);;
                                                                 let
                                                                   rec sgnCompressUpTo
                                                                   x = begin
                                                                   if 
                                                                   x < 0 then
                                                                   () else
                                                                   begin
                                                                    sgnCompressUpTo
                                                                    (x - 1);
                                                                    begin
                                                                    sgnLookup
                                                                    x;()
                                                                    end
                                                                    end
                                                                   end;;
                                                                 let check =
                                                                   Reductio.check;;
                                                                 let
                                                                   rec extract
                                                                   f =
                                                                   try 
                                                                   begin
                                                                    f ();
                                                                    raise
                                                                    Match
                                                                    end
                                                                   with 
                                                                   
                                                                   | 
                                                                   Debug x
                                                                    -> x;;
                                                                 let
                                                                   set_modes
                                                                   =
                                                                   Sgn.set_modes;;
                                                                 (* val log : Sgn.sigent list ref = ref [] *);;
                                                                 (* given a cid, pick some vaguely plausible omission modes *);;
                                                                 let
                                                                   rec naiveModes
                                                                   cid =
                                                                   let
                                                                    (ak,
                                                                    omitted_args,
                                                                    uni) =
                                                                    begin
                                                                    match 
                                                                    I.sgnLookup
                                                                    cid
                                                                    with 
                                                                    
                                                                    | 
                                                                    I.ConDec
                                                                    (name,
                                                                    package,
                                                                    o_a,
                                                                    status,
                                                                    ak, uni)
                                                                    -> 
                                                                    (ak, o_a,
                                                                    uni)
                                                                    | 
                                                                    I.ConDef
                                                                    (name,
                                                                    package,
                                                                    o_a, ak,
                                                                    def, uni,
                                                                    _)
                                                                    -> 
                                                                    (ak, o_a,
                                                                    uni)
                                                                    | 
                                                                    I.AbbrevDef
                                                                    (name,
                                                                    package,
                                                                    o_a, ak,
                                                                    def, uni)
                                                                    -> 
                                                                    (ak, o_a,
                                                                    uni)
                                                                    | 
                                                                    _
                                                                    -> 
                                                                    raise
                                                                    NoModes
                                                                    end
                                                                    in 
                                                                    let
                                                                    rec count_args
                                                                    =
                                                                    function 
                                                                    | I.Pi
                                                                    (_, ak')
                                                                    -> 1 +
                                                                    (count_args
                                                                    ak')
                                                                    | _ -> 0
                                                                    in 
                                                                    let
                                                                    total_args
                                                                    =
                                                                    count_args
                                                                    ak
                                                                    in 
                                                                    let
                                                                    rec can_omit
                                                                    ms =
                                                                    let _ =
                                                                    Sgn.set_modes
                                                                    (cid, ms)
                                                                    in 
                                                                    let s =
                                                                    compress
                                                                    (cid,
                                                                    I.sgnLookup
                                                                    cid)
                                                                    in 
                                                                    let t =
                                                                    Sgn.typeOfSigent
                                                                    s
                                                                    in 
                                                                    let
                                                                    isValid =
                                                                    Reductio.check_plusconst_strictness
                                                                    t
                                                                    in isValid
                                                                    (*                val _ = if true then log := !log @ [s] else () *)(*                val _ = if isValid then print ""yup\n"" else print ""nope\n"" *)
                                                                    in 
                                                                    let
                                                                    rec optimize'
                                                                    arg__29
                                                                    arg__30 =
                                                                    begin
                                                                    match 
                                                                    (arg__29,
                                                                    arg__30)
                                                                    with 
                                                                    
                                                                    | 
                                                                    (ms, [])
                                                                    -> 
                                                                    rev ms
                                                                    | 
                                                                    (ms,
                                                                    (plus_
                                                                    :: ms'))
                                                                    -> begin
                                                                    if
                                                                    can_omit
                                                                    ((rev ms)
                                                                    @
                                                                    ((S.minus_
                                                                    :: ms')))
                                                                    then
                                                                    optimize'
                                                                    ((S.minus_
                                                                    :: ms))
                                                                    ms' else
                                                                    optimize'
                                                                    ((S.plus_
                                                                    :: ms))
                                                                    ms' end
                                                                    | 
                                                                    (ms,
                                                                    (minus_
                                                                    :: ms'))
                                                                    -> begin
                                                                    if
                                                                    can_omit
                                                                    ((rev ms)
                                                                    @
                                                                    ((S.omit_
                                                                    :: ms')))
                                                                    then
                                                                    optimize'
                                                                    ((S.omit_
                                                                    :: ms))
                                                                    ms' else
                                                                    optimize'
                                                                    ((S.minus_
                                                                    :: ms))
                                                                    ms' end
                                                                    end
                                                                    in 
                                                                    let
                                                                    rec optimize
                                                                    ms =
                                                                    optimize'
                                                                    []
                                                                    ms
                                                                    in begin
                                                                    if
                                                                    uni =
                                                                    I.kind_
                                                                    then
                                                                    List.tabulate
                                                                    (total_args,
                                                                    function 
                                                                    | _
                                                                    -> S.minus_)
                                                                    else
                                                                    optimize
                                                                    (List.tabulate
                                                                    (total_args,
                                                                    function 
                                                                    | x
                                                                    -> begin
                                                                    if
                                                                    x <
                                                                    omitted_args
                                                                    then
                                                                    S.minus_
                                                                    else
                                                                    S.plus_
                                                                    end)) end;;
                                                                 (* Given a cid, return the ""ideal"" modes specified by twelf-
     omitted arguments. It is cheating to really use these for
     compression: the resulting signature will not typecheck. *);;
                                                                 let
                                                                   rec idealModes
                                                                   cid =
                                                                   let
                                                                    (ak,
                                                                    omitted_args)
                                                                    =
                                                                    begin
                                                                    match 
                                                                    I.sgnLookup
                                                                    cid
                                                                    with 
                                                                    
                                                                    | 
                                                                    I.ConDec
                                                                    (name,
                                                                    package,
                                                                    o_a,
                                                                    status,
                                                                    ak, uni)
                                                                    -> 
                                                                    (ak, o_a)
                                                                    | 
                                                                    I.ConDef
                                                                    (name,
                                                                    package,
                                                                    o_a, ak,
                                                                    def, uni,
                                                                    _)
                                                                    -> 
                                                                    (ak, o_a)
                                                                    | 
                                                                    I.AbbrevDef
                                                                    (name,
                                                                    package,
                                                                    o_a, ak,
                                                                    def, uni)
                                                                    -> 
                                                                    (ak, o_a)
                                                                    | 
                                                                    _
                                                                    -> 
                                                                    raise
                                                                    NoModes
                                                                    end
                                                                    in 
                                                                    let
                                                                    rec count_args
                                                                    =
                                                                    function 
                                                                    | I.Pi
                                                                    (_, ak')
                                                                    -> 1 +
                                                                    (count_args
                                                                    ak')
                                                                    | _ -> 0
                                                                    in 
                                                                    let
                                                                    total_args
                                                                    =
                                                                    count_args
                                                                    ak
                                                                    in 
                                                                    List.tabulate
                                                                    (total_args,
                                                                    function 
                                                                    | x
                                                                    -> begin
                                                                    if
                                                                    x <
                                                                    omitted_args
                                                                    then
                                                                    S.omit_
                                                                    else
                                                                    S.minus_
                                                                    end);;
                                                                 (* not likely to work if the mode-setting function f actually depends on
   properties of earlier sgn entries *);;
                                                                 let
                                                                   rec setModesUpTo
                                                                   x f =
                                                                   begin
                                                                   if 
                                                                   x < 0 then
                                                                   () else
                                                                   begin
                                                                    setModesUpTo
                                                                    (x - 1)
                                                                    f;
                                                                    begin
                                                                    Sgn.set_modes
                                                                    (x, f x);
                                                                    ()
                                                                    end
                                                                    end
                                                                   end;;
                                                                 let
                                                                   rec sgnAutoCompress
                                                                   n f =
                                                                   try 
                                                                   let modes
                                                                    = 
                                                                    f n
                                                                    in 
                                                                    begin
                                                                    Sgn.set_modes
                                                                    (n,
                                                                    modes);
                                                                    Sgn.update
                                                                    (n,
                                                                    compress
                                                                    (n,
                                                                    IntSyn.sgnLookup
                                                                    n))
                                                                    end
                                                                   with 
                                                                   
                                                                   | 
                                                                   NoModes
                                                                    -> ();;
                                                                 let
                                                                   rec sgnAutoCompressUpTo'
                                                                   n0 n f =
                                                                   begin
                                                                   if 
                                                                   n0 > n
                                                                   then ()
                                                                   else
                                                                   let _ =
                                                                    begin
                                                                    match 
                                                                    Sgn.sub
                                                                    n0
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some _
                                                                    -> ()
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    try 
                                                                    let modes
                                                                    = f n0
                                                                    in 
                                                                    begin
                                                                    Sgn.set_modes
                                                                    (n0,
                                                                    modes);
                                                                    begin
                                                                    Sgn.update
                                                                    (n0,
                                                                    compress
                                                                    (n0,
                                                                    IntSyn.sgnLookup
                                                                    n0));
                                                                    begin
                                                                    if
                                                                    (n0 mod
                                                                    100) = 0
                                                                    then
                                                                    print
                                                                    ((Int.toString
                                                                    n0) ^
                                                                    "\n")
                                                                    else ()
                                                                    end
                                                                    end
                                                                    end
                                                                    with 
                                                                    
                                                                    | 
                                                                    NoModes
                                                                    -> ()
                                                                    end
                                                                    (* if not, compress it *)
                                                                    in 
                                                                    sgnAutoCompressUpTo'
                                                                    (n0 + 1)
                                                                    n
                                                                    f
                                                                    (* has this entry already been processed? *)
                                                                   end;;
                                                                 let
                                                                   rec sgnAutoCompressUpTo
                                                                   n f =
                                                                   sgnAutoCompressUpTo'
                                                                   0
                                                                   n
                                                                   f;;
                                                                 let check =
                                                                   Reductio.check;;
                                                                 end;;
(*
c : ((o -> o) -> o -> o) -> o

a : o -> o

c ([x] a)

eta_expand_immediate ( a) ( o -> o)
*);;