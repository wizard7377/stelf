# 1 "src/compress/reductio.sig.ml"

# 1 "src/compress/reductio.fun.ml"

# 1 "src/compress/reductio.sml.ml"
open! Strict;;
open! Sgn;;
open! Basis;;
module Reductio = struct
                    exception Unimp ;;
                    exception Error of string ;;
                    exception Matching of string ;;
                    exception NonPattern ;;
                    exception NotFound of string ;;
                    open Syntax;;
                    type kinding_constraint =
                      | Con_lf 
                      | Con_plus 
                      | Con_minus ;;
                    (* Pi- only *);;
                    (* Pi-, Pi+, [Pi] matched by strict occ in later args
                             not necessarily in return type *);;
                    (* All Pis, and [Pi] can use strict occs in later args
                              and in return type. *);;
                    (* left side is open, (with respect to outer pi bindings)
           and right side is closed *);;
                    type eq_c =
                      | EltC of spinelt * spinelt 
                      | SpineC of spine * spine 
                      | TypeC of tp * tp ;;
                    type nonrec tp_c = term * tp;;
                    (* equality checking *);;
                    let rec tp_eq =
                      function 
                               | (TRoot (n, sp), TRoot (n', sp'))
                                   -> type_const_head_eq (n, n', sp, sp')
                               | (TPi (m, a, b), TPi (m', a', b'))
                                   -> (m = m') &&
                                        ((tp_eq (a, a')) && (tp_eq (b, b')))
                               | _ -> false
                    and sp_eq =
                      function 
                               | ([], []) -> true
                               | ((e :: sp), (e' :: sp'))
                                   -> (elt_eq (e, e')) && (sp_eq (sp, sp'))
                               | _ -> false
                    and elt_eq (t, t') =
                      elt_eq' (elt_eroot_elim t, elt_eroot_elim t')
                    and elt_eq' =
                      function 
                               | (Elt t, Elt t') -> tm_eq (t, t')
                               | (AElt t, AElt t') -> atm_eq (t, t')
                               | (Ascribe (t, a), Ascribe (t', a'))
                                   -> (ntm_eq (t, t')) && (tp_eq (a, a'))
                               | (Omit, Omit) -> true
                               | _ -> false
                    and tm_eq =
                      function 
                               | (NTerm t, NTerm t') -> ntm_eq (t, t')
                               | (ATerm t, ATerm t') -> atm_eq (t, t')
                               | _ -> false
                    and atm_eq =
                      function 
                               | ((ARoot (Const n, sp) as tm),
                                  (ARoot (Const n', sp') as tm'))
                                   -> const_head_eq
                                      (n, n', sp, sp', aTerm_ tm, aTerm_ tm')
                               | (ARoot (Var n, sp), ARoot (Var n', sp'))
                                   -> (n = n') && (sp_eq (sp, sp'))
                               | _ -> false
                    and ntm_eq (t, t') =
                      ntm_eq' (ntm_eroot_elim t, ntm_eroot_elim t')
                    and ntm_eq' =
                      function 
                               | ((NRoot (Const n, sp) as tm),
                                  (NRoot (Const n', sp') as tm'))
                                   -> const_head_eq
                                      (n, n', sp, sp', nTerm_ tm, nTerm_ tm')
                               | (Lam t, Lam t') -> tm_eq (t, t')
                               | _ -> false
                    and const_head_eq (n, n', sp, sp', tm, tm') =
                      let def = Sgn.def n
                        in let def' = Sgn.def n'
                             in let eq_and_strict =
                                  (n = n') &&
                                    ((def = Sgn.def_none_) ||
                                       (not (Sgn.abbreviation n)))
                                  in let rec redux t n sp =
                                       reduce
                                       (srTerm (t, typeOf (Sgn.classifier n)),
                                        sp)
                                       in begin
                                          match (eq_and_strict, def, def')
                                          with 
                                               | (true, _, _)
                                                   -> sp_eq (sp, sp')
                                               | (false, def_none_,
                                                  def_none_) -> false
                                               | (_, Sgn.Def_term t,
                                                  Sgn.Def_term t')
                                                   -> tm_eq
                                                      (redux t n sp,
                                                       redux t' n' sp')
                                               | (_, Sgn.Def_term t,
                                                  def_none_)
                                                   -> tm_eq
                                                      (redux t n sp, tm')
                                               | (_, def_none_, Sgn.Def_term
                                                  t')
                                                   -> tm_eq
                                                      (tm, redux t' n' sp')
                                               | _
                                                   -> raise
                                                      (syntax_
                                                       "invariant violation")
                                          end
                    and type_const_head_eq (n, n', sp, sp') =
                      let def = Sgn.def n
                        in let def' = Sgn.def n'
                             in let eq_and_strict =
                                  (n = n') &&
                                    ((def = Sgn.def_none_) ||
                                       (not (Sgn.abbreviation n)))
                                  in let rec redux a n sp =
                                       tp_reduce
                                       (a, kindOf (Sgn.classifier n), sp)
                                       in begin
                                          match (eq_and_strict, def, def')
                                          with 
                                               | (true, _, _)
                                                   -> sp_eq (sp, sp')
                                               | (false, def_none_,
                                                  def_none_) -> false
                                               | (_, Sgn.Def_type a,
                                                  Sgn.Def_type a')
                                                   -> tp_eq
                                                      (redux a n sp,
                                                       redux a' n' sp')
                                               | (_, Sgn.Def_type a,
                                                  def_none_)
                                                   -> tp_eq
                                                      (redux a n sp,
                                                       tRoot_ (n', sp'))
                                               | (_, def_none_, Sgn.Def_type
                                                  a')
                                                   -> tp_eq
                                                      (tRoot_ (n, sp),
                                                       redux a' n' sp')
                                               | _
                                                   -> raise
                                                      (syntax_
                                                       "invariant violation")
                                          end;;
                    (* ERoots are taken care of at the spine element level *);;
                    (* determine whether two roots are equal. n and n' are the cids of the heads, whether the
           roots happen to be nroots or aroots. sp and sp' are the spines, and tm and tm' are the
           entire roots. *);;
                    (* similar thing for atomic types. Here we need not include redundant arguments for the entire
            TRoot since there is only one kind of TRoot (not both ARoot and NRoot in the case of terms)
            so we just build it back up from scratch *);;
                    (* is an equality constraint satisfied? *);;
                    let rec eq_c_true =
                      function 
                               | EltC (e, e') -> elt_eq (e, e')
                               | SpineC (s, s') -> sp_eq (s, s')
                               | TypeC (a, a') -> tp_eq (a, a');;
                    (* The type ppsubst is a compact way of representing a
           class of substitutions that contains all of the pattern
           substitutions. These are the ""prepattern"" substitutions,
           the ones that are of the form 
           i1.i2. ... in . shift^m
           where all the i1...in are variables. *);;
                    (* ([i1, i2, ... , in], m) represents i1.i2. ... in . shift^m *);;
                    type nonrec ppsubst = int list * int;;
                    (* pp_shift pps m: compute pps o shift^m *);;
                    let rec pp_shift (vs, shift) m =
                      let len = length vs in begin
                        if m < len then (List.drop (vs, m), shift) else
                        ([], (m - len) + shift) end;;
                    (* pp_nth: extract the result of applying a ppsubst to the nth variable *);;
                    let rec pp_nth (vs, shift) n =
                      let len = length vs in begin
                        if n < len then List.nth (vs, n) else
                        (n - len) + shift end;;
                    (* pp_o: compose two ppsubsts *);;
                    let rec pp_o (pps, (vs, shift)) =
                      let (vs', shift') = pp_shift pps shift
                        in ((map (pp_nth pps) vs) @ vs', shift');;
                    (* pp_comp: compose a list of ppsubsts *);;
                    let rec pp_comp ppsl = foldr pp_o ([], 0) ppsl;;
                    (* pp_normalize s
           if a substitution s is equal to a 'prepattern'
           i1.i2. ... in . shift^m (no restriction on the i's being distinct)
           returns ([i1, i2, ... , in], m).
           Otherwise raises Domain. *);;
                    let rec pp_normalize s = pp_normalize' s
                    and pp_normalize' =
                      function 
                               | Id -> ([], 0)
                               | TermDot (t, a, s)
                                   -> let v =
                                        try Strict.eta_contract_var (elt_ t)
                                        with 
                                             | etaContract_ -> raise Domain
                                        in let (vs, shift) = pp_normalize' s
                                             in ((v :: vs), shift)
                                             (* if the term being consed on is not an eta-expansion of
                    a variable, forget about it *)
                               | ZeroDotShift s
                                   -> let (vs, shift) = pp_normalize' s
                                        in ((0
                                             :: map
                                                (function 
                                                          | x -> x + 1)
                                                vs),
                                            shift + 1)
                               | Shift (n, m)
                                   -> (List.tabulate (n, function 
                                                                  | x -> x),
                                       n + m)
                               | EVarDot _ -> raise Domain
                               | VarOptDot (no, s)
                                   -> let (vs, shift) = pp_normalize' s
                                        in begin
                                           match no
                                           with 
                                                | Some n
                                                    -> ((n :: vs), shift)
                                                | None
                                                    -> raise
                                                       ((Error
                                                         "??? I'm not sure this is really wrong"))
                                           end
                               | Compose sl -> prepattern (substs_comp sl)(* XXX: Correct??? *)(* using the fact that Shift (n+1) m = ZeroDotShift (Shift n m) *)
                    and prepattern ((s : subst)) = pp_normalize s;;
                    (* prepattern: convert a subst into a ppsubst *);;
                    (* raises Domain if it is not a prepattern *);;
                    (* pp_ispat: is this ppsubst a pattern substitution? *);;
                    let rec pp_ispat =
                      function 
                               | ([], shift) -> true
                               | ((n :: s), shift)
                                   -> let rec isn x = x = n
                                        in let rec hasn s = List.exists isn s
                                             in (n < shift) &&
                                                  ((not (hasn s)) &&
                                                     (pp_ispat (s, shift)));;
                    (* take a list of int options and a shift value and
        produce an actual substitution. This is morally a one-sided
        inverse to pp_normalize *);;
                    let rec makesubst =
                      function 
                               | ([], 0) -> Id
                               | ([], shift) -> shift_ (0, shift)
                               | ((v :: vs), shift)
                                   -> varOptDot_ (v, makesubst (vs, shift));;
                    (* take in a ppsubst and return a substitution (which may involve VarOptDots) that is its inverse. *);;
                    let rec pp_invert (vs, shift) =
                      let inds = List.tabulate (shift, function 
                                                                | x -> x)
                        in let rec search arg__0 arg__1 arg__2 =
                             begin
                             match (arg__0, arg__1, arg__2)
                             with 
                                  | (n, [], (x : int)) -> None
                                  | (n, (h :: tl), x) -> begin
                                      if x = h then (Some n) else
                                      search (n + 1) tl x end
                             end
                             in makesubst (map (search 0 vs) inds, length vs);;
                    (* Here begins all the matching code.
           flex_left takes an uninstantiated evar, a substitution, and a right-hand-side of an equation.
           The equation is
           E[sl] = RHS
           If it can successfully instantiate E with RHS[sl^-1], then it does so
           imperatively and returns ().

           If sl is not pattern it raises NonPattern.
           If RHS is not in the range of sl, then MissingVar is raised by substitution *);;
                    let rec flex_left =
                      function 
                               | ((({ contents = None} as r), a),
                                  (s : subst), rhs)
                                   -> let pps =
                                        try prepattern s
                                        with 
                                             | Domain -> raise NonPattern
                                        in let _ = begin
                                             if pp_ispat pps then () else
                                             raise NonPattern end
                                             in let ppsi = pp_invert pps
                                                  in let rhs' =
                                                       subst_term
                                                       ppsi
                                                       (termof rhs)
                                                       in let _ =
                                                            r :=
                                                              ((Some rhs'))
                                                            in ()
                               | _
                                   -> raise
                                      ((Error "evar invariant violated"));;
                    (* match_one' takes an equation (which by invariant does not
           have an instantiated evar on the left, and is ground on the
           right) and returns a list of smaller equations that are
           equivalent to it, or else throws NonPattern in the event
           that it finds a flex-rigid equation where the flex side is
           not pattern. *);;
                    (* XXX this just_one stuff is here for debugging: replace with match_one *);;
                    let rec just_one c = [c]
                    and just_one' c = [c]
                    and match_one' =
                      function 
                               | EltC
                                   (Elt (NTerm (Lam t)), Elt
                                    (NTerm (Lam t')))
                                   -> just_one ((EltC (elt_ t, elt_ t')))
                               | EltC
                                   ((Elt (NTerm (NRoot (Const n, s))) as elt),
                                    (Elt (NTerm (NRoot (Const n', s'))) as
                                      elt'))
                                   -> match_const_head
                                      (n, n', s, s', elt, elt',
                                       "c- head mismatch")
                               | EltC
                                   ((Elt (ATerm (ARoot (Const n, s))) as elt),
                                    (Elt (ATerm (ARoot (Const n', s'))) as
                                      elt'))
                                   -> match_const_head
                                      (n, n', s, s', elt, elt',
                                       "c+ head mismatch")
                               | EltC
                                   (Elt (ATerm (ARoot (Var n, s))), Elt
                                    (ATerm (ARoot (Var n', s'))))
                                   -> begin
                                   if n = n' then
                                   just_one' ((SpineC (s, s'))) else
                                   raise ((Matching "var head mismatch")) end
                               | EltC (AElt t, AElt t')
                                   -> just_one'
                                      ((EltC
                                        (elt_ (aTerm_ t), elt_ (aTerm_ t'))))
                               | EltC (Ascribe (m, a), Ascribe (m', a'))
                                   -> match_two
                                      ((EltC
                                        (elt_ (nTerm_ m), elt_ (nTerm_ m'))))
                                      ((TypeC (a, a')))
                               | EltC (Omit, Omit) -> []
                               | TypeC (TPi (m, a, b), TPi (m', a', b'))
                                   -> begin
                                   if (m = minus_) && (m' = minus_) then
                                   match_two
                                   ((TypeC (a, a')))
                                   ((TypeC (b, b'))) else
                                   raise ((Matching "mode mismatch")) end
                               | TypeC (TRoot (n, s), TRoot (n', s'))
                                   -> match_type_const_head
                                      (n, n', s, s', "type family mismatch")
                               | SpineC ([], []) -> []
                               | SpineC ((h :: s), (h' :: s'))
                                   -> match_two
                                      ((EltC (h, h')))
                                      ((SpineC (s, s')))
                               | EltC
                                   (Elt (ATerm (ERoot (ev, (s : subst)))),
                                    elt)
                                   -> begin
                                        flex_left (ev, s, elt);[]
                                        end
                               | x -> raise ((Matching "doesn't match"))
                    and match_one =
                      function 
                               | EltC (elt, elt')
                                   -> match_one'
                                      ((EltC
                                        (elt_eroot_elim elt,
                                         elt_eroot_elim elt')))
                               | e -> match_one' e
                    and match_two e1 e2 = [e1; e2]
                    and match_const_head (n, n', s, s', elt, elt', err) =
                      let def = Sgn.def n
                        in let def' = Sgn.def n'
                             in let eq_and_strict =
                                  (n = n') &&
                                    ((def = Sgn.def_none_) ||
                                       (not (Sgn.abbreviation n)))
                                  in let rec redux t n sp =
                                       reduce
                                       (srTerm (t, typeOf (Sgn.classifier n)),
                                        sp)
                                       in let eq =
                                            begin
                                            match (eq_and_strict, def, def')
                                            with 
                                                 | (true, _, _)
                                                     -> (SpineC (s, s'))
                                                 | (false, def_none_,
                                                    def_none_)
                                                     -> raise
                                                        ((Matching err))
                                                 | (_, Sgn.Def_term t,
                                                    Sgn.Def_term t')
                                                     -> (EltC
                                                         (elt_ (redux t n s),
                                                          elt_
                                                          (redux t' n' s')))
                                                 | (_, Sgn.Def_term t,
                                                    def_none_)
                                                     -> (EltC
                                                         (elt_ (redux t n s),
                                                          elt'))
                                                 | (_, def_none_,
                                                    Sgn.Def_term t')
                                                     -> (EltC
                                                         (elt,
                                                          elt_
                                                          (redux t' n' s')))
                                                 | _
                                                     -> raise
                                                        ((Matching
                                                          "invariant violation"))
                                            end in just_one' eq
                    and match_type_const_head (n, n', s, s', err) =
                      let def = Sgn.def n
                        in let def' = Sgn.def n'
                             in let eq_and_strict =
                                  (n = n') &&
                                    ((def = Sgn.def_none_) ||
                                       (not (Sgn.abbreviation n)))
                                  in let rec redux a n sp =
                                       tp_reduce
                                       (a, kindOf (Sgn.classifier n), sp)
                                       in let eq =
                                            begin
                                            match (eq_and_strict, def, def')
                                            with 
                                                 | (true, _, _)
                                                     -> (SpineC (s, s'))
                                                 | (false, def_none_,
                                                    def_none_)
                                                     -> raise
                                                        ((Matching err))
                                                 | (_, Sgn.Def_type a,
                                                    Sgn.Def_type a')
                                                     -> (TypeC
                                                         (redux a n s,
                                                          redux a' n' s'))
                                                 | (_, Sgn.Def_type a,
                                                    def_none_)
                                                     -> (TypeC
                                                         (redux a n s,
                                                          tRoot_ (n', s')))
                                                 | (_, def_none_,
                                                    Sgn.Def_type a')
                                                     -> (TypeC
                                                         (tRoot_ (n, s),
                                                          redux a' n' s'))
                                                 | _
                                                     -> raise
                                                        ((Matching
                                                          "invariant violation"))
                                            end in just_one' eq;;
                    (* PERF: this second elt_eroot_elim on elt' seems like it ought to be unnecessary if
	     I eliminate all eroots at synth time *);;
                    let rec matching p =
                      let rec matching' =
                        function 
                                 | ((c :: p), p')
                                     -> try let eqs = match_one c
                                              in matching' (eqs @ p, p')
                                        with 
                                             | NonPattern
                                                 -> matching' (p, (c :: p'))
                                 | ([], p') -> p'
                        in matching' (p, []);;
                    (*	fun ctxcons (a, G) = map (shift_tp 0) (a::G) *);;
                    let rec ctxcons (a, g_) = (a :: g_);;
                    type cg_mode = | Cg_synth 
                                   | Cg_check of tp ;;
                    (* 	val constraint_gen : tp list -> spine * tp * cg_mode -> eq_c list * tp_c list
        fun constraint_gen G (s, z, c) = (p, q, aopt) *);;
                    (* invariants: 
	   s is ground
	   if c is CG_CHECK c', then c' is ground 
           right-hand sides of p,q are ground
           left-hand sides of p,q and z may involve evars
           
           the returned aopt...
           ... is SOME of a type if c was CG_SYNTH
           ... is NONE           if c was CG_CHECK of something *);;
                    let rec constraint_gen g_ (s, z, c) =
                      constraint_gen' g_ (s, z, c)
                    and constraint_gen' arg__3 arg__4 =
                      begin
                      match (arg__3, arg__4)
                      with 
                           | (g_,
                              ([], (TRoot _ as a), Cg_check
                               ((TRoot _ as a'))))
                               -> ([(TypeC (a, a'))], [], None)
                           | (g_, ([], TRoot (n, s), Cg_synth))
                               -> ([], [], (Some (tRoot_ (n, s))))
                           | (g_, ((Omit :: s), TPi (omit_, a, z), c))
                               -> let ev : evar = (ref None, a)
                                    in let z' = subst_tp (eVarDotId_ ev) z
                                         in let (p, q, aa) =
                                              constraint_gen' g_ (s, z', c)
                                              in (p, q, aa)
                           | (g_, ((Elt m :: s), TPi (minus_, a, z), c))
                               -> let z' = subst_tp (termDot_ (m, a, Id)) z
                                    in let (p, q, aa) =
                                         constraint_gen' g_ (s, z', c)
                                         in (p, ((m, a) :: q), aa)
                           | (g_, ((AElt m :: s), TPi (plus_, a, z), c))
                               -> let a' = synth (g_, m)
                                    in let z' =
                                         subst_tp
                                         (termDot_ (aTerm_ m, a, Id))
                                         z
                                         in let (p, q, aa) =
                                              constraint_gen' g_ (s, z', c)
                                              in (((TypeC (a, a')) :: p), q,
                                                  aa)
                                              (* Same PERF comment here as above *)
                           | (g_,
                              ((Ascribe (m, a') :: s), TPi (plus_, a, z), c))
                               -> let z' =
                                    subst_tp (termDot_ (nTerm_ m, a, Id)) z
                                    in let (p, q, aa) =
                                         constraint_gen' g_ (s, z', c)
                                         in (((TypeC (a, a')) :: p), q, aa)
                                         (* As well as here *)
                           | (_, _)
                               -> raise ((Error "spine doesn't match type"))
                      end(* PERF: we might be able to reject this faster if we knew a and a'
                                         were not defined types and were different *)
                    and tp_constraint_gen arg__5 arg__6 =
                      begin
                      match (arg__5, arg__6)
                      with 
                           | (g_, ([], Type)) -> ([], [])
                           | (g_, ((Omit :: s), KPi (omit_, a, z)))
                               -> let ev : evar = (ref None, a)
                                    in let z' = subst_knd (eVarDotId_ ev) z
                                         in let (p, q) =
                                              tp_constraint_gen g_ (s, z')
                                              in (p, q)
                           | (g_, ((Elt m :: s), KPi (minus_, a, z)))
                               -> let z' = subst_knd (termDot_ (m, a, Id)) z
                                    in let (p, q) =
                                         tp_constraint_gen g_ (s, z')
                                         in (p, ((m, a) :: q))
                           | (g_, ((AElt m :: s), KPi (plus_, a, z)))
                               -> let a' = synth (g_, m)
                                    in let z' =
                                         subst_knd
                                         (termDot_ (aTerm_ m, a, Id))
                                         z
                                         in let (p, q) =
                                              tp_constraint_gen g_ (s, z')
                                              in (((TypeC (a, a')) :: p), q)
                           | (g_,
                              ((Ascribe (m, a') :: s), KPi (plus_, a, z)))
                               -> let z' =
                                    subst_knd (termDot_ (nTerm_ m, a, Id)) z
                                    in let (p, q) =
                                         tp_constraint_gen g_ (s, z')
                                         in (((TypeC (a, a')) :: p), q)
                           | (_, _)
                               -> raise ((Error "spine doesn't match type"))
                      end
                    and check_equality_constraints p = List.all eq_c_true p
                    and check_typing_constraints g_ q =
                      List.all (function 
                                         | (m, a) -> check (g_, m, a)) q
                    and matching_succeeds g_ (p, q) =
                      let p' = matching p
                        in let _ = begin
                             if check_equality_constraints p' then () else
                             raise
                             ((Matching
                               "residual equality constraints failed"))
                             end
                             in let _ = begin
                                  if check_typing_constraints g_ q then ()
                                  else
                                  raise
                                  ((Matching
                                    "residual typing constraints failed"))
                                  end in true
                                  (* evar side-effects affect q, raises Matching if matching fails *)
                    and check_spinelt =
                      function 
                               | (g_, Elt t, a) -> check (g_, t, a)
                               | (g_, AElt t, a) -> check (g_, aTerm_ t, a)
                               | (g_, Ascribe (t, a), a')
                                   -> (tp_eq (a, a')) &&
                                        (check (g_, nTerm_ t, a))
                               | (g_, Omit, _)
                                   -> raise
                                      ((Error
                                        "cannot check omitted arguments"))
                    and check =
                      function 
                               | (g_, NTerm (Lam t), TPi (_, a, b))
                                   -> check (ctxcons (a, g_), t, b)
                               | (g_, ATerm t, a)
                                   -> try tp_eq (synth (g_, t), a)
                                      with 
                                           | Error s -> false
                               | (g_, NTerm (NRoot (Const n, s)), a)
                                   -> let b =
                                        begin
                                        match Sgn.classifier n
                                        with 
                                             | Tclass_ b -> b
                                             | _
                                                 -> raise
                                                    ((Error
                                                      "signature invariant violated!"))
                                        end
                                        in let (p, q, _) =
                                             constraint_gen
                                             g_
                                             (s, b, (Cg_check a))
                                             in matching_succeeds g_ (p, q)
                                             (* creates ref cells for evars *)
                               | _ -> false
                    and check_kind =
                      function 
                               | (g_, Type) -> true
                               | (g_, KPi (omit_, a, k))
                                   -> (check_type Con_lf (g_, a)) &&
                                        ((check_kind (ctxcons (a, g_), k)) &&
                                           (Strict.check_strict_kind k))
                               | (g_, KPi (_, a, k))
                                   -> (check_type Con_lf (g_, a)) &&
                                        (check_kind (ctxcons (a, g_), k))
                    and check_type arg__7 arg__8 =
                      begin
                      match (arg__7, arg__8)
                      with 
                           | (_, (g_, TRoot (n, s)))
                               -> let k =
                                    begin
                                    match Sgn.classifier n
                                    with 
                                         | Kclass_ k -> k
                                         | _
                                             -> raise
                                                ((Error
                                                  "signature invariant violated!"))
                                    end
                                    in let (p, q) =
                                         tp_constraint_gen g_ (s, k)
                                         in matching_succeeds g_ (p, q)
                                         (* creates ref cells for evars *)
                           | (con, (g_, TPi (omit_, a, b)))
                               -> let plusconst =
                                    begin
                                    match con
                                    with 
                                         | Con_lf
                                             -> raise
                                                ((Error
                                                  "TPi(OMIT) where a pure LF function type expected"))
                                         | Con_plus -> true
                                         | Con_minus -> false
                                    end
                                    in (check_type Con_lf (g_, a)) &&
                                         ((check_type
                                           con
                                           (ctxcons (a, g_), b)) &&
                                            (Strict.check_strict_type
                                             plusconst
                                             b))
                           | (con, (g_, TPi (m, a, b)))
                               -> begin
                                  match (con, m)
                                  with 
                                       | (Con_lf, plus_)
                                           -> raise
                                              ((Error
                                                "TPi(PLUS) where a pure LF function type expected"))
                                       | _
                                           -> (check_type Con_lf (g_, a)) &&
                                                (check_type
                                                 con
                                                 (ctxcons (a, g_), b))
                                  end
                      end
                    and check_type' =
                      function 
                               | (g_, Type, []) -> true
                               | (g_, KPi (_, a, k), (m :: s))
                                   -> let _ = begin
                                        if check_spinelt (g_, m, a) then ()
                                        else
                                        raise
                                        ((Error "argument type mismatch"))
                                        end
                                        in let k' =
                                             subst_knd
                                             (termDot_ (termof m, a, Id))
                                             k in check_type' (g_, k', s)
                               | _ -> false
                    and synth =
                      function 
                               | (g_, ARoot (Var n, s))
                                   -> synth' (g_, ctxLookup (g_, n), s)
                               | (g_, ARoot (Const n, s))
                                   -> let b =
                                        begin
                                        match Sgn.classifier n
                                        with 
                                             | Tclass_ b -> b
                                             | _
                                                 -> raise
                                                    ((Error
                                                      "signature invariant violated!"))
                                        end
                                        in let (p, q, aopt) =
                                             constraint_gen
                                             g_
                                             (s, b, Cg_synth)
                                             in let _ =
                                                  matching_succeeds g_ (p, q)
                                                  in Option.valOf aopt
                                                  (* creates ref cells for evars *)(* DEBUG		 val _ = l3 := (p, q, aopt)::(!l3) *)(* raises Matching if not *)(* by invariant, aopt must be SOME *)
                               | (g_, (ERoot _ as t))
                                   -> elt_synth (g_, eroot_elim_plus t)
                    and synth' =
                      function 
                               | (g_, (TRoot (_, _) as a), []) -> a
                               | (g_, TPi (_, a, b), (m :: s))
                                   -> let _ = begin
                                        if check_spinelt (g_, m, a) then ()
                                        else
                                        raise
                                        ((Error "argument type mismatch"))
                                        end
                                        in let b' =
                                             subst_tp
                                             (termDot_ (termof m, a, Id))
                                             b in synth' (g_, b', s)
                               | _
                                   -> raise
                                      ((Error
                                        "applying nonfunction to argument"))
                    and elt_synth =
                      function 
                               | (g_, AElt t) -> synth (g_, t)
                               | (g_, Ascribe (t, a)) -> begin
                                   if check (g_, nTerm_ t, a) then a else
                                   raise ((Error "ascription doesn't check"))
                                   end
                               | (g_, Elt _)
                                   -> raise
                                      ((Error
                                        "trying to synthesize a merely checkable element"))
                               | (g_, Omit)
                                   -> raise
                                      ((Error
                                        "trying to synthesize an omitted argument"));;
                    (* similar to above but we just have a putative type and its kind, and return nothing but constraints *);;
                    (* returns true on success or raises Matching on failure *);;
                    (* check a type spine *);;
                    let rec check_plusconst_type t =
                      check_type Con_plus ([], t);;
                    let rec check_minusconst_type t =
                      check_type Con_minus ([], t);;
                    (* check_strictness_type : bool -> tp -> bool

   For a type B = Pi x1 : A1 . Pi x2 : A2 ... a . S (where the Pis
   may be omit or plus or minus) 
   and plus_const : bool
   the call
   check_strictness_type plus_const B
   returns true iff for every i, the following holds:
     the variable xi has either a strict occurrence in Aj for
     some j > i where xj is bound by a plus-Pi, or else 
     plus_const = false and xi has a strict occurrence in a . S.

  This function does *not* check to make sure types such as A1
  do not contain omit-Pis and plus-Pis. This test is carried
  out in check_type. check_strictness_type is useful mainly when
  we are simply deciding, by trial and error, which of the arguments
  to B we should omit and which to force to be synthesizing.
 *);;
                    let rec check_strictness_type arg__9 arg__10 =
                      begin
                      match (arg__9, arg__10)
                      with 
                           | (_, TRoot (n, s)) -> true
                           | (plusconst, TPi (omit_, _, b))
                               -> (check_strictness_type plusconst b) &&
                                    (Strict.check_strict_type plusconst b)
                           | (plusconst, TPi (_, _, b))
                               -> check_strictness_type plusconst b
                      end;;
                    let check_plusconst_strictness =
                      check_strictness_type true;;
                    let check_minusconst_strictness =
                      check_strictness_type false;;
                    end;;