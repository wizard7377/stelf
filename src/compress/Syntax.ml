(* # 1 "src/compress/Syntax.sig.ml" *)

(* # 1 "src/compress/Syntax.fun.ml" *)

(* # 1 "src/compress/Syntax.sml.ml" *)
open! Basis

module Syntax = struct
  exception Syntax of string
  exception MissingVar

  type mode = Minus | Plus | Omit

  type nterm = Lam of term | NRoot of (head * spine)
  and aterm = ARoot of (head * spine) | ERoot of (evar * subst)
  and head = Var of int | Const of int
  and tp = TRoot of (int * spine) | TPi of (mode * tp * tp)
  and knd = Type | KPi of (mode * tp * knd)
  and spinelt = Elt of term | AElt of aterm | Ascribe of (nterm * tp) | Omit
  and spine = spinelt list
  and term = NTerm of nterm | ATerm of aterm

  and subst =
    | Id
    | Shift of (int * int)
    | ZeroDotShift of subst
    | TermDot of (term * tp * subst)
    | EVarDot of (evar * subst list * subst)
    | VarOptDot of (int option * subst)
    | Compose of subst list

  and evar = term option ref * tp

  (* c^- *)
  (* c^+, x *)
  (* X[s] lowered to base type *)
  (*   M    *)
  (*  (R:)  *)
  (*  (N:A) *)
  (*   *    *)
  (* Shift n m = 0.1.2. ... .n-1.n+m.n+m+1.n+m+2. ... *)
  (* X[sl] . s *)
  (* special hack for type functions used only in tp_reduce *)
  type tpfn = TpfnType_ of tp | TpfnLam_ of tpfn

  let rec eVarDotId_ ev = EVarDot (ev, [], Id)

  (*	type decl = string * Parse.term *)
  (*	type ctx = decl list *)
  type class_ = Kclass_ of knd | Tclass_ of tp

  (* termof elm
        returns the term part of the spine element elm *)
  let rec termof = function
    | Elt t -> t
    | AElt t -> ATerm t
    | Ascribe (t, a) -> NTerm t
    | Omit ->
        raise
          (Syntax "invariant violated: arguments to variables cannot be omitted")

  type subst_result =
    | SrVar_ of int
    | SrTerm_ of (term * tp)
    | SrEVar_ of evar * subst list

  exception Debugs of subst_result * spinelt list

  let rec curryfoldr sf sl x = foldr (function s, x' -> sf s x') x sl

  (* lower (a, sp)
           supposing we have an evar of (potentially higher-order)
           type a, applied to a spine sp, return the lowered type of
           that evar and a substitution to apply it to *)
  (* XXX: so we're not carrying out substitutions over the type
                as we recurse down: is this right? I think it is. *)
  let rec lower arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | acc, ((TRoot _ as a), []) -> (a, acc)
    | acc, (TPi (m, a, b), elt :: sp) ->
        let newacc = TermDot (termof elt, subst_tp acc a, acc) in
        lower newacc (b, sp)
    | _, _ -> raise (Syntax "type mismatch in lowering")
    end
  (*
	  | lower base (TPi(m,a,b), elt::sp) = 
	    let
		val (aa,subst) = lower base (b, sp)
	    in
		(aa, TermDot(termof elt, a, subst))
	    end *)

  and substNth = function
    | Id, n -> SrVar_ n
    | ZeroDotShift s, n -> begin
        if n = 0 then SrVar_ 0
        else begin
          match substNth (s, n - 1) with
          | SrTerm_ (t, a) -> SrTerm_ (shift t, shift_tp 0 a)
          | SrVar_ n -> SrVar_ (n + 1)
          | SrEVar_ (ev, sl) -> SrEVar_ (ev, Shift (0, 1) :: sl)
        end
      end
    | TermDot (m, a, s), n -> begin
        if n = 0 then SrTerm_ (m, a) else substNth (s, n - 1)
      end
    | EVarDot (ev, sl, s), n -> begin
        if n = 0 then SrEVar_ (ev, sl) else substNth (s, n - 1)
      end
    | Shift (n, m), n' -> begin
        if n' >= n then SrVar_ (n' + m) else SrVar_ n'
      end
    | VarOptDot (no, s), n' -> begin
        if n' = 0 then begin
          match no with Some n -> SrVar_ n | None -> raise MissingVar
        end
        else substNth (s, n' - 1)
      end
    | Compose [], n -> SrVar_ n
    | Compose (h :: tl), n -> subst_sr h (substNth (Compose tl, n))

  and subst_sr arg__2 arg__3 =
    begin match (arg__2, arg__3) with
    | s, SrTerm_ (t, a) -> SrTerm_ (subst_term s t, subst_tp s a)
    | s, SrVar_ n -> substNth (s, n)
    | s, SrEVar_ (ev, sl) -> SrEVar_ (ev, s :: sl)
    end

  and subst_spinelt arg__4 arg__5 =
    begin match (arg__4, arg__5) with
    | Id, x -> x
    | s, Elt t -> Elt (subst_term s t)
    | s, AElt t -> subst_aterm_plus s t
    | s, Ascribe (t, a) -> Ascribe (subst_nterm s t, subst_tp s a)
    | s, Omit -> Omit
    end

  and subst_spine s sp = map (subst_spinelt s) sp

  and subst_term arg__6 arg__7 =
    begin match (arg__6, arg__7) with
    | s, ATerm t -> subst_aterm s t
    | s, NTerm t -> NTerm (subst_nterm s t)
    end

  and subst_nterm arg__8 arg__9 =
    begin match (arg__8, arg__9) with
    | s, Lam t -> Lam (subst_term (ZeroDotShift s) t)
    | s, NRoot (h, sp) -> NRoot (h, subst_spine s sp)
    end

  and subst_aterm arg__10 arg__11 =
    begin match (arg__10, arg__11) with
    | s, ARoot (Const n, sp) -> ATerm (ARoot (Const n, subst_spine s sp))
    | s, ARoot (Var n, sp) -> reduce (substNth (s, n), subst_spine s sp)
    | s, ERoot ((({ contents = None }, _) as ev), sl) ->
        ATerm (ERoot (ev, subst_compose (s, sl)))
    | s, (ERoot _ as t) -> subst_term s (eroot_elim t)
    end
  (* XXX right??? *)

  and subst_aterm_plus arg__12 arg__13 =
    begin match (arg__12, arg__13) with
    | s, ARoot (Const n, sp) -> AElt (ARoot (Const n, subst_spine s sp))
    | s, ARoot (Var n, sp) -> reduce_plus (substNth (s, n), subst_spine s sp)
    | s, ERoot ((({ contents = None }, _) as ev), sl) ->
        AElt (ERoot (ev, subst_compose (s, sl)))
    | s, (ERoot _ as t) -> subst_spinelt s (eroot_elim_plus t)
    end

  and subst_tp arg__14 arg__15 =
    begin match (arg__14, arg__15) with
    | s, TRoot (h, sp) -> TRoot (h, subst_spine s sp)
    | s, TPi (m, b, b') -> TPi (m, subst_tp s b, subst_tp (ZeroDotShift s) b')
    end

  and subst_knd arg__16 arg__17 =
    begin match (arg__16, arg__17) with
    | s, Type -> Type
    | s, KPi (m, b, k) -> KPi (m, subst_tp s b, subst_knd (ZeroDotShift s) k)
    end

  and reduce = function
    | SrVar_ n, sp -> ATerm (ARoot (Var n, sp))
    | SrTerm_ (NTerm (Lam n), TPi (_, a, b)), h :: sp ->
        let s = TermDot (termof h, a, Id) in
        let n' = subst_term s n in
        let b' = subst_tp s b in
        reduce (SrTerm_ (n', b'), sp)
    | SrTerm_ ((NTerm (NRoot (h, sp)) as t), a), [] -> t
    | SrTerm_ ((ATerm (ARoot (h, sp)) as t), a), [] -> t
    | SrTerm_ (ATerm (ERoot (({ contents = Some _ }, _), _) as t), a), [] ->
        reduce (SrTerm_ (eroot_elim t, a), [])
    | SrTerm_ (ATerm (ERoot (({ contents = None }, _), _) as t), a), [] ->
        ATerm t
    | SrEVar_ ((x, a), sl), sp ->
        let a', subst = lower (substs_comp sl) (a, sp) in
        ATerm (ERoot ((x, a'), subst))
    | _ -> raise (Syntax "simplified-type mismatch in reduction")

  and reduce_plus = function
    | SrVar_ n, sp -> AElt (ARoot (Var n, sp))
    | SrTerm_ (NTerm (Lam n), TPi (_, a, b)), h :: sp ->
        let s = TermDot (termof h, a, Id) in
        let n' = subst_term s n in
        let b' = subst_tp s b in
        reduce_plus (SrTerm_ (n', b'), sp)
    | SrTerm_ (NTerm (NRoot (h, sp) as t), a), [] -> Ascribe (t, a)
    | SrTerm_ (ATerm (ARoot (h, sp) as t), a), [] -> AElt t
    | SrTerm_ (ATerm (ERoot (({ contents = Some _ }, _), _) as t), a), [] ->
        reduce_plus (SrTerm_ (eroot_elim t, a), [])
    | SrTerm_ (ATerm (ERoot (({ contents = None }, _), _) as t), a), [] ->
        AElt t
    | SrEVar_ ((x, a), sl), sp ->
        let a', subst = lower (substs_comp sl) (a, sp) in
        AElt (ERoot ((x, a'), subst))
    | x, y -> begin
        raise (Debugs (x, y));
        raise (Syntax "simplified-type mismatch in reduction")
      end

  and tp_reduce (a, k, sp) =
    let rec subst_tpfn arg__18 arg__19 =
      begin match (arg__18, arg__19) with
      | s, TpfnLam_ a -> TpfnLam_ (subst_tpfn (ZeroDotShift s) a)
      | s, TpfnType_ a -> TpfnType_ (subst_tp s a)
      end
    in
    let rec tp_reduce' = function
      | TpfnLam_ a, KPi (_, b, k), h :: sp ->
          let s = TermDot (termof h, b, Id) in
          let a' = subst_tpfn s a in
          let k' = subst_knd s k in
          tp_reduce' (a', k', sp)
      | TpfnType_ a, Type, [] -> a
      | _ -> raise (Syntax "simplified-kind mismatch in type reduction")
    in
    let rec wrap = function
      | a, KPi (_, b, k) -> TpfnLam_ (wrap (a, k))
      | a, Type -> TpfnType_ a
    in
    let aw = wrap (a, k) in
    tp_reduce' (aw, k, sp)

  and substs_term x = curryfoldr subst_term x
  and substs_tp x = curryfoldr subst_tp x

  and eroot_elim = function
    | ERoot (({ contents = Some t }, a), subst) -> subst_term subst t
    | x -> ATerm x

  and eroot_elim_plus = function
    | ERoot (({ contents = Some t }, a), subst) ->
        let newt = subst_term subst t in
        begin match newt with
        | ATerm t -> AElt t
        | NTerm t -> Ascribe (t, subst_tp subst a)
        end
    | x -> AElt x

  and composeNth (s, n, s') =
    let s'' = subst_compose (s, s') in
    begin match substNth (s, n) with
    | SrVar_ n' -> VarOptDot (Some n', s'')
    | SrTerm_ (t, a) -> TermDot (t, a, s'')
    | SrEVar_ (ev, sl) -> EVarDot (ev, sl, s'')
    end

  and subst_compose = function
    | Id, s -> s
    | s, Id -> s
    | s, Shift (_, 0) -> s
    | Shift (_, 0), s -> s
    | s, Compose [] -> s
    | Compose [], s -> s
    | s, Compose (h :: tl) -> subst_compose (subst_compose (s, h), Compose tl)
    | Compose (h :: tl), s -> subst_compose (h, subst_compose (Compose tl, s))
    | ZeroDotShift s, Shift (0, m) ->
        subst_compose (subst_compose (Shift (0, 1), s), Shift (0, m - 1))
    | TermDot (_, _, s), Shift (0, m) -> subst_compose (s, Shift (0, m - 1))
    | EVarDot (_, _, s), Shift (0, m) -> subst_compose (s, Shift (0, m - 1))
    | VarOptDot (_, s), Shift (0, m) -> subst_compose (s, Shift (0, m - 1))
    | Shift (0, m), Shift (0, m') -> Shift (0, m + m')
    | Shift (n, m'), (Shift (0, m) as t) ->
        subst_compose (ZeroDotShift (Shift (n - 1, m')), t)
    | s, Shift (n, m) -> subst_compose (s, ZeroDotShift (Shift (n - 1, m)))
    | s, ZeroDotShift s' -> composeNth (s, 0, subst_compose (Shift (0, 1), s'))
    | s, TermDot (t, a, s') ->
        TermDot (subst_term s t, subst_tp s a, subst_compose (s, s'))
    | s, EVarDot (ev, sl, s') -> EVarDot (ev, s :: sl, subst_compose (s, s'))
    | s, VarOptDot (no, s') -> begin
        match no with
        | None -> VarOptDot (None, subst_compose (s, s'))
        | Some n -> composeNth (s, n, s')
      end
  (* ZeroDotShift (Shift (n-1,m)) = Shift(n,m) but the former is 'smaller' *)

  and shift t = shift_term 0 t

  and shift_nterm arg__20 arg__21 =
    begin match (arg__20, arg__21) with
    | n, Lam t -> Lam (shift_term (n + 1) t)
    | n, NRoot (h, sp) -> NRoot (h, shift_spine n sp)
    end

  and shift_aterm arg__22 arg__23 =
    begin match (arg__22, arg__23) with
    | n, ARoot (Const n', sp) -> ARoot (Const n', shift_spine n sp)
    | n, ERoot (ev, sl) -> ERoot (ev, subst_compose (Shift (n, 1), sl))
    | n, ARoot (Var n', sp) ->
        let sp' = shift_spine n sp in
        begin if n' >= n then ARoot (Var (n' + 1), sp') else ARoot (Var n', sp')
        end
    end

  and shift_spinelt arg__24 arg__25 =
    begin match (arg__24, arg__25) with
    | n, Elt (ATerm t) -> Elt (ATerm (shift_aterm n t))
    | n, Elt (NTerm t) -> Elt (NTerm (shift_nterm n t))
    | n, AElt t -> AElt (shift_aterm n t)
    | n, Ascribe (t, a) -> Ascribe (shift_nterm n t, shift_tp n a)
    | n, Omit -> Omit
    end

  and shift_spine n = map (shift_spinelt n)

  and shift_tp arg__26 arg__27 =
    begin match (arg__26, arg__27) with
    | n, TPi (m, a, b) -> TPi (m, shift_tp n a, shift_tp (n + 1) b)
    | n, TRoot (h, sp) -> TRoot (h, shift_spine n sp)
    end

  and shift_term arg__28 arg__29 =
    begin match (arg__28, arg__29) with
    | n, NTerm t -> NTerm (shift_nterm n t)
    | n, ATerm t -> ATerm (shift_aterm n t)
    end

  and substs_comp sl = foldr subst_compose Id sl

  (* substNth (subst, n)
        returns the result of applying the substitution subst
        to the index n *)
  (* the type of the evar is understood to be
							        affected by the subst as well *)
  (* XXX right??? *)
  (* val tp_reduce : tp * knd * spine -> tp
           tp_reduce (a, k, sp) computes the result
           of reducing (.\ .\ ... .\ a) . sp
           assuming (.\ .\ ... .\ a) : k
           (where the number of lambdas is the number
            of pis found in k) 
        *)
  (* elt_eroot_elim e
        returns a spine element equal to e but makes sure that it's not
        an instatiated ERoot. That is, it carries out the instantiation
        and substitutions involved therein. *)
  (* probably not the right way to do things considering I have Compose *)
  (* YYY: the following doesn't avoid incurring polyequal. why??? 

	datatype foo =
	        Foo of baralias
	     and bar =
	        Bar of foo 
	withtype baralias = bar;

        - fn (x : foo, y : foo) => x = y;
        stdIn:376.28 Warning: calling polyEqual
        val it = fn : foo * foo -> bool

        doesn't really matter anymore to this code, (it used to)
        but I'm still curious.
        *)
  (* compute [s]n . (s o s') *)
  (* val subst_compose : subst * subst -> subst *)
  (* shift_[...] n t
        shifts all deBruijn indices in the object t by one, as long
        as they refer to positions in the current context 
        greater than or equal to n. *)
  let rec elt_eroot_elim = function
    | AElt t -> eroot_elim_plus t
    | Elt (ATerm t) -> Elt (eroot_elim t)
    | x -> x

  let rec ntm_eroot_elim = function
    | Lam (ATerm t) -> Lam (eroot_elim t)
    | x -> x

  let rec ctxLookup (g_, n) = subst_tp (Shift (0, n + 1)) (List.nth (g_, n))
  let rec typeOf (Tclass_ a) = a
  let rec kindOf (Kclass_ k) = k
  let sum = foldl (fun (x__op, y__op) -> x__op + y__op) 0

  let rec size_term = function
    | NTerm (Lam t) -> 1 + size_term t
    | NTerm (NRoot (_, s)) -> 1 + size_spine s
    | ATerm (ARoot (_, s)) -> 1 + size_spine s
    | ATerm (ERoot _) -> 1

  and size_spine s = sum (map size_spinelt s)

  and size_spinelt = function
    | Elt t -> size_term t
    | AElt t -> size_term (ATerm t)
    | Ascribe (t, a) -> size_term (NTerm t) + size_tp a
    | Omit -> 0

  and size_tp = function
    | TRoot (_, s) -> 1 + size_spine s
    | TPi (_, a, b) -> 1 + size_tp a + size_tp b

  and size_knd = function
    | Type -> 1
    | KPi (_, a, b) -> 1 + size_tp a + size_knd b

  (* convert a kind to a context of all the pi-bound variables in it *)
  let rec explodeKind = function
    | Type -> []
    | KPi (_, a, k) -> explodeKind k @ [ a ]
end

include Syntax
