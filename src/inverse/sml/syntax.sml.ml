open! Timers
open! Signat
open! Basis

module Syntax : SYNTAX = struct
  module L = Lib

  type nonrec const = int
  type uni = Type | Kind
  type head = Const of const | BVar of int
  type depend = No | Maybe

  type exp =
    | Uni of uni
    | Pi of pi
    | Lam of lam
    | Root of head * spine
    | Redex of exp * spine
    | EClo of exp * sub

  and spine = Nil | App of exp * spine | SClo of spine * sub
  and sub = Dot of exp * sub | Shift of int | Comp of sub * sub

  type nonrec __0 = {
    var : string option;
    arg : exp;
    depend : depend;
    body : exp;
  }

  type nonrec __1 = { var : string option; body : exp }

  type pi = __0
  and lam = __1

  type nonrec __2 = { id : const; name : string; exp : exp; uni : uni }
  type nonrec decl = __2

  type nonrec __3 = {
    id : const;
    name : string;
    exp : exp;
    def : exp;
    height : int;
    root : const;
    uni : uni;
  }

  type nonrec def = __3

  type nonrec __4 = {
    id : const;
    name : string;
    exp : exp;
    def : exp;
    uni : uni;
  }

  type nonrec abbrev = __4
  type dec = Decl of decl | Def of def | Abbrev of abbrev

  (* -------------------------------------------------------------------------- *)
  (*  Signatures                                                                *)
  (* -------------------------------------------------------------------------- *)
  module Signat = struct
    module T = Table

    type nonrec signat = dec T.table

    let global_signat : dec T.table = T.table 100000
    let rec lookup c = T.lookup global_signat c
    let rec insert (c, d) = ignore (T.insert global_signat (c, d))
    let rec app f = T.appi f global_signat
    let rec size () = T.size global_signat
    let rec reset () = T.clear global_signat
  end

  module Sig = Signat

  (* -------------------------------------------------------------------------- *)
  (*  Util                                                                      *)
  (* -------------------------------------------------------------------------- *)
  let expType = Uni Type
  let expKind = Uni Kind
  let rec bvar n = Root (BVar n, Nil)
  let one = Bvar_ 1
  let shift = Shift 1
  let id_sub = Shift 0

  let rec id = function
    | Decl decl -> (fun r -> r.id) decl
    | Def def -> (fun r -> r.id) def
    | Abbrev abb -> (fun r -> r.id) abb

  let rec name = function
    | Decl decl -> (fun r -> r.name) decl
    | Def def -> (fun r -> r.name) def
    | Abbrev abb -> (fun r -> r.name) abb

  let rec exp = function
    | Decl decl -> (fun r -> r.exp) decl
    | Def def -> (fun r -> r.exp) def
    | Abbrev abb -> (fun r -> r.exp) abb

  let rec is_def c =
    begin match Signat.lookup c with
    | Def _ -> true
    | Abbrev _ -> true
    | Decl _ -> false
    end

  let rec def c =
    begin match Signat.lookup c with
    | Def def -> (fun r -> r.def) def
    | Abbrev abb -> (fun r -> r.def) abb
    | Decl _ -> raise (Fail "def: not a def")
    end

  (* -------------------------------------------------------------------------- *)
  (*  Exceptions                                                                *)
  (* -------------------------------------------------------------------------- *)
  exception Fail_exp of string * exp
  exception Fail_exp2 of string * exp * exp
  exception Fail_exp_spine of string * exp * spine
  exception Fail_spine_exp of string * spine * exp
  exception Fail_hd_spine of string * head * spine
  exception Fail_sub_exp of string * sub * exp
  exception Fail_sub_exp of string * sub * exp

  (* -------------------------------------------------------------------------- *)
  (*  Eta                                                                       *)
  (* -------------------------------------------------------------------------- *)
  type skel = Base | Arrow of skel * skel

  let rec card = function
    | Nil -> 0
    | App (m_, s_) -> 1 + card s_
    | _ -> raise (Fail "card: no closures")

  let rec num_pi_quants = function
    | Pi { body } -> 1 + num_pi_quants body
    | _ -> 0

  let rec skel_length = function
    | Base -> 0
    | Arrow (_, tau) -> 1 + skel_length tau

  let rec concat = function
    | Nil, m_ -> App (m_, Nil)
    | App (m_, s_), m'_ -> App (m_, concat (s_, m'_))
    | SClo _, _ -> raise (Fail "concat: no closures")

  let rec skeleton = function
    | ctx, Uni Type -> Base
    | ctx, Root (Const a, s_) ->
        let aty = exp (Sig.lookup a) in
        let n = num_pi_quants aty in
        let n' = card s_ in
        begin if n = n' then Base else raise (Fail "skeleton: not eta expanded")
        end
    | ctx, Root (BVar i, s_) ->
        let aty = L.ith (i - 1) ctx in
        let n = skel_length aty in
        let n' = card s_ in
        begin if n = n' then Base else raise (Fail "skeleton: not eta expanded")
        end
    | ctx, Pi { arg; body } ->
        let tau1 = skeleton (ctx, arg) in
        let tau2 = skeleton (ctx, body) in
        Arrow (tau1, tau2)
    | _, exp -> raise (Fail_exp ("skeleton: bad case", exp))

  exception Fail_exp_skel of string * exp * skel

  open! struct
    let changed = ref false
  end

  (* A quick implementation of applying a shift substitution. 
       This is just for eta expansion, and we don't want this
       code to be tangled with the different typechecker versions.
    *)
  let rec shift_head = function
    | lev, (Const _ as con) -> con
    | lev, (BVar n as var) -> begin if n >= lev then BVar (n + 1) else var end

  let rec shift_spine = function
    | lev, Nil -> Nil
    | lev, App (m_, s_) -> App (shift_exp (lev, m_), shift_spine (lev, s_))
    | lev, SClo _ ->
        raise (Fail "shift_spine: shouldn't have closures during eta expansion")

  and shift_exp = function
    | lev, (Uni _ as uni) -> uni
    | lev, Pi { var; arg; depend; body } ->
        Pi
          {
            var;
            arg = shift_exp (lev, arg);
            depend;
            body = shift_exp (lev + 1, body);
          }
    | lev, Lam { var; body } -> Lam { var; body = shift_exp (lev + 1, body) }
    | lev, Root (h_, s_) -> Root (shift_head (lev, h_), shift_spine (lev, s_))
    | _ ->
        raise
          (Fail
             "shift_exp: shouldn't have redexes or closures during eta \
              expansion")

  let rec shift_spine' exp = shift_spine (0, exp)

  let rec long_exp = function
    | ctx, (Uni Type as exp), Base -> exp
    | ctx, Pi { arg; body; depend; var }, Base ->
        let arg' = long_exp (ctx, arg, Base) in
        let tau = skeleton (ctx, arg') in
        let body' = long_exp (tau :: ctx, body, Base) in
        Pi { arg = arg'; body = body'; depend; var }
    | ctx, Lam { var; body }, Arrow (tau1, tau2) ->
        let body' = long_exp (tau1 :: ctx, body, tau2) in
        Lam { var; body = body' }
    | ctx, (Root ((Const a as con), s_) as expr), Base ->
        let tau = skeleton (ctx, exp (Sig.lookup a)) in
        Root (con, long_spine (ctx, s_, tau))
    | ctx, (Root ((BVar i as var), s_) as exp), Base ->
        let tau = L.ith (i - 1) ctx in
        Root (var, long_spine (ctx, s_, tau))
        (* indices start at 1 *)
    | ctx, Root ((Const c as con), s_), (Arrow (tau1, tau2) as tau) ->
        let s'_ = concat (shift_spine' s_, one) in
        begin
          changed := true;
          long_exp (ctx, Lam { var = None; body = Root (con, s'_) }, tau)
        end
    | ctx, Root (BVar i, s_), (Arrow (tau1, tau2) as tau) ->
        let s'_ = concat (shift_spine' s_, one) in
        begin
          changed := true;
          long_exp
            (ctx, Lam { var = None; body = Root (BVar (i + 1), s'_) }, tau)
        end
    | _, exp, skel -> raise (Fail_exp_skel ("long_exp: bad case", exp, skel))

  and long_spine = function
    | ctx, Nil, Base -> Nil
    | ctx, App (m_, s_), Arrow (tau1, tau2) ->
        let m'_ = long_exp (ctx, m_, tau1) in
        let s'_ = long_spine (ctx, s_, tau2) in
        App (m'_, s'_)
    | _ -> raise (Fail "long_spine: bad case")

  let rec eta_expand' = function
    | e1, Uni Kind -> e1
    | e1, e2 ->
        let () = changed := false in
        let skel = skeleton ([], e2) in
        let e2' = long_exp ([], e1, skel) in
        e2'
  (*           if !changed then L.warning ""expression is not eta long"" else (); *)

  let rec eta_expand e = Timers.time Timers.eta_normal eta_expand' e
end
