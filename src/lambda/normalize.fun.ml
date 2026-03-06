open! Whnf;;
open! Basis;;
(* Internal syntax for functional proof term calculus *);;
(* Author: Carsten Schuermann *);;
module Normalize(Normalize__0: sig module Whnf : WHNF end) : NORMALIZE =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure Tomega = Tomega' !*);;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module T = Tomega;;
        let rec normalizeFor =
          function 
                   | (T.All ((d_, q_), f_), t)
                       -> (T.All
                           ((T.decSub (d_, t), q_),
                            normalizeFor (f_, T.dot1 t)))
                   | (T.Ex ((d_, q_), f_), t)
                       -> (T.Ex
                           ((I.decSub (d_, T.coerceSub t), q_),
                            normalizeFor (f_, T.dot1 t)))
                   | (T.And (f1_, f2_), t)
                       -> (T.And
                           (normalizeFor (f1_, t), normalizeFor (f2_, t)))
                   | (T.FClo (f_, t1), t2)
                       -> normalizeFor (f_, T.comp (t1, t2))
                   | (T.World (w_, f_), t)
                       -> (T.World (w_, normalizeFor (f_, t)))
                   | (true_, _) -> T.true_;;
        let rec whnfFor =
          function 
                   | ((T.All (d_, _), t) as ft_) -> ft_
                   | ((T.Ex (d_, f_), t) as ft_) -> ft_
                   | ((T.And (f1_, f2_), t) as ft_) -> ft_
                   | (T.FClo (f_, t1), t2) -> whnfFor (f_, T.comp (t1, t2))
                   | ((T.World (w_, f_), t) as ft_) -> ft_
                   | ((true_, _) as ft_) -> ft_;;
        let rec normalizePrg =
          function 
                   | (T.Var n, t)
                       -> begin
                          match T.varSub (n, t)
                          with 
                               | T.Prg p_ -> p_
                               | T.Idx _ -> raise Domain
                               | T.Exp _ -> raise Domain
                               | T.Block _ -> raise Domain
                               | undef_ -> raise Domain
                          end
                   | (T.PairExp (u_, p'_), t)
                       -> (T.PairExp
                           (Whnf.normalize (u_, T.coerceSub t),
                            normalizePrg (p'_, t)))
                   | (T.PairBlock (b_, p'_), t)
                       -> (T.PairBlock
                           (I.blockSub (b_, T.coerceSub t),
                            normalizePrg (p'_, t)))
                   | (T.PairPrg (p1_, p2_), t)
                       -> (T.PairPrg
                           (normalizePrg (p1_, t), normalizePrg (p2_, t)))
                   | (unit_, _) -> T.unit_
                   | (T.EVar (_, { contents = Some p_}, _), t)
                       -> (T.PClo (p_, t))
                   | ((T.EVar _ as p_), t) -> (T.PClo (p_, t))
                   | (T.PClo (p_, t), t')
                       -> normalizePrg (p_, T.comp (t, t'))
        and normalizeSpine =
          function 
                   | (nil_, t) -> T.nil_
                   | (T.AppExp (u_, s_), t)
                       -> (T.AppExp
                           (Whnf.normalize (u_, T.coerceSub t),
                            normalizeSpine (s_, t)))
                   | (T.AppPrg (p_, s_), t)
                       -> (T.AppPrg
                           (normalizePrg (p_, t), normalizeSpine (s_, t)))
                   | (T.AppBlock (b_, s_), t)
                       -> (T.AppBlock
                           (I.blockSub (b_, T.coerceSub t),
                            normalizeSpine (s_, t)))
                   | (T.SClo (s_, t1), t2)
                       -> normalizeSpine (s_, T.comp (t1, t2));;
        let rec normalizeSub =
          function 
                   | (T.Shift n as s) -> s
                   | T.Dot (T.Prg p_, s)
                       -> (T.Dot
                           ((T.Prg (normalizePrg (p_, T.id))),
                            normalizeSub s))
                   | T.Dot (T.Exp e_, s)
                       -> (T.Dot
                           ((T.Exp (Whnf.normalize (e_, I.id))),
                            normalizeSub s))
                   | T.Dot (T.Block k, s)
                       -> (T.Dot ((T.Block k), normalizeSub s))
                   | T.Dot (T.Idx k, s)
                       -> (T.Dot ((T.Idx k), normalizeSub s));;
        end;;
    (*      | normalizeFor (T.FVar (G, r))   think about it *);;
    (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *);;
    (* ABP -- 1/20/03 *);;
    (* ABP *);;
    (*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
      | normalizeDec (T.BDec (k, t1), t2) = 
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*);;
    let normalizeFor = normalizeFor;;
    let normalizePrg = normalizePrg;;
    let normalizeSub = normalizeSub;;
    let whnfFor = whnfFor;;
    end;;
(*! structure IntSyn' : INTSYN !*);;
(*! structure Tomega' : TOMEGA !*);;
(*! sharing Tomega'.IntSyn = IntSyn' !*);;
(*! sharing Whnf.IntSyn = IntSyn' !*);;