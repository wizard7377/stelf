# 1 "src/meta/print.sig.ml"
open! Basis;;
(* Meta Printer Version 1.3 *);;
(* Author: Carsten Schuermann *);;
module type MTPRINT = sig
                      module Formatter : FORMATTER
                      module StateSyn : STATESYN
                      exception Error of string 
                      val nameState : StateSyn.state_ -> StateSyn.state_
                      val formatState : StateSyn.state_ -> Formatter.format
                      val stateToString : StateSyn.state_ -> string
                      end;;
(* signature MTPRINT *);;
# 1 "src/meta/print.fun.ml"
open! Global;;
open! Basis;;
module MTPrint(MTPrint__0: sig
                           (* Meta Printer Version 1.3 *)
                           (* Author: Carsten Schuermann *)
                           module Global : GLOBAL
                           (*! structure IntSyn : INTSYN !*)
                           (*! structure FunSyn : FUNSYN !*)
                           (*! sharing FunSyn.IntSyn = IntSyn !*)
                           module Names : NAMES
                           (*! sharing Names.IntSyn = IntSyn !*)
                           module StateSyn' : STATESYN
                           (*! sharing StateSyn'.FunSyn = FunSyn !*)
                           (*! sharing StateSyn'.IntSyn = IntSyn !*)
                           module Formatter' : FORMATTER
                           module Print : PRINT
                           (*! sharing Print.IntSyn = IntSyn !*)
                           module FunPrint : FUNPRINT
                           end) : MTPRINT
  =
  struct
    module Formatter = Formatter';;
    module StateSyn = StateSyn';;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module N = Names;;
        module S = StateSyn;;
        module Fmt = Formatter;;
        let rec nameState (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_))
          =
          let _ = Names.varReset I.null_
            in let g'_ = Names.ctxName g_
                 in (S.State (n, (g'_, b_), (ih_, oh_), d, o_, h_, f_));;
        let rec formatOrder =
          function 
                   | (g_, S.Arg (us_, vs_))
                       -> [Print.formatExp (g_, (I.EClo us_));
                           (Fmt.String ":");
                           Print.formatExp (g_, (I.EClo vs_))]
                   | (g_, S.Lex os_)
                       -> [(Fmt.String "{");
                           (Fmt.HVbox0 (1, 0, 1, formatOrders (g_, os_)));
                           (Fmt.String "}")]
                   | (g_, S.Simul os_)
                       -> [(Fmt.String "[");
                           (Fmt.HVbox0 (1, 0, 1, formatOrders (g_, os_)));
                           (Fmt.String "]")]
        and formatOrders =
          function 
                   | (g_, []) -> []
                   | (g_, (o_ :: [])) -> formatOrder (g_, o_)
                   | (g_, (o_ :: os_))
                       -> (formatOrder (g_, o_)) @
                            ([(Fmt.String ","); Fmt.break_] @
                               (formatOrders (g_, os_)));;
        let rec formatTag =
          function 
                   | (g_, S.Parameter l) -> [(Fmt.String "<p>")]
                   | (g_, S.Lemma (S.Splits k))
                       -> [(Fmt.String "<i"); (Fmt.String (Int.toString k));
                           (Fmt.String ">")]
                   | (g_, S.Lemma rl_) -> [(Fmt.String "<i >")]
                   | (g_, S.Lemma rLdone_) -> [(Fmt.String "<i*>")];;
        let rec formatCtx =
          function 
                   | (null_, b_) -> []
                   | (I.Decl (null_, d_), I.Decl (null_, T)) -> begin
                       if (! Global.chatter) >= 4 then
                       [(Fmt.HVbox
                         ((formatTag (I.null_, T)) @
                            [Fmt.break_; Print.formatDec (I.null_, d_)]))]
                       else [Print.formatDec (I.null_, d_)] end
                   | (I.Decl (g_, d_), I.Decl (b_, T)) -> begin
                       if (! Global.chatter) >= 4 then
                       (formatCtx (g_, b_)) @
                         ([(Fmt.String ","); Fmt.break_; Fmt.break_] @
                            [(Fmt.HVbox
                              ((formatTag (g_, T)) @
                                 [Fmt.break_; Print.formatDec (g_, d_)]))])
                       else
                       (formatCtx (g_, b_)) @
                         ([(Fmt.String ","); Fmt.break_] @
                            [Fmt.break_; Print.formatDec (g_, d_)])
                       end;;
        let rec formatState
          (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_)) =
          (Fmt.Vbox0
           (0, 1,
            [(Fmt.HVbox0 (1, 0, 1, formatOrder (g_, o_))); Fmt.break_;
             (Fmt.String "========================"); Fmt.break_;
             (Fmt.HVbox0 (1, 0, 1, formatCtx (g_, b_))); Fmt.break_;
             (Fmt.String "------------------------"); Fmt.break_;
             FunPrint.formatForBare (g_, f_)]));;
        let rec stateToString s_ = Fmt.makestring_fmt (formatState s_);;
        end;;
    (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *);;
    (* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *);;
    (*      | formatTag (G, S.Assumption k) = [Fmt.String ""<a"",
                                         Fmt.String (Int.toString k),
                                         Fmt.String "">""] *);;
    (* formatCtx (G, B) = fmt'

       Invariant:
       If   |- G ctx       and G is already named
       and  |- B : G tags
       then fmt' is a format describing the context (G, B)
    *);;
    (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *);;
    (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *);;
    let nameState = nameState;;
    let formatState = formatState;;
    let stateToString = stateToString;;
    end;;
(*! sharing FunPrint.FunSyn = FunSyn !*);;
(* local *);;
(* functor MTPrint *);;
# 1 "src/meta/print.sml.ml"
