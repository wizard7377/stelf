open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_
open! Print.Print_

(* # 1 "src/meta/Init.sig.ml" *)
open Funsyn
open Statesyn
open MtpGlobal
open MtpData
open Funprint

(* Initialization *)
(* Author: Carsten Schuermann *)
include MTPINIT
(* signature MTPINIT *)

(* # 1 "src/meta/Init.fun.ml" *)
open! Basis

(* Initialization *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPInit (MTPInit__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module MTPData : MTPDATA.MTPDATA

  (*! structure IntSyn : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Formatter : FORMATTER
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunPrint : FUNPRINT.FUNPRINT
end) : MTPINIT.MTPINIT = struct
  (*! structure FunSyn = FunSyn' !*)
  open MTPInit__0
  module StateSyn = StateSyn'

  exception Error = Error

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter

    let init f_ of_ =
      let rec init' (gb, a, b, ss_) = match gb, a, b with
        | (g_, b_), S.All (_, o_), F.All (F.Prim d_, f'_) ->
            let d'_ = Names.decName g_ d_ in
            init'
              ( ( I.Decl (g_, d'_),
                  I.Decl (b_, S.Lemma (S.Splits !MTPGlobal.maxSplit)) ),
                o_,
                f'_,
                ss_ )
        | gb, S.And (o1_, o2_), F.And (f1_, f2_) ->
            init' (gb, o1_, f1_, init' (gb, o2_, f2_, ss_))
        | gb, o_, (F.Ex _ as f'_) ->
            S.State (List.length ss_ + 1, gb, (f_, of_), 1, o_, [], f'_) :: ss_
        | gb, o_, (True as f'_) ->
            S.State (List.length ss_ + 1, gb, (f_, of_), 1, o_, [], f'_) :: ss_
      in
      Names.varReset I.Null;
      begin
        MTPData.maxFill := 0;
        init' ((I.Null, I.Null), of_, f_, [])
      end
  end

  (* init (F, OF) = Ss'

       Invariant:
       If   . |- F formula    and   F in nf
       and  . |- OF order
       then Ss' is a list of initial states for the theorem prover
    *)
  (* it is possible to calculuate
                 index/induction variable information here
                 define occursOrder in StateSyn.fun  --cs *)
  (*      | init' (G, B, O, (F.All (F.Block _, F), s)) =
           no such case yet  --cs *)
  (* added in case there are no existentials -fp *)
  let init = init
end
(*! sharing FunPrint.FunSyn = FunSyn' !*)
(* local *)
(* functor Init *)

(* # 1 "src/meta/MtpInit.sml.ml" *)
