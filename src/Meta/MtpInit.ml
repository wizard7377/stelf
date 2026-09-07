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

    let init f of_ =
      let rec init' (gb, a, b, ss) = match gb, a, b with
        | (g, b), S.All (_, o), F.All (F.Prim d, f') ->
            let d' = Names.decName g d in
            init'
              ( ( I.Decl (g, d'),
                  I.Decl (b, S.Lemma (S.Splits !MTPGlobal.maxSplit)) ),
                o,
                f',
                ss )
        | gb, S.And (o1, o2), F.And (f1, f2) ->
            init' (gb, o1, f1, init' (gb, o2, f2, ss))
        | gb, o, (F.Ex _ as f') ->
            S.State (List.length ss + 1, gb, (f, of_), 1, o, [], f') :: ss
        | gb, o, (True as f') ->
            S.State (List.length ss + 1, gb, (f, of_), 1, o, [], f') :: ss
      in
      Names.varReset I.Null;
      begin
        MTPData.maxFill := 0;
        init' ((I.Null, I.Null), of_, f, [])
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
