open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_

(* # 1 "src/print/ClausePrint.sig.ml" *)

(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
include CLAUSEPRINT
(* signature CLAUSEPRINT *)

(* # 1 "src/print/ClausePrint.fun.ml" *)
open! Symbol

(* open! Print_;; - causes cycle, qualify PRINT directly *)
open! Basis

module MakeClausePrint
    (Whnf : WHNF)
    (Names : NAMES)
    (Formatter_param : FORMATTER)
    (Print : sig
      module Formatter : FORMATTER

      val formatDec : IntSyn.dctx -> IntSyn.dec -> Formatter.format
      val formatExp : IntSyn.dctx -> IntSyn.exp -> Formatter.format
      val formatSpine : IntSyn.dctx -> IntSyn.spine -> Formatter.format list
      val formatConDec : IntSyn.conDec -> Formatter.format
      val implicit : bool ref
    end)
    (Symbol : SYMBOL) : CLAUSEPRINT = struct
  (*
  (* Clause Printing *)
  (* Author: Frank Pfenning, Carsten Schuermann *)
  (* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Formatter_param : FORMATTER

  (* PRINT inlined to avoid cycle with print_ *)
  module Print : sig
    module Formatter : FORMATTER

    val formatDec : IntSyn.dctx * IntSyn.dec -> Formatter.format
    val formatExp : IntSyn.dctx * IntSyn.exp -> Formatter.format
    val formatSpine : IntSyn.dctx * IntSyn.spine -> Formatter.format list
    val formatConDec : IntSyn.conDec -> Formatter.format
    val implicit : bool ref
  end

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Symbol : SYMBOL
*)
  (*! structure IntSyn = IntSyn' !*)
  module Print = Print
  module Formatter = Print.Formatter
  module Whnf = Whnf
  module Names = Names
  module Symbol = Symbol

  open! struct
    module I = IntSyn
    module F = Print.Formatter

    let str_ = F.string
    let str0 (s, n) = F.string0 n s
    let sym s = str0 (Symbol.sym s)
    let parens fmt = F.hbox [ sym "("; fmt; sym ")" ]

    let rec fmtDQuants (g, a) = match a with
      | I.Pi (((I.Dec (_, v1) as d), I.Maybe), v2) ->
          let d' = Names.decEName g d in
          sym "{"
          :: Print.formatDec g d'
          :: sym "}" :: F.break
          :: fmtDQuants (I.Decl (g, d'), v2)
      | I.Pi (((I.Dec (_, v1) as d), I.Meta), v2) ->
          let d' = Names.decEName g d in
          sym "{"
          :: Print.formatDec g d'
          :: sym "}" :: F.break
          :: fmtDQuants (I.Decl (g, d'), v2)
      | (I.Pi _ as v) -> [ F.hOVbox (fmtDSubGoals (g, v, [])) ]
      | v -> [ Print.formatExp g v ]

    and fmtDSubGoals (g, a, acc) = match a with
      | I.Pi (((I.Dec (_, v1) as d), I.No), v2) ->
          fmtDSubGoals
            ( I.Decl (g, d),
              v2,
              F.break :: sym "<-" :: F.space :: fmtGparens (g, v1) :: acc )
      | (I.Pi _ as v) -> parens (F.hVbox (fmtDQuants (g, v))) :: acc
      | v -> Print.formatExp g v :: acc

    and fmtDparens (g, a) = match a with
      | (I.Pi _ as v) -> parens (F.hVbox (fmtDQuants (g, v)))
      | v -> Print.formatExp g v

    and fmtGparens (g, a) = match a with
      | (I.Pi _ as v) -> parens (F.hVbox (fmtGQuants (g, v)))
      | v -> Print.formatExp g v

    and fmtGQuants (g, v) = match v with
      | I.Pi (((I.Dec (_, v1) as d), I.Maybe), v2) ->
          let d' = Names.decLUName g d in
          sym "{"
          :: Print.formatDec g d'
          :: sym "}" :: F.break
          :: fmtGQuants (I.Decl (g, d'), v2)
      | I.Pi (((I.Dec (_, v1) as d), I.Meta), v2) ->
          let d' = Names.decLUName g d in
          sym "{"
          :: Print.formatDec g d'
          :: sym "}" :: F.break
          :: fmtGQuants (I.Decl (g, d'), v2)
      | v -> [ F.hOVbox (fmtGHyps (g, v)) ]

    and fmtGHyps (g, a) = match a with
      | I.Pi (((I.Dec (_, v1) as d), I.No), v2) ->
          fmtDparens (g, v1)
          :: F.break :: sym "->" :: F.space
          :: fmtGHyps (I.Decl (g, d), v2)
      | (I.Pi _ as v) -> [ F.hVbox (fmtGQuants (g, v)) ]
      | v -> [ Print.formatExp g v ]

    let fmtClause (g, v) = F.hVbox (fmtDQuants (g, v))

    let rec fmtClauseI (i, g, a) = match i, a with
      | 0, v -> fmtClause (g, v)
      | i, I.Pi ((d, _), v) ->
          fmtClauseI (i - 1, I.Decl (g, Names.decEName g d), v)

    let fmtConDec = function
      | I.ConDec (id, parent, i, _, v, I.Type) ->
          ignore (Names.varReset IntSyn.Null);
          let vfmt = fmtClauseI (i, I.Null, v) in
          F.hVbox
            [ str0 (Symbol.const id); F.space; sym ":"; F.break; vfmt; sym "." ]
      | condec -> Print.formatConDec condec
  end

  (* some shorthands *)
  (* assumes NF *)
  (* P = I.No *)
  (* V = Root _ *)
  (* acc <> nil *)
  (* V = Root _ *)
  (* V = Root _ *)
  (* V = Root _ *)
  (* P = I.No or V = Root _ *)
  (* P = I.Maybe *)
  (* V = Root _ *)
  (* type family declaration, definition, or Skolem constant *)
  let formatClause g v = fmtClause (g, v)
  let formatConDec condec = fmtConDec condec
  let clauseToString g v = F.makestring_fmt (formatClause g v)
  let conDecToString condec = F.makestring_fmt (formatConDec condec)

  let printSgn () =
    IntSyn.sgnApp (function cid ->
        begin
          print (conDecToString (IntSyn.sgnLookup cid));
          print "\n"
        end)
end
(* local ... *)
(* functor ClausePrint *)

(* # 1 "src/print/ClausePrint.sml.ml" *)
