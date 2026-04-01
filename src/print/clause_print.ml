(* # 1 "src/print/clause_print.sig.ml" *)
open! Basis

(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
include Clause_print_intf
(* signature CLAUSEPRINT *)

(* # 1 "src/print/clause_print.fun.ml" *)
open! Symbol

(* open! Print_;; - causes cycle, qualify PRINT directly *)
open! Basis

module MakeClausePrint (ClausePrint__0 : sig
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
end) : CLAUSEPRINT = struct
  (*! structure IntSyn = IntSyn' !*)
  module Print = ClausePrint__0.Print
  module Formatter = Print.Formatter
  module Whnf = ClausePrint__0.Whnf
  module Names = ClausePrint__0.Names
  module Symbol = ClausePrint__0.Symbol

  open! struct
    module I = IntSyn
    module F = Print.Formatter

    let str_ = F.string
    let rec str0_ (s, n) = F.string0 n s
    let rec sym s = str0_ (Symbol.sym s)
    let rec parens fmt = F.hbox [ sym "("; fmt; sym ")" ]

    let rec fmtDQuants = function
      | g_, I.Pi (((I.Dec (_, v1_) as d_), I.Maybe), v2_) ->
          let d'_ = Names.decEName (g_, d_) in
          sym "{"
          :: Print.formatDec (g_, d'_)
          :: sym "}" :: F.break
          :: fmtDQuants (I.Decl (g_, d'_), v2_)
      | g_, I.Pi (((I.Dec (_, v1_) as d_), I.Meta), v2_) ->
          let d'_ = Names.decEName (g_, d_) in
          sym "{"
          :: Print.formatDec (g_, d'_)
          :: sym "}" :: F.break
          :: fmtDQuants (I.Decl (g_, d'_), v2_)
      | g_, (I.Pi _ as v_) -> [ F.hOVbox (fmtDSubGoals (g_, v_, [])) ]
      | g_, v_ -> [ Print.formatExp (g_, v_) ]

    and fmtDSubGoals = function
      | g_, I.Pi (((I.Dec (_, v1_) as d_), I.No), v2_), acc ->
          fmtDSubGoals
            ( I.Decl (g_, d_),
              v2_,
              F.break :: sym "<-" :: F.space :: fmtGparens (g_, v1_) :: acc )
      | g_, (I.Pi _ as v_), acc -> parens (F.hVbox (fmtDQuants (g_, v_))) :: acc
      | g_, v_, acc -> Print.formatExp (g_, v_) :: acc

    and fmtDparens = function
      | g_, (I.Pi _ as v_) -> parens (F.hVbox (fmtDQuants (g_, v_)))
      | g_, v_ -> Print.formatExp (g_, v_)

    and fmtGparens = function
      | g_, (I.Pi _ as v_) -> parens (F.hVbox (fmtGQuants (g_, v_)))
      | g_, v_ -> Print.formatExp (g_, v_)

    and fmtGQuants = function
      | g_, I.Pi (((I.Dec (_, v1_) as d_), I.Maybe), v2_) ->
          let d'_ = Names.decLUName (g_, d_) in
          sym "{"
          :: Print.formatDec (g_, d'_)
          :: sym "}" :: F.break
          :: fmtGQuants (I.Decl (g_, d'_), v2_)
      | g_, I.Pi (((I.Dec (_, v1_) as d_), I.Meta), v2_) ->
          let d'_ = Names.decLUName (g_, d_) in
          sym "{"
          :: Print.formatDec (g_, d'_)
          :: sym "}" :: F.break
          :: fmtGQuants (I.Decl (g_, d'_), v2_)
      | g_, v_ -> [ F.hOVbox (fmtGHyps (g_, v_)) ]

    and fmtGHyps = function
      | g_, I.Pi (((I.Dec (_, v1_) as d_), I.No), v2_) ->
          fmtDparens (g_, v1_)
          :: F.break :: sym "->" :: F.space
          :: fmtGHyps (I.Decl (g_, d_), v2_)
      | g_, (I.Pi _ as v_) -> [ F.hVbox (fmtGQuants (g_, v_)) ]
      | g_, v_ -> [ Print.formatExp (g_, v_) ]

    let rec fmtClause (g_, v_) = F.hVbox (fmtDQuants (g_, v_))

    let rec fmtClauseI = function
      | 0, g_, v_ -> fmtClause (g_, v_)
      | i, g_, I.Pi ((d_, _), v_) ->
          fmtClauseI (i - 1, I.Decl (g_, Names.decEName (g_, d_)), v_)

    let rec fmtConDec = function
      | I.ConDec (id, parent, i, _, v_, I.Type) ->
          let _ = Names.varReset IntSyn.Null in
          let vfmt_ = fmtClauseI (i, I.Null, v_) in
          F.hVbox
            [
              str0_ (Symbol.const id); F.space; sym ":"; F.break; vfmt_; sym ".";
            ]
      | condec_ -> Print.formatConDec condec_
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
  let rec formatClause (g_, v_) = fmtClause (g_, v_)
  let rec formatConDec condec_ = fmtConDec condec_
  let rec clauseToString (g_, v_) = F.makestring_fmt (formatClause (g_, v_))
  let rec conDecToString condec_ = F.makestring_fmt (formatConDec condec_)

  let rec printSgn () =
    IntSyn.sgnApp (function cid ->
        begin
          print (conDecToString (IntSyn.sgnLookup cid));
          print "\n"
        end)
end
(* local ... *)
(* functor ClausePrint *)

(* # 1 "src/print/clause_print.sml.ml" *)
