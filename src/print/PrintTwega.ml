(* # 1 "src/print/PrintTwega.sig.ml" *)
open! Basis

(* Printing Signatures *)
(* Author: Frank Pfenning *)
include PrintTwega_intf
(* signature PRINT_TWEGA *)

(* # 1 "src/print/PrintTwega.fun.ml" *)
open! Basis

module MakePrintTwega
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER) :
  PRINT_TWEGA =
struct
(*
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow *)
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Formatter_param : FORMATTER
*)
  (*! structure IntSyn = IntSyn' !*)
  module Formatter = struct
    include Formatter_param
  end

  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names

  open! struct
    module I = IntSyn
    module F = Formatter

    let str_ = F.string
    let rec str0_ (s, n) = F.string0 n s
    let rec name_ x = F.string (("\"" ^ x) ^ "\"")
    let rec integer_ n = F.string (Int.toString n)
    let rec sexp fmts = F.hbox [ str_ "("; F.hVbox fmts; str_ ")" ]

    let rec fmtCon = function
      | g_, I.BVar n -> sexp [ str_ "tw~bvar"; F.break; integer_ n ]
      | g_, I.Const cid -> sexp [ str_ "tw~const"; F.break; integer_ cid ]
      | g_, I.Def cid -> sexp [ str_ "tw~def"; F.break; integer_ cid ]

    let rec fmtUni = function
      | I.Type -> str_ "tw*type"
      | I.Kind -> str_ "tw*kind"

    let rec fmtExpW = function
      | g_, (I.Uni l_, s) -> sexp [ str_ "tw~uni"; F.break; fmtUni l_ ]
      | g_, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s) -> begin
          match p_ with
          | I.Maybe ->
              let d'_ = Names.decLUName (g_, d_) in
              let g'_ = I.Decl (g_, d'_) in
              sexp
                [
                  str_ "tw~pi";
                  F.break;
                  fmtDec (g_, (d'_, s));
                  F.break;
                  str_ "tw*maybe";
                  F.break;
                  fmtExp (g'_, (v2_, I.dot1 s));
                ]
          | I.No ->
              let g'_ = I.Decl (g_, d_) in
              sexp
                [
                  str_ "tw~pi";
                  F.break;
                  fmtDec (g_, (d_, s));
                  F.break;
                  str_ "tw*no";
                  F.break;
                  fmtExp (g'_, (v2_, I.dot1 s));
                ]
        end
      | g_, (I.Root (h_, s_), s) ->
          sexp
            [
              str_ "tw~root";
              F.break;
              fmtCon (g_, h_);
              F.break;
              fmtSpine (g_, (s_, s));
            ]
      | g_, (I.Lam (d_, u_), s) ->
          let d'_ = Names.decLUName (g_, d_) in
          let g'_ = I.Decl (g_, d'_) in
          sexp
            [
              str_ "tw~lam";
              F.break;
              fmtDec (g_, (d'_, s));
              F.break;
              fmtExp (g'_, (u_, I.dot1 s));
            ]

    and fmtExp (g_, (u_, s)) = fmtExpW (g_, Whnf.whnf (u_, s))

    and fmtSpine = function
      | g_, (I.Nil, _) -> str_ "tw*empty-spine"
      | g_, (I.SClo (s_, s'), s) -> fmtSpine (g_, (s_, I.comp (s', s)))
      | g_, (I.App (u_, s_), s) ->
          sexp
            [
              str_ "tw~app";
              F.break;
              fmtExp (g_, (u_, s));
              F.break;
              fmtSpine (g_, (s_, s));
            ]

    and fmtDec = function
      | g_, (I.Dec (None, v_), s) ->
          sexp
            [
              str_ "tw~decl"; F.break; str_ "nil"; F.break; fmtExp (g_, (v_, s));
            ]
      | g_, (I.Dec (Some x, v_), s) ->
          sexp
            [ str_ "tw~decl"; F.break; name_ x; F.break; fmtExp (g_, (v_, s)) ]

    let rec fmtConDec = function
      | I.ConDec (name, parent, imp, _, v_, l_) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [
              str_ "tw~defConst";
              F.space;
              name_ name;
              F.break;
              integer_ imp;
              F.break;
              fmtExp (I.Null, (v_, I.id));
              F.break;
              fmtUni l_;
            ]
      | I.SkoDec (name, parent, imp, v_, l_) ->
          str_ (("%% Skipping Skolem constant " ^ name) ^ " %%")
      | I.ConDef (name, parent, imp, u_, v_, l_, _) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [
              str_ "tw~defConst";
              F.space;
              name_ name;
              F.break;
              integer_ imp;
              F.break;
              fmtExp (I.Null, (u_, I.id));
              F.break;
              fmtExp (I.Null, (v_, I.id));
              F.break;
              fmtUni l_;
            ]
      | I.AbbrevDef (name, parent, imp, u_, v_, l_) ->
          let _ = Names.varReset IntSyn.Null in
          sexp
            [
              str_ "tw~defConst";
              F.space;
              name_ name;
              F.break;
              integer_ imp;
              F.break;
              fmtExp (I.Null, (u_, I.id));
              F.break;
              fmtExp (I.Null, (v_, I.id));
              F.break;
              fmtUni l_;
            ]

    let rec fmtEqn (I.Eqn (g_, u1_, u2_)) =
      sexp
        [
          str_ "tw*eqn";
          F.break;
          fmtExp (g_, (u1_, I.id));
          F.break;
          fmtExp (g_, (u2_, I.id));
        ]

    let rec fmtEqnName (I.Eqn (g_, u1_, u2_)) =
      fmtEqn (I.Eqn (Names.ctxLUName g_, u1_, u2_))
  end

  (* Shorthands *)
  (* fmtCon (c) = ""c"" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding ""`"" (backquote) character
  *)
  (* I.Skonst, I.FVar cases should be impossible *)
  (* fmtUni (L) = ""L"" *)
  (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a ""printing context"" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  (* if Pi is dependent but anonymous, invent name here *)
  (* could sometimes be EName *)
  (* I.EClo, I.Redex, I.EVar not possible *)
  (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  (* fmtEqn assumes that G is a valid printing context *)
  (* print context?? *)
  (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing Constraints.
  *)
  (* In the functions below, G must be a ""printing context"", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  let rec formatDec (g_, d_) = fmtDec (g_, (d_, I.id))
  let rec formatExp (g_, u_) = fmtExp (g_, (u_, I.id))
  let rec formatSpine (g_, s_) = fmtSpine (g_, (s_, I.id))
  let rec formatConDec condec_ = fmtConDec condec_
  let rec formatEqn e_ = fmtEqn e_
  let rec decToString (g_, d_) = F.makestring_fmt (formatDec (g_, d_))
  let rec expToString (g_, u_) = F.makestring_fmt (formatExp (g_, u_))
  let rec conDecToString condec_ = F.makestring_fmt (formatConDec condec_)
  let rec eqnToString e_ = F.makestring_fmt (formatEqn e_)

  let rec printSgn () =
    IntSyn.sgnApp (function cid ->
        begin
          print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
          print "\n"
        end)

  let rec printSgnToFile filename =
    let file = TextIO.openOut filename in
    let _ =
      IntSyn.sgnApp (function cid ->
          begin
            TextIO.output
              (file, F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
            TextIO.output (file, "\n")
          end)
    in
    let _ = TextIO.closeOut file in
    ()
end
(* local ... *)
(* functor Print *)

(* # 1 "src/print/PrintTwega.sml.ml" *)
