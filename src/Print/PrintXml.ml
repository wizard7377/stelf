(* # 1 "src/print/PrintXml.sig.ml" *)
open! Basis

(* Printing Signatures *)
(* Author: Frank Pfenning *)
(* modified: Carsten Schuermann *)
include PRINTXML
(* signature PRINT_XML *)

(* # 1 "src/print/PrintXml.fun.ml" *)
open! Basis

module MakePrintXML
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER) : PRINT_XML = struct
  (*
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow *)
  (* Modified: Carsten Schuermann *)
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
    let str0 (s, n) = F.string0 n s
    let name_ x = F.string (("\"" ^ x) ^ "\"")
    let integer_ n = F.string (("\"" ^ Int.toString n) ^ "\"")
    let sexp fmts = F.hbox [ F.hVbox fmts ]

    let fmtCon = function
      | g_, I.BVar n ->
          let (I.Dec (Some n, _)) = I.ctxDec (g_, n) in
          sexp [ str_ (("<Var name = \"" ^ n) ^ "\"/>") ]
      | g_, I.Const cid ->
          sexp
            [
              str_ "<Const name=\"";
              str_ (I.conDecName (I.sgnLookup cid));
              str_ "\"/>";
            ]
      | g_, I.Def cid ->
          sexp [ str_ "<Def>"; F.break; integer_ cid; str_ "</Def>" ]
      | g_, I.FgnConst (csid, condec_) -> sexp [ str_ "FngConst" ]

    let fmtUni = function
      | I.Type -> str_ "<Type/>"
      | I.Kind -> str_ "<Kind/>"

    let rec fmtExpW = function
      | g_, (I.Uni l_, s) ->
          sexp [ str_ "<Uni>"; F.break; fmtUni l_; str_ "</Uni>" ]
      | g_, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s) ->
          begin match p_ with
          | I.Maybe ->
              let d'_ = Names.decLUName (g_, d_) in
              let g'_ = I.Decl (g_, d'_) in
              sexp
                [
                  str_ "<Pi>";
                  F.break;
                  fmtDec (g_, (d'_, s));
                  F.break;
                  fmtExp (g'_, (v2_, I.dot1 s));
                  str_ "</Pi>";
                ]
          | I.No ->
              let g'_ = I.Decl (g_, d_) in
              sexp
                [
                  str_ "<Arrow>";
                  F.break;
                  fmtDec' (g_, (d_, s));
                  F.break;
                  fmtExp (g'_, (v2_, I.dot1 s));
                  str_ "</Arrow>";
                ]
          end
      | g_, (I.Root (h_, s_), s) ->
          begin match fmtSpine (g_, (s_, s)) with
          | None -> fmtCon (g_, h_)
          | Some fmts ->
              F.hVbox
                [
                  str_ "<App>";
                  fmtCon (g_, h_);
                  F.break;
                  sexp fmts;
                  str_ "</App>";
                ]
          end
      | g_, (I.Lam (d_, u_), s) ->
          let d'_ = Names.decLUName (g_, d_) in
          let g'_ = I.Decl (g_, d'_) in
          sexp
            [
              str_ "<Lam>";
              F.break;
              fmtDec (g_, (d'_, s));
              F.break;
              fmtExp (g'_, (u_, I.dot1 s));
              str_ "</Lam>";
            ]
      | g_, (I.FgnExp (csid, f_), s) -> sexp [ str_ "FgnExp" ]

    and fmtExp (g_, (u_, s)) = fmtExpW (g_, Whnf.whnf (u_, s))

    and fmtSpine = function
      | g_, (I.Nil, _) -> None
      | g_, (I.SClo (s_, s'), s) -> fmtSpine (g_, (s_, I.comp (s', s)))
      | g_, (I.App (u_, s_), s) ->
          begin match fmtSpine (g_, (s_, s)) with
          | None -> Some [ fmtExp (g_, (u_, s)) ]
          | Some fmts -> Some ([ fmtExp (g_, (u_, s)); F.break ] @ fmts)
          end

    and fmtDec = function
      | g_, (I.Dec (None, v_), s) ->
          sexp [ str_ "<Dec>"; F.break; fmtExp (g_, (v_, s)); str_ "</Dec>" ]
      | g_, (I.Dec (Some x, v_), s) ->
          sexp
            [
              str_ "<Dec name =";
              name_ x;
              str_ ">";
              F.break;
              fmtExp (g_, (v_, s));
              str_ "</Dec>";
            ]

    and fmtDec' = function
      | g_, (I.Dec (None, v_), s) -> sexp [ fmtExp (g_, (v_, s)) ]
      | g_, (I.Dec (Some x, v_), s) -> sexp [ fmtExp (g_, (v_, s)) ]

    let fmtConDec = function
      | I.ConDec (name, parent, imp, _, v_, l_) ->
          ignore (Names.varReset IntSyn.Null);
          sexp
            [
              str_ "<Condec name=";
              name_ name;
              F.break;
              str_ "implicit=";
              integer_ imp;
              str_ ">";
              F.break;
              fmtExp (I.Null, (v_, I.id));
              F.break;
              fmtUni l_;
              str_ "</Condec>";
            ]
      | I.SkoDec (name, parent, imp, v_, l_) ->
          str_ (("<! Skipping Skolem constant " ^ name) ^ ">")
      | I.ConDef (name, parent, imp, u_, v_, l_, _) ->
          ignore (Names.varReset IntSyn.Null);
          sexp
            [
              str_ "<Condef name=";
              name_ name;
              F.break;
              str_ "implicit=";
              integer_ imp;
              str_ ">";
              F.break;
              fmtExp (I.Null, (u_, I.id));
              F.break;
              fmtExp (I.Null, (v_, I.id));
              F.break;
              fmtUni l_;
              str_ "</Condef>";
            ]
      | I.AbbrevDef (name, parent, imp, u_, v_, l_) ->
          ignore (Names.varReset IntSyn.Null);
          sexp
            [
              str_ "<Abbrevdef name=";
              name_ name;
              str_ ">";
              F.break;
              integer_ imp;
              F.break;
              fmtExp (I.Null, (u_, I.id));
              F.break;
              fmtExp (I.Null, (v_, I.id));
              F.break;
              fmtUni l_;
              str_ "</Abbrevdef>";
            ]
      | I.BlockDec (name, _, _, _) ->
          str_ (("<! Skipping Skolem constant " ^ name) ^ ">")

    let fmtEqn (I.Eqn (g_, u1_, u2_)) =
      sexp
        [
          str_ "<Equation>";
          F.break;
          fmtExp (g_, (u1_, I.id));
          F.break;
          fmtExp (g_, (u2_, I.id));
          str_ "</Equation>";
        ]

    let fmtEqnName (I.Eqn (g_, u1_, u2_)) =
      fmtEqn (I.Eqn (Names.ctxLUName g_, u1_, u2_))
  end

  (* Shorthands *)
  (* fmtCon (c) = ""c"" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding ""`"" (backquote) character
  *)
  (* FIX -cs Fri Jan 28 17:45:35 2005*)
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
  (* str_ ""tw*maybe"", F.Break, *)
  (* str_ ""tw*no"", F.Break,*)
  (* FIX -cs Fri Jan 28 17:45:43 2005 *)
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
  let formatDec (g_, d_) = fmtDec (g_, (d_, I.id))
  let formatExp (g_, u_) = fmtExp (g_, (u_, I.id))

  (*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *)
  let formatConDec condec_ = fmtConDec condec_
  let formatEqn e_ = fmtEqn e_
  let decToString (g_, d_) = F.makestring_fmt (formatDec (g_, d_))
  let expToString (g_, u_) = F.makestring_fmt (formatExp (g_, u_))
  let conDecToString condec_ = F.makestring_fmt (formatConDec condec_)
  let eqnToString e_ = F.makestring_fmt (formatEqn e_)

  let printSgn () =
    IntSyn.sgnApp (function cid ->
        begin
          print (F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
          print "\n"
        end)

  let printSgnToFile path filename =
    let file = TextIO.openOut (path ^ filename) in
    let _ =
      TextIO.output
        ( file,
          "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n\
           <!-- nsgmls ex.xml -->\n\
           <!DOCTYPE Signature SYSTEM \"lf.dtd\">\n\
           <Signature>" )
    in
    let _ =
      IntSyn.sgnApp (function cid ->
          begin
            TextIO.output
              (file, F.makestring_fmt (formatConDec (IntSyn.sgnLookup cid)));
            TextIO.output (file, "\n")
          end)
    in
    ignore (TextIO.output (file, "</Signature>"));
    ignore (TextIO.closeOut file);
    ()
end
(* local ... *)
(* functor PrintXml *)

(* # 1 "src/print/PrintXml.sml.ml" *)
