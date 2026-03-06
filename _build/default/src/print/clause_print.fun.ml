open! Symbol;;
open! Print;;
open! Basis;;
module ClausePrint(ClausePrint__0: sig
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
                                   module Formatter' : FORMATTER
                                   module Print : PRINT
                                   (*! sharing Print.IntSyn = IntSyn' !*)
                                   module Symbol : SYMBOL
                                   end) : CLAUSEPRINT
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    module Formatter = Formatter';;
    open!
      struct
        module I = IntSyn;;
        module F = Formatter;;
        let Str = F.string_;;
        let rec str0_ (s, n) = (F.String0 (n, s));;
        let rec sym s = str0_ (Symbol.sym s);;
        let rec parens fmt = (F.Hbox [sym "("; fmt; sym ")"]);;
        let rec fmtDQuants =
          function 
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_))
                       -> let d'_ = Names.decEName (g_, d_)
                            in (sym "{" :: Print.formatDec (g_, d'_)
                                :: sym "}" :: F.break_
                                :: fmtDQuants ((I.Decl (g_, d'_)), v2_))
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), meta_), v2_))
                       -> let d'_ = Names.decEName (g_, d_)
                            in (sym "{" :: Print.formatDec (g_, d'_)
                                :: sym "}" :: F.break_
                                :: fmtDQuants ((I.Decl (g_, d'_)), v2_))
                   | (g_, (I.Pi _ as v_))
                       -> [(F.HOVbox (fmtDSubGoals (g_, v_, [])))]
                   | (g_, v_) -> [Print.formatExp (g_, v_)]
        and fmtDSubGoals =
          function 
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), acc)
                       -> fmtDSubGoals
                          ((I.Decl (g_, d_)), v2_,
                           (F.break_ :: sym "<-" :: F.space_
                            :: fmtGparens (g_, v1_) :: acc))
                   | (g_, (I.Pi _ as v_), acc)
                       -> (parens ((F.HVbox (fmtDQuants (g_, v_)))) :: acc)
                   | (g_, v_, acc) -> (Print.formatExp (g_, v_) :: acc)
        and fmtDparens =
          function 
                   | (g_, (I.Pi _ as v_))
                       -> parens ((F.HVbox (fmtDQuants (g_, v_))))
                   | (g_, v_) -> Print.formatExp (g_, v_)
        and fmtGparens =
          function 
                   | (g_, (I.Pi _ as v_))
                       -> parens ((F.HVbox (fmtGQuants (g_, v_))))
                   | (g_, v_) -> Print.formatExp (g_, v_)
        and fmtGQuants =
          function 
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_))
                       -> let d'_ = Names.decLUName (g_, d_)
                            in (sym "{" :: Print.formatDec (g_, d'_)
                                :: sym "}" :: F.break_
                                :: fmtGQuants ((I.Decl (g_, d'_)), v2_))
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), meta_), v2_))
                       -> let d'_ = Names.decLUName (g_, d_)
                            in (sym "{" :: Print.formatDec (g_, d'_)
                                :: sym "}" :: F.break_
                                :: fmtGQuants ((I.Decl (g_, d'_)), v2_))
                   | (g_, v_) -> [(F.HOVbox (fmtGHyps (g_, v_)))]
        and fmtGHyps =
          function 
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), no_), v2_))
                       -> (fmtDparens (g_, v1_) :: F.break_ :: sym "->"
                           :: F.space_ :: fmtGHyps ((I.Decl (g_, d_)), v2_))
                   | (g_, (I.Pi _ as v_))
                       -> [(F.HVbox (fmtGQuants (g_, v_)))]
                   | (g_, v_) -> [Print.formatExp (g_, v_)];;
        let rec fmtClause (g_, v_) = (F.HVbox (fmtDQuants (g_, v_)));;
        let rec fmtClauseI =
          function 
                   | (0, g_, v_) -> fmtClause (g_, v_)
                   | (i, g_, I.Pi ((d_, _), v_))
                       -> fmtClauseI
                          (i - 1, (I.Decl (g_, Names.decEName (g_, d_))), v_);;
        let rec fmtConDec =
          function 
                   | I.ConDec (id, parent, i, _, v_, type_)
                       -> let _ = Names.varReset IntSyn.null_
                            in let vfmt_ = fmtClauseI (i, I.null_, v_)
                                 in (F.HVbox
                                     [str0_ (Symbol.const id); F.space_;
                                      sym ":"; F.break_; vfmt_; sym "."])
                   | Condec_ -> Print.formatConDec Condec_;;
        end;;
    (* some shorthands *);;
    (* assumes NF *);;
    (* P = I.No *);;
    (* V = Root _ *);;
    (* acc <> nil *);;
    (* V = Root _ *);;
    (* V = Root _ *);;
    (* V = Root _ *);;
    (* P = I.No or V = Root _ *);;
    (* P = I.Maybe *);;
    (* V = Root _ *);;
    (* type family declaration, definition, or Skolem constant *);;
    let rec formatClause (g_, v_) = fmtClause (g_, v_);;
    let rec formatConDec Condec_ = fmtConDec Condec_;;
    let rec clauseToString (g_, v_) =
      F.makestring_fmt (formatClause (g_, v_));;
    let rec conDecToString Condec_ = F.makestring_fmt (formatConDec Condec_);;
    let rec printSgn () =
      IntSyn.sgnApp
      (function 
                | cid
                    -> begin
                         print (conDecToString (IntSyn.sgnLookup cid));
                         print "\n"
                         end);;
    end;;
(* local ... *);;
(* functor ClausePrint *);;