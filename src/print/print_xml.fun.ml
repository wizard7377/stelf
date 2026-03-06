open! Basis;;
module PrintXML(PrintXML__0: sig
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
                             module Formatter' : FORMATTER
                             end) : PRINT_XML
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
        let rec name_ x = (F.String (("\"" ^ x) ^ "\""));;
        let rec integer_ n = (F.String (("\"" ^ (Int.toString n)) ^ "\""));;
        let rec sexp fmts = (F.Hbox [(F.HVbox fmts)]);;
        let rec fmtCon =
          function 
                   | (g_, I.BVar n)
                       -> let I.Dec (Some n, _) = I.ctxDec (g_, n)
                            in sexp [(Str (("<Var name = \"" ^ n) ^ "\"/>"))]
                   | (g_, I.Const cid)
                       -> sexp
                          [(Str "<Const name=\"");
                           (Str (I.conDecName (I.sgnLookup cid)));
                           (Str "\"/>")]
                   | (g_, I.Def cid)
                       -> sexp
                          [(Str "<Def>"); F.break_; integer_ cid;
                           (Str "</Def>")]
                   | (g_, I.FgnConst (csid, Condec_))
                       -> sexp [(Str "FngConst")];;
        let rec fmtUni =
          function 
                   | type_ -> (Str "<Type/>")
                   | kind_ -> (Str "<Kind/>");;
        let rec fmtExpW =
          function 
                   | (g_, (I.Uni l_, s))
                       -> sexp
                          [(Str "<Uni>"); F.break_; fmtUni l_;
                           (Str "</Uni>")]
                   | (g_, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s))
                       -> begin
                          match p_
                          with 
                               | maybe_
                                   -> let d'_ = Names.decLUName (g_, d_)
                                        in let g'_ = (I.Decl (g_, d'_))
                                             in sexp
                                                [(Str "<Pi>"); F.break_;
                                                 fmtDec (g_, (d'_, s));
                                                 F.break_;
                                                 fmtExp
                                                 (g'_, (v2_, I.dot1 s));
                                                 (Str "</Pi>")]
                               | no_
                                   -> let g'_ = (I.Decl (g_, d_))
                                        in sexp
                                           [(Str "<Arrow>"); F.break_;
                                            fmtDec' (g_, (d_, s)); F.break_;
                                            fmtExp (g'_, (v2_, I.dot1 s));
                                            (Str "</Arrow>")]
                          end
                   | (g_, (I.Root (h_, s_), s))
                       -> begin
                          match fmtSpine (g_, (s_, s))
                          with 
                               | None -> fmtCon (g_, h_)
                               | Some fmts
                                   -> (F.HVbox
                                       [(Str "<App>"); fmtCon (g_, h_);
                                        F.break_; sexp fmts; (Str "</App>")])
                          end
                   | (g_, (I.Lam (d_, u_), s))
                       -> let d'_ = Names.decLUName (g_, d_)
                            in let g'_ = (I.Decl (g_, d'_))
                                 in sexp
                                    [(Str "<Lam>"); F.break_;
                                     fmtDec (g_, (d'_, s)); F.break_;
                                     fmtExp (g'_, (u_, I.dot1 s));
                                     (Str "</Lam>")]
                   | (g_, (I.FgnExp (csid, f_), s)) -> sexp [(Str "FgnExp")]
        and fmtExp (g_, (u_, s)) = fmtExpW (g_, Whnf.whnf (u_, s))
        and fmtSpine =
          function 
                   | (g_, (nil_, _)) -> None
                   | (g_, (I.SClo (s_, s'), s))
                       -> fmtSpine (g_, (s_, I.comp (s', s)))
                   | (g_, (I.App (u_, s_), s))
                       -> begin
                          match fmtSpine (g_, (s_, s))
                          with 
                               | None -> (Some [fmtExp (g_, (u_, s))])
                               | Some fmts
                                   -> (Some
                                       ([fmtExp (g_, (u_, s)); F.break_] @
                                          fmts))
                          end
        and fmtDec =
          function 
                   | (g_, (I.Dec (None, v_), s))
                       -> sexp
                          [(Str "<Dec>"); F.break_; fmtExp (g_, (v_, s));
                           (Str "</Dec>")]
                   | (g_, (I.Dec (Some x, v_), s))
                       -> sexp
                          [(Str "<Dec name ="); name_ x; (Str ">"); F.break_;
                           fmtExp (g_, (v_, s)); (Str "</Dec>")]
        and fmtDec' =
          function 
                   | (g_, (I.Dec (None, v_), s))
                       -> sexp [fmtExp (g_, (v_, s))]
                   | (g_, (I.Dec (Some x, v_), s))
                       -> sexp [fmtExp (g_, (v_, s))];;
        let rec fmtConDec =
          function 
                   | I.ConDec (name, parent, imp, _, v_, l_)
                       -> let _ = Names.varReset IntSyn.null_
                            in sexp
                               [(Str "<Condec name="); name_ name; F.break_;
                                (Str "implicit="); integer_ imp; (Str ">");
                                F.break_; fmtExp (I.null_, (v_, I.id));
                                F.break_; fmtUni l_; (Str "</Condec>")]
                   | I.SkoDec (name, parent, imp, v_, l_)
                       -> (Str
                           (("<! Skipping Skolem constant " ^ name) ^ ">"))
                   | I.ConDef (name, parent, imp, u_, v_, l_, _)
                       -> let _ = Names.varReset IntSyn.null_
                            in sexp
                               [(Str "<Condef name="); name_ name; F.break_;
                                (Str "implicit="); integer_ imp; (Str ">");
                                F.break_; fmtExp (I.null_, (u_, I.id));
                                F.break_; fmtExp (I.null_, (v_, I.id));
                                F.break_; fmtUni l_; (Str "</Condef>")]
                   | I.AbbrevDef (name, parent, imp, u_, v_, l_)
                       -> let _ = Names.varReset IntSyn.null_
                            in sexp
                               [(Str "<Abbrevdef name="); name_ name;
                                (Str ">"); F.break_; integer_ imp; F.break_;
                                fmtExp (I.null_, (u_, I.id)); F.break_;
                                fmtExp (I.null_, (v_, I.id)); F.break_;
                                fmtUni l_; (Str "</Abbrevdef>")]
                   | I.BlockDec (name, _, _, _)
                       -> (Str
                           (("<! Skipping Skolem constant " ^ name) ^ ">"));;
        let rec fmtEqn (I.Eqn (g_, u1_, u2_)) =
          sexp
          [(Str "<Equation>"); F.break_; fmtExp (g_, (u1_, I.id)); F.break_;
           fmtExp (g_, (u2_, I.id)); (Str "</Equation>")];;
        let rec fmtEqnName (I.Eqn (g_, u1_, u2_)) =
          fmtEqn ((I.Eqn (Names.ctxLUName g_, u1_, u2_)));;
        end;;
    (* Shorthands *);;
    (* fmtCon (c) = ""c"" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding ""`"" (backquote) character
  *);;
    (* FIX -cs Fri Jan 28 17:45:35 2005*);;
    (* I.Skonst, I.FVar cases should be impossible *);;
    (* fmtUni (L) = ""L"" *);;
    (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a ""printing context"" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *);;
    (* if Pi is dependent but anonymous, invent name here *);;
    (* could sometimes be EName *);;
    (* Str ""tw*maybe"", F.Break, *);;
    (* Str ""tw*no"", F.Break,*);;
    (* FIX -cs Fri Jan 28 17:45:43 2005 *);;
    (* I.EClo, I.Redex, I.EVar not possible *);;
    (* fmtSpine (G, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *);;
    (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *);;
    (* fmtEqn assumes that G is a valid printing context *);;
    (* print context?? *);;
    (* fmtEqnName and fmtEqns do not assume that G is a valid printing
     context and will name or rename variables to make it so.
     fmtEqns should only be used for printing constraints.
  *);;
    (* In the functions below, G must be a ""printing context"", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *);;
    let rec formatDec (g_, d_) = fmtDec (g_, (d_, I.id));;
    let rec formatExp (g_, u_) = fmtExp (g_, (u_, I.id));;
    (*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *);;
    let rec formatConDec Condec_ = fmtConDec Condec_;;
    let rec formatEqn e_ = fmtEqn e_;;
    let rec decToString (g_, d_) = F.makestring_fmt (formatDec (g_, d_));;
    let rec expToString (g_, u_) = F.makestring_fmt (formatExp (g_, u_));;
    let rec conDecToString Condec_ = F.makestring_fmt (formatConDec Condec_);;
    let rec eqnToString e_ = F.makestring_fmt (formatEqn e_);;
    let rec printSgn () =
      IntSyn.sgnApp
      (function 
                | cid
                    -> begin
                         print
                         (F.makestring_fmt
                          (formatConDec (IntSyn.sgnLookup cid)));
                         print "\n"
                         end);;
    let rec printSgnToFile path filename =
      let file = TextIO.openOut (path ^ filename)
        in let _ =
             TextIO.output
             (file,
              "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!-- nsgmls ex.xml -->\n<!DOCTYPE Signature SYSTEM \"lf.dtd\">\n<Signature>")
             in let _ =
                  IntSyn.sgnApp
                  (function 
                            | cid
                                -> begin
                                     TextIO.output
                                     (file,
                                      F.makestring_fmt
                                      (formatConDec (IntSyn.sgnLookup cid)));
                                     TextIO.output (file, "\n")
                                     end)
                  in let _ = TextIO.output (file, "</Signature>")
                       in let _ = TextIO.closeOut file in ();;
    end;;
(* local ... *);;
(* functor PrintXml *);;