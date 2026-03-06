# 1 "src/print/print_twega.sig.ml"
open! Basis;;
(* Printing Signatures *);;
(* Author: Frank Pfenning *);;
module type PRINT_TWEGA = sig
                          val printSgn : unit -> unit
                          val printSgnToFile : string -> unit
                          end;;
(* signature PRINT_TWEGA *);;
# 1 "src/print/print_twega.fun.ml"
open! Basis;;
module PrintTwega(PrintTwega__0: sig
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
                                 module Formatter' : FORMATTER
                                 end) : PRINT_TWEGA
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
        let rec integer_ n = (F.String (Int.toString n));;
        let rec sexp fmts = (F.Hbox [(Str "("); (F.HVbox fmts); (Str ")")]);;
        let rec fmtCon =
          function 
                   | (g_, I.BVar n)
                       -> sexp [(Str "tw~bvar"); F.break_; integer_ n]
                   | (g_, I.Const cid)
                       -> sexp [(Str "tw~const"); F.break_; integer_ cid]
                   | (g_, I.Def cid)
                       -> sexp [(Str "tw~def"); F.break_; integer_ cid];;
        let rec fmtUni =
          function 
                   | type_ -> (Str "tw*type")
                   | kind_ -> (Str "tw*kind");;
        let rec fmtExpW =
          function 
                   | (g_, (I.Uni l_, s))
                       -> sexp [(Str "tw~uni"); F.break_; fmtUni l_]
                   | (g_, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s))
                       -> begin
                          match p_
                          with 
                               | maybe_
                                   -> let d'_ = Names.decLUName (g_, d_)
                                        in let g'_ = (I.Decl (g_, d'_))
                                             in sexp
                                                [(Str "tw~pi"); F.break_;
                                                 fmtDec (g_, (d'_, s));
                                                 F.break_; (Str "tw*maybe");
                                                 F.break_;
                                                 fmtExp
                                                 (g'_, (v2_, I.dot1 s))]
                               | no_
                                   -> let g'_ = (I.Decl (g_, d_))
                                        in sexp
                                           [(Str "tw~pi"); F.break_;
                                            fmtDec (g_, (d_, s)); F.break_;
                                            (Str "tw*no"); F.break_;
                                            fmtExp (g'_, (v2_, I.dot1 s))]
                          end
                   | (g_, (I.Root (h_, s_), s))
                       -> sexp
                          [(Str "tw~root"); F.break_; fmtCon (g_, h_);
                           F.break_; fmtSpine (g_, (s_, s))]
                   | (g_, (I.Lam (d_, u_), s))
                       -> let d'_ = Names.decLUName (g_, d_)
                            in let g'_ = (I.Decl (g_, d'_))
                                 in sexp
                                    [(Str "tw~lam"); F.break_;
                                     fmtDec (g_, (d'_, s)); F.break_;
                                     fmtExp (g'_, (u_, I.dot1 s))]
        and fmtExp (g_, (u_, s)) = fmtExpW (g_, Whnf.whnf (u_, s))
        and fmtSpine =
          function 
                   | (g_, (nil_, _)) -> (Str "tw*empty-spine")
                   | (g_, (I.SClo (s_, s'), s))
                       -> fmtSpine (g_, (s_, I.comp (s', s)))
                   | (g_, (I.App (u_, s_), s))
                       -> sexp
                          [(Str "tw~app"); F.break_; fmtExp (g_, (u_, s));
                           F.break_; fmtSpine (g_, (s_, s))]
        and fmtDec =
          function 
                   | (g_, (I.Dec (None, v_), s))
                       -> sexp
                          [(Str "tw~decl"); F.break_; (Str "nil"); F.break_;
                           fmtExp (g_, (v_, s))]
                   | (g_, (I.Dec (Some x, v_), s))
                       -> sexp
                          [(Str "tw~decl"); F.break_; name_ x; F.break_;
                           fmtExp (g_, (v_, s))];;
        let rec fmtConDec =
          function 
                   | I.ConDec (name, parent, imp, _, v_, l_)
                       -> let _ = Names.varReset IntSyn.null_
                            in sexp
                               [(Str "tw~defConst"); F.space_; name_ name;
                                F.break_; integer_ imp; F.break_;
                                fmtExp (I.null_, (v_, I.id)); F.break_;
                                fmtUni l_]
                   | I.SkoDec (name, parent, imp, v_, l_)
                       -> (Str
                           (("%% Skipping Skolem constant " ^ name) ^ " %%"))
                   | I.ConDef (name, parent, imp, u_, v_, l_, _)
                       -> let _ = Names.varReset IntSyn.null_
                            in sexp
                               [(Str "tw~defConst"); F.space_; name_ name;
                                F.break_; integer_ imp; F.break_;
                                fmtExp (I.null_, (u_, I.id)); F.break_;
                                fmtExp (I.null_, (v_, I.id)); F.break_;
                                fmtUni l_]
                   | I.AbbrevDef (name, parent, imp, u_, v_, l_)
                       -> let _ = Names.varReset IntSyn.null_
                            in sexp
                               [(Str "tw~defConst"); F.space_; name_ name;
                                F.break_; integer_ imp; F.break_;
                                fmtExp (I.null_, (u_, I.id)); F.break_;
                                fmtExp (I.null_, (v_, I.id)); F.break_;
                                fmtUni l_];;
        let rec fmtEqn (I.Eqn (g_, u1_, u2_)) =
          sexp
          [(Str "tw*eqn"); F.break_; fmtExp (g_, (u1_, I.id)); F.break_;
           fmtExp (g_, (u2_, I.id))];;
        let rec fmtEqnName (I.Eqn (g_, u1_, u2_)) =
          fmtEqn ((I.Eqn (Names.ctxLUName g_, u1_, u2_)));;
        end;;
    (* Shorthands *);;
    (* fmtCon (c) = ""c"" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding ""`"" (backquote) character
  *);;
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
    let rec formatSpine (g_, s_) = fmtSpine (g_, (s_, I.id));;
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
    let rec printSgnToFile filename =
      let file = TextIO.openOut filename
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
             in let _ = TextIO.closeOut file in ();;
    end;;
(* local ... *);;
(* functor Print *);;
# 1 "src/print/print_twega.sml.ml"
