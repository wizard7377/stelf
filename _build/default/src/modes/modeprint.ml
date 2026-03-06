# 1 "src/modes/modeprint.sig.ml"
open! Basis;;
(* Printing Mode Declarations *);;
(* Author: Carsten Schuermann *);;
module type MODEPRINT = sig
                        (*! structure ModeSyn : MODESYN !*)
                        val
                          modeToString : (IntSyn.cid * ModeSyn.modeSpine_) ->
                                         string
                        val
                          modesToString : (IntSyn.cid * ModeSyn.modeSpine_)
                                          list ->
                                          string
                        end;;
(* signature MODEPRINT *);;
# 1 "src/modes/modeprint.fun.ml"
open! Basis;;
(* Printing Mode Declarations *);;
(* Author: Carsten Schuermann *);;
module ModePrint(ModePrint__0: sig
                               (*! structure ModeSyn' : MODESYN !*)
                               module Names : NAMES
                               (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                               module Formatter : FORMATTER
                               module Print : PRINT
                               end) : MODEPRINT
  =
  struct
    (* structure ModeSyn = ModeSyn' *);;
    open!
      struct
        module I = IntSyn;;
        module M = ModeSyn;;
        module F = Formatter;;
        module P = Print;;
        let rec modeToString =
          function 
                   | plus_ -> "+"
                   | star_ -> "*"
                   | minus_ -> "-"
                   | minus1_ -> "-1";;
        let rec argToString (M.Marg (m, _)) = modeToString m;;
        let rec nameDec =
          function 
                   | (I.Dec (_, v_), M.Marg (_, (Some _ as name)))
                       -> (I.Dec (name, v_))
                   | (d_, M.Marg (_, None)) -> d_;;
        let rec makeSpine g_ =
          let rec makeSpine' =
            function 
                     | (null_, _, s_) -> s_
                     | (I.Decl (g_, _), k, s_)
                         -> makeSpine'
                            (g_, k + 1,
                             (I.App ((I.Root ((I.BVar k), I.nil_)), s_)))
            in makeSpine' (g_, 1, I.nil_);;
        let rec fmtModeDec (cid, mS) =
          let v_ = I.constType cid
            in let rec fmtModeDec' =
                 function 
                          | (g_, _, mnil_)
                              -> [(F.String "(");
                                  P.formatExp
                                  (g_,
                                   (I.Root ((I.Const cid), makeSpine g_)));
                                  (F.String ")")]
                          | (g_, I.Pi ((d_, _), v'_), M.Mapp (marg, s_))
                              -> let d'_ = nameDec (d_, marg)
                                   in let d''_ = Names.decEName (g_, d'_)
                                        in [(F.String (argToString marg));
                                            (F.String "{");
                                            P.formatDec (g_, d''_);
                                            (F.String "}"); F.break_] @
                                             (fmtModeDec'
                                              ((I.Decl (g_, d''_)), v'_, s_))
                 in (F.HVbox (fmtModeDec' (I.null_, v_, mS)));;
        let rec fmtModeDecs =
          function 
                   | ((cid, mS) :: []) -> [fmtModeDec (cid, mS)]
                   | ((cid, mS) :: mdecs)
                       -> (fmtModeDec (cid, mS) :: F.break_
                           :: fmtModeDecs mdecs);;
        let rec modeToString cM = F.makestring_fmt (fmtModeDec cM);;
        let rec modesToString mdecs =
          F.makestring_fmt ((F.Vbox0 (0, 1, fmtModeDecs mdecs)));;
        end;;
    let modeToString = modeToString;;
    let modesToString = modesToString;;
    end;;
(*! sharing Print.IntSyn = ModeSyn'.IntSyn !*);;
(* local *);;
(* functor ModePrint *);;
# 1 "src/modes/modeprint.sml.ml"
