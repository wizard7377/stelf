open! Basis;;
open!
  struct
    module F = FunSyn;;
    module I = IntSyn;;
    let rec load file =
      begin
      match Twelf.Config.load (Twelf.Config.read file)
      with 
           | ok_ -> Twelf.ok_
           | abort_ -> raise Domain
      end;;
    let rec test names =
      let a =
        map
        (function 
                  | x
                      -> valOf
                         (Names.constLookup (valOf (Names.stringToQid x))))
        names
        in let name = foldr (fun (x__op, y__op) -> x__op ^ y__op) "" names
             in let _ = Names.varReset IntSyn.null_
                  in let p_ = RelFun.convertPro a
                       in let f_ = RelFun.convertFor a
                            in let _ =
                                 begin
                                   FunTypeCheck.check (p_, f_);Twelf.ok_
                                   end
                                 in let ld_ = (F.LemmaDec (names, p_, f_))
                                      in let _ =
                                           TextIO.print
                                           (FunPrint.lemmaDecToString ld_)
                                           in FunNames.installName
                                              (name, F.lemmaAdd ld_);;
    end;;
let _ = Twelf.chatter := 1;;
let _ = FunNames.reset ();;
let _ = Twelf.loadFile "TEST/cp.elf";;
let _ = test ["new"];;
let _ = raise Domain;;
(* Regression test for Mini-ML *);;
let _ = load "examples/mini-ml/sources.cfg";;
let _ = Twelf.loadFile "examples/mini-ml/reduce.elf";;
let _ = test ["eval"];;
let _ = test ["value"];;
let _ = test ["vs"];;
let _ = test ["tps"];;
let _ = test ["==>"];;
let _ = test ["==>*"];;
(* Regression test for copy *);;
let _ = Twelf.loadFile "TEST/cp.elf";;
let _ = test ["cpt"];;
(* Regression test for ccc *);;
let _ = load "examples/ccc/sources.cfg";;
let _ = test ["conc"];;
(* Regression test for prop-calc *);;
let _ = load "examples/prop-calc/sources.cfg";;
let _ = test ["combdefn"];;
(* Regression test for compile *);;
let _ = load "examples/compile/cpm/sources.cfg";;
let _ = test ["ccp"];;
let _ = test ["peq"];;
(* Regression test for logic programming *);;
let _ = load "examples/lp/sources.cfg";;
let _ = test ["can"; "atm"];;
let _ = test ["iscan"; "isatm"];;
let _ = test ["s_sound"; "h_sound"; "i_sound"];;
let _ = test ["cmpcs"; "cmpai"];;
let _ = test ["gl"; "pg"];;
let _ = test ["r_total"];;
(* Cannot work yet because we do not have mutual
     recursive functions.
  *);;
(* Regression test for compile *);;
let _ = load "examples/compile/cls/sources.cfg";;
let _ = test ["trans"; "vtrans"];;
let _ = test ["feval"];;
let _ = test ["=>"];;
let _ = test [">=>*"];;
let _ = test [">ceval"];;
let _ = test ["append"];;
let _ = test ["subcomp"];;
let _ = test ["cev_complete"];;
let _ = test ["<"];;
let _ = test ["trans*"];;
let _ = test ["spl"];;
let _ = test ["cls_sound"];;
(* Regression test for Church-Rosser *);;
let _ = load "examples/church-rosser/sources.cfg";;
let _ = test ["identity"];;
let _ = test ["append"];;
(*  val _ = test [""subst""] 
  val _ = test [""dia""]
  val _ = test [""strip""] 
  val _ = test [""conf""]
  val _ = test [""cr""] *);;
(* Regression test for Cut-Elimination *);;
let _ = load "examples/cut-elim/sources.cfg";;
let _ = test ["ca"];;
let _ = test ["ce"];;
let _ = test ["ca'"];;
let _ = test ["ce'"];;
let _ = load "examples/kolm/sources.cfg";;
let _ = test ["kolm"];;
let _ = test ["existskolm"];;
let _ = test ["nj_nk"];;
let _ = test ["equiv"];;
let _ = test ["complete"];;