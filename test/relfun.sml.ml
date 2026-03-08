open! Basis

open! struct
  module I = IntSyn
  module T = Tomega

  let rec load file =
    begin match Twelf.Config.load (Twelf.Config.read file) with
    | ok_ -> Twelf.ok_
    | abort_ -> raise Domain
    end

  let rec printS = function
    | [] -> ()
    | condec :: s_ -> begin
        TextIO.print (Print.conDecToString condec ^ "\n");
        printS s_
      end
end

let _ = Compiler.Control.Print.printDepth := 100

let rec test names =
  let a =
    map
      (function x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
      names
  in
  let name = foldr (fun (x__op, y__op) -> x__op ^ y__op) "" names in
  let _ = Names.varReset IntSyn.null_ in
  let ss_ = map Worldify.worldify a in
  let s_ = foldr (fun (x__op, y__op) -> x__op @ y__op) [] ss_ in
  let _ = printS s_ in
  let _ = TextIO.print "[convertPrg " in
  let p_ = Converter.convertPrg a in
  let _ = TextIO.print "convertFor... " in
  let f_ = Converter.convertFor a in
  let _ = TextIO.print "installPrg... " in
  let _ = Converter.installPrg a in
  let _ = TextIO.print "printing... " in
  let _ = TextIO.print (TomegaPrint.forToString (I.null_, f_) ^ "\n") in
  let _ = TextIO.print (TomegaPrint.funToString p_ ^ "\n") in
  let _ = TextIO.print "checking ... " in
  let _ = TomegaTypeCheck.checkPrg (I.null_, (p_, f_)) in
  let _ = TextIO.print "]" in
  p_
(*      val _ = (FunTypeCheck.check (P, F); Twelf.OK)   *)
(*      val LD = F.LemmaDec (names, P, F) *)
(*      val _ = TextIO.print (FunPrint.lemmaDecToString LD) *)
(*      FunNames.installName (name, F.lemmaAdd LD) *)

let rec print names =
  let p_ = test names in
  begin
    TextIO.print (TomegaPrint.funToString p_ ^ "\n");
    p_
  end

let _ = Twelf.chatter := 1

(*  val _ = FunNames.reset(); --cs *)
let _ = load "/home/carsten/people/KarlCrary/sources.cfg"
let _ = print [ "foo" ]
let _ = load "examples/guide/sources.cfg"
let _ = print [ "cp" ]

(* Regression print for Mini-ML *)
let _ = load "examples/mini-ml/sources.cfg"
let _ = Twelf.loadFile "examples/mini-ml/reduce.elf"
let _ = print [ "eval" ]
let _ = print [ "value" ]
let _ = print [ "vs" ]
let _ = print [ "tps" ]
let _ = print [ "==>" ]
let _ = print [ "==>*" ]
let _ = print [ "closed" ]

(* Regression print for prop-calc *)
let _ = load "examples/prop-calc/sources.cfg"
let _ = print [ "combdefn" ]

(* Regression print for ccc *)
let _ = load "examples/ccc/sources.cfg"
let _ = print [ "conc" ]

(* Regression print for compile *)
let _ = load "examples/compile/cpm/sources.cfg"
let _ = print [ "ccp" ]
let _ = print [ "peq" ]

(* Regression print for copy *)
let _ = Twelf.loadFile "TEST/cp.elf"
let _ = print [ "cpt" ]
let _ = print [ "new" ]

(*   Regression test for Church-Rosser 
  val _ = load ""examples/church-rosser/sources.cfg""
  val _ = print [""identity""]
  val _ = print [""append""]
  val _ = print [""subst""] 
  val _ = print [""dia""] 
  val _ = print [""strip""] 
  val _ = print [""conf""]
  val _ = print [""cr""]
  val _ = print [""appd""]
  val _ = print [""lm1*""]
  val _ = print [""apr1*""]
  val _ = print [""apl1*""]
  val _ = print [""eq1""]
  val _ = print [""eq2""]

   Regression test for logic programming 
  val _ = Twelf.loadFile ""TEST/evenodd.elf""
  val _ = print [""even"", ""odd""]

*)
(* Regression test for logic programming *)
let _ = load "examples/lp-horn/sources.cfg"
let _ = print [ "can"; "atm" ]
let _ = print [ "iscan"; "isatm" ]
let _ = print [ "s_sound"; "h_sound"; "i_sound" ]
let _ = print [ "cmpcs"; "cmpai" ]

(* Regression test for logic programming *)
let _ = load "examples/lp/sources.cfg"
let _ = print [ "can"; "atm" ]
let _ = print [ "iscan"; "isatm" ]
let _ = print [ "s_sound"; "h_sound"; "i_sound" ]
let _ = print [ "cmpcs"; "cmpai" ]

(* Regression test for Cut-Elimination *)
let _ = load "examples/cut-elim/sources.cfg"
let _ = print [ "ca" ]
let _ = print [ "ce" ]
let _ = print [ "ca'" ]
let _ = print [ "ce'" ]

(* Regression test for Kolmogoroff translation *)
let _ = load "examples/kolm/sources.cfg"
let _ = print [ "kolm" ]
let _ = print [ "existskolm" ]
let _ = print [ "nj_nk" ]
let _ = print [ "equiv" ]
let _ = print [ "complete" ]

(* Regression test for compile *)
let _ = load "examples/compile/cls/sources.cfg"
let _ = test [ "trans"; "vtrans" ]
let _ = test [ "feval" ]
let _ = test [ "=>" ]
let _ = test [ ">=>*" ]
let _ = test [ ">ceval" ]
let _ = test [ "append" ]
let _ = test [ "subcomp" ]
let _ = test [ "cev_complete" ]
let _ = test [ "<" ]
let _ = test [ "trans*" ]
let _ = test [ "spl" ]
let _ = test [ "cls_sound" ]
