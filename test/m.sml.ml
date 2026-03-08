open! Basis

open! struct
  module F = FunSyn
  module I = IntSyn
  module S = StateSyn

  let rec load file =
    begin match Twelf.Config.load (Twelf.Config.read file) with
    | ok_ -> Twelf.ok_
    | abort_ -> raise Domain
    end

  let rec transformOrder' = function
    | g_, Order.Arg k ->
        let k' = I.ctxLength g_ - k + 1 in
        let (I.Dec (_, v_)) = I.ctxDec (g_, k') in
        S.Arg ((I.Root (I.BVar k', I.nil_), I.id), (v_, I.id))
    | g_, Order.Lex os_ ->
        S.Lex (map (function o_ -> transformOrder' (g_, o_)) os_)
    | g_, Order.Simul os_ ->
        S.Simul (map (function o_ -> transformOrder' (g_, o_)) os_)

  let rec transformOrder = function
    | g_, F.All (F.Prim d_, f_), os_ ->
        S.All (d_, transformOrder (I.Decl (g_, d_), f_, os_))
    | g_, F.And (f1_, f2_), o_ :: os_ ->
        S.And (transformOrder (g_, f1_, [ o_ ]), transformOrder (g_, f2_, os_))
    | g_, F.Ex _, o_ :: [] -> transformOrder' (g_, o_)

  let rec select c = try Order.selLookup c with _ -> Order.Lex []

  let rec test (depth, names) =
    let a = map (function x -> valOf (Names.nameLookup x)) names in
    let name = foldr (fun (x__op, y__op) -> x__op ^ y__op) "" names in
    let _ = Names.varReset () in
    let f_ = RelFun.convertFor a in
    let os_ = map select a in
    let _ = Twelf.chatter := 5 in
    let _ = MTPi.reset () in
    let _ = MTPi.init (depth, (f_, transformOrder (I.null_, f_, os_))) in
    let _ = raise Domain in
    let _ = MTPi.auto () in
    let _ = Twelf.chatter := 3 in
    ()
end

(* just for non-inductive types *)
let _ = Twelf.chatter := 3
let _ = FunNames.reset ()

(*
   Regression test for Mini-ML 
  val _ = load ""examples/mini-ml/test.cfg""
  val _ = Twelf.loadFile ""examples/mini-ml/reduce.elf""
  val _ = test (5,[""vs""])
  val _ = test (9, [""evalRed""])
  val _ = test [""tps""] 


  val _ = load ""examples/ccc/test.cfg"";
  val _ = test (6, [""conc""])

  val _ = load ""examples/prop-calc/test.cfg"";
  val _ = test (6, [""abst""])


   Regression test for compile 
  val _ = load ""examples/compile/cpm/test.cfg""
  val _ = test (20, [""ccf""])
  val _ = test (6, [""peqr""])


  val _ = load ""examples/lp-horn/test.cfg"";
  val _ = test (4, [""s_snd"", ""h_snd"", ""i_snd""])
  val _ = test (4, [""ss_cn"", ""hs_at"", ""is_at""])
  val _ = test (4, [""compcs"", ""compai""])
*)
let _ = load "examples/arith/test.cfg"
let _ = test (3, [ "assoc" ])
(* -----------------------
  val _ = load ""TEST/fol.cfg"";
 
  val _ = MTPGlobal.maxFill := 5
  val _ = test [""identity""]
  val _ = MTPGlobal.maxFill := 12
  val _ = test [""curry""]
  val _ = test [""uncurry""] 
  val _ = MTPGlobal.maxFill := 15
  val _ = test [""split""]  
  val _ = MTPGlobal.maxFill := 13
  val _ = test [""join""] 
*)
