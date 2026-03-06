open! Basis;;
(* Internal syntax for Delphin *);;
(* Author: Carsten Schuermann *);;
module type TOMEGA = sig
                     (*! structure IntSyn : INTSYN !*)
                     (* make abstract *)
                     type nonrec label = int
                     type nonrec lemma = int
                     type worlds_ = | Worlds of IntSyn.cid list 
                     type quantifier_ = | Implicit 
                                        | Explicit 
                     type tC_ =
                       | Abs of IntSyn.dec_ * tC_ 
                       | Conj of tC_ * tC_ 
                       | Base of
                         ((IntSyn.exp_ * IntSyn.sub_) *
                          (IntSyn.exp_ * IntSyn.sub_))
                         Order.order_ 
                     (* Terminiation Condition     *)
                     (* T ::= {{D}} O              *)
                     (*     | O1 ^ O2              *)
                     type for_ =
                       | World of worlds_ * for_ 
                       | All of (dec_ * quantifier_) * for_ 
                       | Ex of (IntSyn.dec_ * quantifier_) * for_ 
                       | True 
                       | And of for_ * for_ 
                       | FClo of for_ * sub_ 
                       | FVar of dec_ IntSyn.ctx_ * for_ option ref 
                     and dec_ =
                       | UDec of IntSyn.dec_ 
                       | PDec of
                         string option * for_ * tC_ option * tC_ option 
                     and prg_ =
                       | Box of worlds_ * prg_ 
                       | Lam of dec_ * prg_ 
                       | New of prg_ 
                       | Choose of prg_ 
                       | PairExp of IntSyn.exp_ * prg_ 
                       | PairBlock of IntSyn.block_ * prg_ 
                       | PairPrg of prg_ * prg_ 
                       | Unit 
                       | Redex of prg_ * spine_ 
                       | Rec of dec_ * prg_ 
                       | Case of cases_ 
                       | PClo of prg_ * sub_ 
                       | Let of dec_ * prg_ * prg_ 
                       | EVar of
                         dec_
                         IntSyn.ctx_ *
                         prg_
                         option
                         ref *
                         for_ *
                         tC_
                         option *
                         tC_
                         option *
                         IntSyn.exp_ 
                       | Const of lemma 
                       | Var of int 
                       | LetPairExp of IntSyn.dec_ * dec_ * prg_ * prg_ 
                       | LetUnit of prg_ * prg_ 
                     and spine_ =
                       | Nil 
                       | AppExp of IntSyn.exp_ * spine_ 
                       | AppBlock of IntSyn.block_ * spine_ 
                       | AppPrg of prg_ * spine_ 
                       | SClo of spine_ * sub_ 
                     and sub_ = | Shift of int 
                                | Dot of front_ * sub_ 
                     and front_ =
                       | Idx of int 
                       | Prg of prg_ 
                       | Exp of IntSyn.exp_ 
                       | Block of IntSyn.block_ 
                       | Undef 
                     and cases_ =
                       | Cases of (dec_ IntSyn.ctx_ * sub_ * prg_) list 
                     (* Formulas                   *)
                     (* F ::= World l1...ln. F     *)
                     (*     | All LD. F            *)
                     (*     | Ex  D. F             *)
                     (*     | T                    *)
                     (*     | F1 ^ F2              *)
                     (*     | F [t]                *)
                     (*     | F (G)                *)
                     (* Declaration:               *)
                     (* D ::= x:A                  *)
                     (*     | xx :: F              *)
                     (* Programs:                  *)
                     (*     | box W. P             *)
                     (*     | lam LD. P            *)
                     (*     | new P                *)
                     (*     | choose P             *)
                     (*     | <M, P>               *)
                     (*     | <rho, P>             *)
                     (*     | <P1, P2>             *)
                     (*     | <>                   *)
                     (*     | mu xx. P             *)
                     (*     | case t of O          *)
                     (*     | P [t]                *)
                     (*     | let D = P1 in P2     *)
                     (*     | E (G, F, _, _, X)    *)
                     (* X is just just for printing*)
                     (* P ::= cc                   *)
                     (*     | xx                   *)
                     (* Spines:                    *)
                     (* S ::= Nil                  *)
                     (*     | P U                  *)
                     (*     | P rho                *)
                     (*     | P1 P2                *)
                     (*     | S [t]                *)
                     (* Substitutions:             *)
                     (* t ::= ^n                   *)
                     (*     | F . t                *)
                     (* Fronts:                    *)
                     (* F ::= i                    *)
                     (*     | p                    *)
                     (*     | U                    *)
                     (*     | _x                   *)
                     (*     | _                    *)
                     (* Cases                      *)
                     (* C ::= (Psi' |> s |-> P)    *)
                     type conDec_ =
                       | ForDec of string * for_ 
                       | ValDec of string * prg_ * for_ 
                     (* ConDec                     *)
                     (* CD ::= f :: F              *)
                     (*      | f == P              *)
                     exception NoMatch 
                     val coerceSub : sub_ -> IntSyn.sub_
                     val embedSub : IntSyn.sub_ -> sub_
                     val
                       coerceCtx : dec_
                                   IntSyn.ctx_ ->
                                   IntSyn.dec_
                                   IntSyn.ctx_
                     val
                       strengthenCtx : dec_
                                       IntSyn.ctx_ ->
                                       IntSyn.dec_ IntSyn.ctx_ * sub_ * sub_
                     val
                       embedCtx : IntSyn.dec_ IntSyn.ctx_ -> dec_ IntSyn.ctx_
                     val weakenSub : dec_ IntSyn.ctx_ -> sub_
                     val invertSub : sub_ -> sub_
                     val id : sub_
                     val shift : sub_
                     val dot1 : sub_ -> sub_
                     val dotEta : (front_ * sub_) -> sub_
                     val comp : (sub_ * sub_) -> sub_
                     val varSub : (int * sub_) -> front_
                     val decSub : (dec_ * sub_) -> dec_
                     val forSub : (for_ * sub_) -> for_
                     val whnfFor : (for_ * sub_) -> for_ * sub_
                     val normalizePrg : (prg_ * sub_) -> prg_
                     val normalizeSub : sub_ -> sub_
                     val derefPrg : prg_ -> prg_
                     val lemmaLookup : lemma -> conDec_
                     val lemmaName : string -> lemma
                     val lemmaAdd : conDec_ -> lemma
                     val lemmaSize : unit -> int
                     val lemmaDef : lemma -> prg_
                     val lemmaFor : lemma -> for_
                     val eqWorlds : (worlds_ * worlds_) -> bool
                     val convFor : ((for_ * sub_) * (for_ * sub_)) -> bool
                     val newEVar : (dec_ IntSyn.ctx_ * for_) -> prg_
                     val
                       newEVarTC : (dec_
                                    IntSyn.ctx_ *
                                    for_ *
                                    tC_
                                    option *
                                    tC_
                                    option) ->
                                   prg_
                     (* Below are added by Yu Liao *)
                     val ctxDec : (dec_ IntSyn.ctx_ * int) -> dec_
                     val revCoerceSub : IntSyn.sub_ -> sub_
                     val
                       revCoerceCtx : IntSyn.dec_
                                      IntSyn.ctx_ ->
                                      dec_
                                      IntSyn.ctx_
                     (* Added references by ABP *)
                     val coerceFront : front_ -> IntSyn.front_
                     val revCoerceFront : IntSyn.front_ -> front_
                     val
                       deblockify : IntSyn.dec_
                                    IntSyn.ctx_ ->
                                    IntSyn.dec_ IntSyn.ctx_ * sub_
                     (* Stuff that has to do with termination conditions *)
                     val tCSub : (tC_ * IntSyn.sub_) -> tC_
                     val normalizeTC : tC_ -> tC_
                     val convTC : (tC_ * tC_) -> bool
                     val
                       transformTC : (IntSyn.dec_
                                      IntSyn.ctx_ *
                                      for_ *
                                      int
                                      Order.order_
                                      list) ->
                                     tC_
                     end;;
(* Signature TOMEGA *);;