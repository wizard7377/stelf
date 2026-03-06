open! Basis;;
(* Weak Head-Normal Forms *);;
(* Authors: Frank Pfenning, Carsten Schuermann *);;
module type WHNF = sig
                   (*! structure IntSyn : INTSYN !*)
                   (* Patterns *)
                   val isPatSub : IntSyn.sub_ -> bool
                   val makePatSub : IntSyn.sub_ -> IntSyn.sub_ option
                   val dotEta : (IntSyn.front_ * IntSyn.sub_) -> IntSyn.sub_
                   exception Eta 
                   val etaContract : IntSyn.exp_ -> int
                   (* can raise Eta *)
                   (* Weak head normalization *)
                   val whnf : IntSyn.eclo -> IntSyn.eclo
                   val expandDef : IntSyn.eclo -> IntSyn.eclo
                   val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
                   val etaExpandRoot : IntSyn.exp_ -> IntSyn.exp_
                   val
                     whnfEta : (IntSyn.eclo * IntSyn.eclo) ->
                               IntSyn.eclo * IntSyn.eclo
                   val lowerEVar : IntSyn.exp_ -> IntSyn.exp_
                   val
                     newLoweredEVar : (IntSyn.dctx * IntSyn.eclo) ->
                                      IntSyn.exp_
                   val
                     newSpineVar : (IntSyn.dctx * IntSyn.eclo) ->
                                   IntSyn.spine_
                   val
                     spineToSub : (IntSyn.spine_ * IntSyn.sub_) ->
                                  IntSyn.sub_
                   (* Full normalization *)
                   val normalize : IntSyn.eclo -> IntSyn.exp_
                   val
                     normalizeDec : (IntSyn.dec_ * IntSyn.sub_) ->
                                    IntSyn.dec_
                   val normalizeCtx : IntSyn.dctx -> IntSyn.dctx
                   (* Inverting substitutions *)
                   val invert : IntSyn.sub_ -> IntSyn.sub_
                   val
                     strengthen : (IntSyn.sub_ * IntSyn.dctx) -> IntSyn.dctx
                   val isId : IntSyn.sub_ -> bool
                   val cloInv : (IntSyn.exp_ * IntSyn.sub_) -> IntSyn.exp_
                   val compInv : (IntSyn.sub_ * IntSyn.sub_) -> IntSyn.sub_
                   end;;
(* signature WHNF *);;