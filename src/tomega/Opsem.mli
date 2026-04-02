include module type of Opsem_intf

module MakeOpsem
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK)
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (Unify : UNIFY) :
  OPSEM
(*
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann, Adam Poswolsky *)
*)
