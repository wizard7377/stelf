include module type of OPSEM

module MakeOpsem
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK)
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (Unify : UNIFY) : OPSEM
(*
  (* Internal syntax for functional proof term calculus *)
  (* Author: Carsten Schuermann, Adam Poswolsky *)
*)
