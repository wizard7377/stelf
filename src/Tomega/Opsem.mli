open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Cover
open! Cover.Cover_
open! Formatter
open! Formatter__Formatter_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Modes
open! Modes.Modes_
open! Trail
open! Trail.Trail_
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
