open! Basis
open! Trail
open! Trail.Trail_
open! Global
open! Global.Global_
open! Domains
open! Domains.Domains_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Table
open! Table.Table_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
include module type of CSEQINTEGERS

module CsEqIntegers (CSEqIntegers__0 : sig
  (* Diophantine Equation Solver *)
  (* Author: Roberto Virga *)
  module Integers : Integers.INTEGERS

  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : CS_EQ_INTEGERS with type Integers.int = CSEqIntegers__0.Integers.int
