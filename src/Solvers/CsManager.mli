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
include module type of CSMANAGER
include CS_MANAGER

module MakeCsManager (Global : GLOBAL) (Unify : UNIFY) (Fixity : FIXITY) :
  CS_MANAGER with module Fixity = Fixity
(*
  (*! structure IntSyn : INTSYN !*)
  (*! sharing Unify.IntSyn = IntSyn !*)
*)
