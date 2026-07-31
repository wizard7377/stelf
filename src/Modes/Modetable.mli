open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_
include module type of MODETABLE
module MakeModeTable (Table : TABLE with type key = int) : MODETABLE
