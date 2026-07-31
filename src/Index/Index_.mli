open! Basis
open! Intsyn
open! Intsyn.Lambda_
open! Table
open! Table.Table_
open! Global
open! Global.Global_
include module type of INDEX
module MakeIndex (Global : GLOBAL) (Queue : Queue.QUEUE) : INDEX
module Index : INDEX
include INDEX
