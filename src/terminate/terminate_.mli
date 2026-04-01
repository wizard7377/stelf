(* # 1 "src/terminate/terminate_.sig.ml" *)

(* # 1 "src/terminate/terminate_.fun.ml" *)

(* # 1 "src/terminate/terminate_.sml.ml" *)
open! Basis
open Checking
open Reduces

module type CHECKING = CHECKING
module type REDUCES = REDUCES

module Checking : CHECKING
module Reduces : REDUCES
