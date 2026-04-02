(* # 1 "src/terminate/Terminate_.sig.ml" *)

(* # 1 "src/terminate/Terminate_.fun.ml" *)

(* # 1 "src/terminate/Terminate_.sml.ml" *)
open! Basis
open Checking
open Reduces

module type CHECKING = CHECKING
module type REDUCES = REDUCES

module Checking : CHECKING
module Reduces : REDUCES
