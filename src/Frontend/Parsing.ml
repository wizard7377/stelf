open! Basis
open! Timing
open! Timing.Timing_
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Tabling
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Style
open! Style.Style_
open! Modes
open! Modes.Modes_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! M2
open! M2.M2_
open! Compile
open! Compile.Compile_
open! Opsem
open! Opsem.Opsem_
open! Subordinate
open! Subordinate
open! Modules
open! Modules.Modules_
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Unique
open! Unique.Unique_
open! Cover
open! Cover.Cover_
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Prover
open! Flit
open! Flit.Flit_
open! Msg
open! Msg.Msg_

(* # 1 "src/frontend/Parsing.sig.ml" *)
open! Basis

(* General basis for parsing modules *)
(* Author: Frank Pfenning *)
include PARSING

(* always raises Error *)
(* signature PARSING *)

(* # 1 "src/frontend/Parsing.fun.ml" *)
open! Basis

module MakeParsing (Stream : STREAM) (Lexer : Lexer.LEXER) : PARSING = struct
  module Stream = Stream
  module Lexer = Lexer

  (*! structure Lexer = Lexer' !*)
  type nonrec lexResult = Lexer.token * Paths.region
  type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  type 'a recParseResult =
    | Done of 'a
    | Continuation of 'a recParseResult parser

  type 'a recparser = 'a recParseResult parser

  let rec recwith recparser func f =
    begin match recparser f with
    | Done x, f' -> (Done (func x), f')
    | Continuation k, f' -> (Continuation (recwith k func), f')
    end

  exception Error of string

  let error r msg = raise (Error (Paths.wrap r msg))
end

(*! structure Lexer' : LEXER !*)
(*! sharing Lexer'.Stream = Stream' !*)
(* functor Parsing *)
module Parsing = MakeParsing (Stream) (Lexer)
module Stream = Parsing.Stream
module Lexer = Parsing.Lexer

type lexResult = Parsing.lexResult
type 'a parser = 'a Parsing.parser

type 'a recParseResult = 'a Parsing.recParseResult =
  | Done of 'a
  | Continuation of 'a Parsing.recParseResult parser

type 'a recparser = 'a Parsing.recparser

let recwith = Parsing.recwith

exception Error = Parsing.Error

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

let error = Parsing.error
(*! structure Lexer' = Lexer !*)

(* # 1 "src/frontend/Parsing.sml.ml" *)
