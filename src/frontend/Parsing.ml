(* # 1 "src/frontend/Parsing.sig.ml" *)
open! Basis

(* General basis for parsing modules *)
(* Author: Frank Pfenning *)
include Parsing_intf
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

  let rec recwith (recparser, func) f =
    begin match recparser f with
    | Done x, f' -> (Done (func x), f')
    | Continuation k, f' -> (Continuation (recwith (k, func)), f')
    end

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
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

let error = Parsing.error
(*! structure Lexer' = Lexer !*)

(* # 1 "src/frontend/Parsing.sml.ml" *)
