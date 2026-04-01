(* # 1 "src/frontend/lexer.sig.ml" *)
open! Basis

(* Lexer *)
(* Author: Frank Pfenning *)

module type LEXER = sig
  (* Stream is not memoizing for efficiency *)
  module Stream : STREAM

  (*! structure Paths : PATHS !*)
  type idCase = Upper | Lower | Quoted

  (* [A-Z]<id> or _<id> *)
  (* any other <id> *)
  (* '<id>', currently unused *)
  type token =
    | Eof
    | Dot
    | Pathsep
    | Colon
    | Lparen
    | Rparen
    | Lbracket
    | Rbracket
    | Lbrace
    | Rbrace
    | Backarrow
    | Arrow
    | Type
    | Equal
    | Id of idCase * string
    | Underscore
    | Infix
    | Prefix
    | Postfix
    | Name
    | Define
    | Solve
    | Query
    | Fquery
    | Compile
    | Querytabled
    | Mode
    | Unique
    | Covers
    | Total
    | Terminates
    | Block
    | Worlds
    | Reduces
    | Tabled
    | Keeptable
    | Theorem
    | Prove
    | Establish
    | Assert
    | Abbrev
    | Trustme
    | Freeze
    | Thaw
    | Subord
    | Deterministic
    | Clause
    | Sig
    | Struct
    | Where
    | Include
    | Open
    | Use
    | String of string

  (* end of file or stream, also `%.' *)
  (* `.' *)
  (* `.' between <id>s *)
  (* `:' *)
  (* `(' `)' *)
  (* `[' `]' *)
  (* `{' `}' *)
  (* `<-' `->' *)
  (* `type' *)
  (* `=' *)
  (* identifer *)
  (* `_' *)
  (* `%infix' `%prefix' `%postfix' *)
  (* `%name' *)
  (* `%define' *)
  (* -rv 8/27/01 *)
  (* `%solve' *)
  (* `%query' *)
  (* `%fquery' *)
  (* '%compile' *)
  (* -ABP 4/4/03 *)
  (* `%querytabled' *)
  (* `%mode' *)
  (* `%unique' *)
  (* -fp 8/17/03 *)
  (* `%covers' *)
  (* -fp 3/7/01 *)
  (* `%total' *)
  (* -fp 3/18/01 *)
  (* `%terminates' *)
  (* `%block' *)
  (* -cs 5/29/01 *)
  (* `%worlds' *)
  (* `%reduces' *)
  (* -bp 6/5/99 *)
  (* `%tabled' *)
  (* -bp 6/5/99 *)
  (* `%keepTable' *)
  (* -bp 04/11/04 *)
  (* `%theorem' *)
  (* `%prove' *)
  (* `%establish' *)
  (* `%assert' *)
  (* `%abbrev' *)
  (* `%trustme' *)
  (* `%freeze' *)
  (* `%thaw' *)
  (* `%subord' *)
  (* -gaw 07/11/08 *)
  (* `%deterministic' *)
  (* -rv 11/27/01 *)
  (* `%clause' *)
  (* -fp 8/9/02 *)
  (* `%sig' *)
  (* `%struct' *)
  (* `%where' *)
  (* `%include' *)
  (* `%open' *)
  (* `%use'    *)
  (* string constants *)
  exception Error of string

  (* lexer returns an infinite stream, terminated by EOF token *)
  val lexStream : TextIO.instream -> (token * Paths.region) Stream.stream
  val lexTerminal : string * string -> (token * Paths.region) Stream.stream
  val toString : token -> string
  val lex : (int -> string) -> (token * Paths.region) Stream.stream

  (* Utilities *)
  exception NotDigit of char

  val stringToNat : string -> int
  val isUpper : string -> bool
end
