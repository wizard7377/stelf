(* # 1 "src/frontend/Lexer.sig.ml" *)
open! Basis

(** Lexer interface.
  Author: Frank Pfenning. *)

module type LEXER = sig
  (* Stream is not memoizing for efficiency *)
  module Stream : STREAM

  (*! structure Paths : PATHS !*)
  (** Identifier case used by the lexer. *)
  type idCase = Upper | Lower | Quoted

  (** Tokens produced by the lexer. *)
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

  (** [lexStream instream] returns an infinite token stream terminated by [Eof]. *)
  val lexStream : TextIO.instream -> (token * Paths.region) Stream.stream
  val lexTerminal : string * string -> (token * Paths.region) Stream.stream
  val toString : token -> string

  (** [lex inputFun] tokenizes input read line by line from [inputFun]. *)
  val lex : (int -> string) -> (token * Paths.region) Stream.stream

  (* Utilities *)
  exception NotDigit of char

  (** Convert a decimal string to an integer. *)
  val stringToNat : string -> int

  (** True when a string starts with an uppercase letter or underscore. *)
  val isUpper : string -> bool
end
