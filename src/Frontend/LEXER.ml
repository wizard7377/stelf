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

(* # 1 "src/frontend/Lexer.sig.ml" *)
open! Basis

(** Lexer interface. Author: Frank Pfenning. *)

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

  val lexStream : TextIO.instream -> (token * Paths.region) Stream.stream
  (** [lexStream instream] returns an infinite token stream terminated by [Eof].
  *)

  val lexTerminal : string * string -> (token * Paths.region) Stream.stream
  val toString : token -> string

  val lex : (int -> string) -> (token * Paths.region) Stream.stream
  (** [lex inputFun] tokenizes input read line by line from [inputFun]. *)

  (* Utilities *)
  exception NotDigit of char

  val stringToNat : string -> int
  (** Convert a decimal string to an integer. *)

  val isUpper : string -> bool
  (** True when a string starts with an uppercase letter or underscore. *)
end
