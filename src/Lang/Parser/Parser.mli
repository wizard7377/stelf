(** {1 STELF Parser Combinators}

	The public parser module exposes the reusable combinators that STELF syntax
	will build on. The eventual grammar-specific productions belong in
	[Grammar]; this layer stays focused on parser state, repetition, and error
	reporting. *)

module type PARSER = Parser_intf.PARSER
module type S = Parser_intf.S

module Make_Parser (N : sig type t end) (L : Lexer.LEXER) : PARSER with type node = N.t and module Lexer = L

module Sugar (P : PARSER) : S with module Lexer = P.Lexer
 