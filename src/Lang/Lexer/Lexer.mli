(** {1 STELF Lexing Primitives}

	The public lexer module exposes the small string-based state machine used
	by the Lang parser layer. It is STELF-specific rather than a general-purpose
	lexer generator. *)

module type LEXER = Lexer_intf.LEXER
module Make_Lexer() : Lexer_intf.LEXER
module Lexer : LEXER
