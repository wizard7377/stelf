(** {1 STELF Parser Combinators}

		This module implements the reusable parser state machine used by STELF.
		Concrete grammar productions are expected to live in [Grammar]; this layer
		only provides parser composition, warnings, and error propagation. *)

module type PARSER = Parser_intf.PARSER
module type S = Parser_intf.S

module Make_Parser (L : Lexer.LEXER) : PARSER with module Lexer = L = struct
	module Lexer = L

	type error = string
	type warning = string
	type info = { warnings : (warning * Lexer.pos) list }
	type 'a parse = Success of ('a * info) | ParseError of (error * Lexer.pos)
	type +'a t = Lexer.lexbuf -> 'a parse * Lexer.lexbuf

	let empty_info = { warnings = [] }

	let append_info left right = { warnings = left.warnings @ right.warnings }

	let run (parser : 'a t) (lexbuf : Lexer.lexbuf) : 'a parse * Lexer.lexbuf =
		parser lexbuf

	let lex (parser : 'a Lexer.t) : 'a t =
	 fun lexbuf ->
		match Lexer.run parser lexbuf with
		| Some (new_lexbuf, value) -> (Success (value, empty_info), new_lexbuf)
		| None -> (ParseError ("lexing failed", Lexer.get_pos lexbuf), lexbuf)

	let warn (warning : warning) : unit t =
	 fun lexbuf ->
		(Success ((), { warnings = [ (warning, Lexer.get_pos lexbuf) ] }), lexbuf)

	let err (error : error) : 'a t =
	 fun lexbuf -> (ParseError (error, Lexer.get_pos lexbuf), lexbuf)

	let map (f : 'a -> 'b) (parser : 'a t) : 'b t =
	 fun lexbuf ->
		match parser lexbuf with
		| (ParseError error, new_lexbuf) -> (ParseError error, new_lexbuf)
		| (Success (value, info), new_lexbuf) -> (Success (f value, info), new_lexbuf)

	let bind (parser : 'a t) (f : 'a -> 'b t) : 'b t =
	 fun lexbuf ->
		match parser lexbuf with
		| (ParseError error, new_lexbuf) -> (ParseError error, new_lexbuf)
		| (Success (value, info1), new_lexbuf) -> (
				match f value new_lexbuf with
				| (ParseError error, final_lexbuf) -> (ParseError error, final_lexbuf)
				| (Success (result, info2), final_lexbuf) ->
						(Success (result, append_info info1 info2), final_lexbuf))

	let pure (value : 'a) : 'a t =
	 fun lexbuf -> (Success (value, empty_info), lexbuf)

	let ( let* ) = bind

	let ( let+ ) (parser : 'a t) (f : 'a -> 'b) : 'b t = map f parser

	let ( and+ ) (left : 'a t) (right : 'b t) : ('a * 'b) t =
	 fun lexbuf ->
		match left lexbuf with
		| (ParseError error, new_lexbuf) -> (ParseError error, new_lexbuf)
		| (Success (left_value, info1), new_lexbuf) -> (
				match right new_lexbuf with
				| (ParseError error, final_lexbuf) -> (ParseError error, final_lexbuf)
				| (Success (right_value, info2), final_lexbuf) ->
						(Success ((left_value, right_value), append_info info1 info2), final_lexbuf))

	let ( and* ) = ( and+ )

	let seq (parser : 'a t) (f : 'a -> 'b t) : 'b t = bind parser f

	let seq_ (left : 'a t) (right : 'b t) : 'b t = seq left (fun _ -> right)

	let rec alt (parsers : 'a t list) : 'a t =
	 fun lexbuf ->
		match parsers with
		| [] -> (ParseError ("no parser matched", Lexer.get_pos lexbuf), lexbuf)
		| parser :: rest -> (
				match parser lexbuf with
				| (Success _ as result, new_lexbuf) -> (result, new_lexbuf)
				| (ParseError _, _) -> alt rest lexbuf)

	let alt_ (branches : (unit t * 'a t) list) : 'a t =
		alt (List.map (fun (prefix, parser) -> seq_ prefix parser) branches)

	let many (parser : 'a t) : 'a list t =
	 fun lexbuf ->
		let rec loop acc info lexbuf =
			match parser lexbuf with
			| (ParseError _, _) -> (Success (List.rev acc, info), lexbuf)
			| (Success (value, parsed_info), new_lexbuf) ->
					if Lexer.get_offset new_lexbuf = Lexer.get_offset lexbuf then
						invalid_arg "Parser.many: parser must consume input"
					else loop (value :: acc) (append_info info parsed_info) new_lexbuf
		in
		loop [] empty_info lexbuf

	let many1 (parser : 'a t) : 'a list t =
	 fun lexbuf ->
		match parser lexbuf with
		| (ParseError error, new_lexbuf) -> (ParseError error, new_lexbuf)
		| (Success (value, info), new_lexbuf) ->
				if Lexer.get_offset new_lexbuf = Lexer.get_offset lexbuf then
					invalid_arg "Parser.many1: parser must consume input"
				else
					match many parser new_lexbuf with
					| (Success (values, rest_info), final_lexbuf) ->
							(Success (value :: values, append_info info rest_info), final_lexbuf)
					| (ParseError error, final_lexbuf) -> (ParseError error, final_lexbuf)

	let opt (parser : 'a t) : 'a option t =
		alt [ map (fun value -> Some value) parser; pure None ]

	let sep_by1 (item : 'a t) (separator : 'b t) : 'a list t =
		seq item (fun first -> map (fun rest -> first :: rest) (many (seq_ separator item)))

	let sep_by (item : 'a t) (separator : 'b t) : 'a list t =
		alt [ sep_by1 item separator; pure [] ]

	let between (left : unit t) (parser : 'a t) (right : unit t) : 'a t =
		seq_ left (seq parser (fun value -> seq_ right (pure value)))

	let token (parser : 'a t) : unit t = seq_ parser (pure ())
	let keyword (kw : string) : unit t = token (lex (Lexer.keyword kw))
	module Monad = struct
		let map = map
		let bind = bind
		let ( let* ) parser f = bind parser f
		let ( let+ ) parser f = map f parser
		let ( and+ ) left right =
			bind left (fun left_value -> map (fun right_value -> (left_value, right_value)) right)
		let ( and* ) = ( and+ )
		let ( << ) x y = bind x (fun _ -> x)
		let ( >> ) x y = bind x (fun _ -> y)
		
		let pure = pure
	end
end

module Sugar (P : PARSER) : S with module Lexer = P.Lexer = struct
	include P
end