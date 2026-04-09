(** {1 STELF Parser Combinators}

		This module implements the reusable parser state machine used by STELF.
		Concrete grammar productions are expected to live in [Grammar]; this layer
		only provides parser composition, warnings, and error propagation. *)

module type PARSER = Parser_intf.PARSER
module type S = Parser_intf.S
open Parser_intf
module Make_Parser (N : sig type t end) (L : Lexer.LEXER) : PARSER with module Lexer = L with type node = N.t = struct
	module Lexer = L

	type error = string
	type warning = string
	type info = { warnings : (warning * Lexer.pos) list }
	type node = N.t
	type ('a, 's) parse = Success of 'a * 's * info | ParseError of (error * Lexer.pos) list
	type ('a, 's) t = {
		recover : bool;
		description : node description;
		action : Lexer.lexbuf -> 's -> ('a, 's) parse * Lexer.lexbuf;
	}

	let make ?(recover = true) ?(description = Parser_intf.Empty) action = { recover; description; action }
	let note node p = make ~recover:p.recover ~description:(Parser_intf.Form (node, p.description)) p.action
	let empty_info = { warnings = [] } 

	let append_info left right = { warnings = left.warnings @ right.warnings }

	let run (parser : ('a, 's) t) (lexbuf : Lexer.lexbuf) (state : 's) :
			('a, 's) parse * Lexer.lexbuf =
		parser.action lexbuf state

	let fc (f : Tag.Pos.range -> 'a -> 'b) (parser : ('a, 's) t) : ('b, 's) t =
		make (fun lexbuf state ->
				match run parser lexbuf state with
				| (ParseError errors, new_lexbuf) -> (ParseError errors, new_lexbuf)
				| (Success (value, state', info), new_lexbuf) ->
						let start_pos = Lexer.get_pos lexbuf in
						let end_pos = Lexer.get_pos new_lexbuf in
						let range = Tag.Pos.make_range start_pos end_pos in
						(Success (f range value, state', info), new_lexbuf))

	let lex (parser : 'a Lexer.t) : ('a, 's) t =
		make (fun lexbuf state ->
				match Lexer.run parser lexbuf with
				| Some (new_lexbuf, value) -> (Success (value, state, empty_info), new_lexbuf)
				| None -> (ParseError [ ("lexing failed", Lexer.get_pos lexbuf) ], lexbuf))

	let warn (warning : warning) : (unit, 's) t =
	make ~description:(Parser_intf.Token warning) (fun lexbuf state ->
				(Success ((), state, { warnings = [ (warning, Lexer.get_pos lexbuf) ] }), lexbuf))

	let err (error : error) : ('a, 's) t =
		make ~description:(Parser_intf.Token error) (fun lexbuf _state -> (ParseError [ (error, Lexer.get_pos lexbuf) ], lexbuf))

	let map (f : 'a -> 'b) (parser : ('a, 's) t) : ('b, 's) t =
		make ~recover:parser.recover ~description:parser.description (fun lexbuf ->
				fun state ->
					match run parser lexbuf state with
					| (ParseError errors, new_lexbuf) -> (ParseError errors, new_lexbuf)
					| (Success (value, state', info), new_lexbuf) ->
							(Success (f value, state', info), new_lexbuf))

	let bind (parser : ('a, 's) t) (f : 'a -> ('b, 's) t) : ('b, 's) t =
		make ~recover:parser.recover (fun lexbuf ->
				fun state ->
					match run parser lexbuf state with
					| (ParseError errors, new_lexbuf) -> (ParseError errors, new_lexbuf)
					| (Success (value, state', info1), new_lexbuf) -> (
							match run (f value) new_lexbuf state' with
							| (ParseError errors, final_lexbuf) -> (ParseError errors, final_lexbuf)
							| (Success (result, state'', info2), final_lexbuf) ->
									(Success (result, state'', append_info info1 info2), final_lexbuf)))

	let pure (value : 'a) : ('a, 's) t =
		make (fun lexbuf state -> (Success (value, state, empty_info), lexbuf))

	let ( let* ) = bind

	let ( let+ ) (parser : ('a, 's) t) (f : 'a -> 'b) : ('b, 's) t = map f parser

	let ( and+ ) (left : ('a, 's) t) (right : ('b, 's) t) : (('a * 'b), 's) t =
		make ~recover:(left.recover && right.recover) (fun lexbuf ->
				fun state ->
					match run left lexbuf state with
					| (ParseError errors, new_lexbuf) -> (ParseError errors, new_lexbuf)
					| (Success (left_value, state', info1), new_lexbuf) -> (
							match run right new_lexbuf state' with
							| (ParseError errors, final_lexbuf) -> (ParseError errors, final_lexbuf)
							| (Success (right_value, state'', info2), final_lexbuf) ->
									( Success
											((left_value, right_value), state'', append_info info1 info2),
											final_lexbuf )))

	let ( and* ) = ( and+ )

	let seq (parser : ('a, 's) t) (f : 'a -> ('b, 's) t) : ('b, 's) t = bind parser f

	let seq_ (left : ('a, 's) t) (right : ('b, 's) t) : ('b, 's) t =
		seq left (fun _ -> right)

	let rec alt (parsers : ('a, 's) t list) : ('a, 's) t =
		make (fun lexbuf ->
				fun state ->
					match parsers with
					| [] -> (ParseError [ ("no parser matched", Lexer.get_pos lexbuf) ], lexbuf)
					| parser :: rest -> (
							match run parser lexbuf state with
							| (Success _ as result, new_lexbuf) -> (result, new_lexbuf)
							| (ParseError _ as result, new_lexbuf) ->
									if parser.recover then run (alt rest) lexbuf state
									else (result, new_lexbuf)))

	let alt_ (branches : ((unit, 's) t * ('a, 's) t) list) : ('a, 's) t =
		alt (List.map (fun (prefix, parser) -> seq_ prefix parser) branches)

	let many (parser : ('a, 's) t) : ('a list, 's) t =
		make (fun lexbuf ->
				fun state ->
					let rec loop acc info current_lexbuf current_state =
						match run parser current_lexbuf current_state with
						| (ParseError _, _) ->
								(Success (List.rev acc, current_state, info), current_lexbuf)
						| (Success (value, next_state, parsed_info), new_lexbuf) ->
							if Lexer.get_offset new_lexbuf = Lexer.get_offset current_lexbuf then
								invalid_arg "Parser.many: parser must consume input"
								else
									loop
											(value :: acc)
											(append_info info parsed_info)
											new_lexbuf
											next_state
					in
					loop [] empty_info lexbuf state)

	let many1 (parser : ('a, 's) t) : ('a list, 's) t =
		make ~recover:parser.recover (fun lexbuf ->
				fun state ->
					match run parser lexbuf state with
					| (ParseError errors, new_lexbuf) -> (ParseError errors, new_lexbuf)
					| (Success (value, state', info), new_lexbuf) ->
							if Lexer.get_offset new_lexbuf = Lexer.get_offset lexbuf then
								invalid_arg "Parser.many1: parser must consume input"
							else
								match run (many parser) new_lexbuf state' with
								| (Success (values, state'', rest_info), final_lexbuf) ->
										( Success
												(value :: values, state'', append_info info rest_info),
												final_lexbuf )
								| (ParseError errors, final_lexbuf) ->
										(ParseError errors, final_lexbuf))

	let opt (parser : ('a, 's) t) : (('a option), 's) t =
		alt [ map (fun value -> Some value) parser; pure None ]

	let sep_by1 (item : ('a, 's) t) (separator : ('b, 's) t) : ('a list, 's) t =
		seq item (fun first -> map (fun rest -> first :: rest) (many (seq_ separator item)))

	let sep_by (item : ('a, 's) t) (separator : ('b, 's) t) : ('a list, 's) t =
		alt [ sep_by1 item separator; pure [] ]

	let between (left : (unit, 's) t) (parser : ('a, 's) t) (right : (unit, 's) t) :
			('a, 's) t =
		seq_ left (seq parser (fun value -> seq_ right (pure value)))

	let token (parser : ('a, 's) t) : (unit, 's) t = seq_ parser (pure ())
	let keyword (kw : string) : (unit, 's) t = token (lex (Lexer.keyword kw))

	module Monad = struct
		let map = map
		let bind = bind
		let ( let* ) parser f = bind parser f
		let ( let+ ) parser f = map f parser
		let ( and+ ) left right =
			bind left (fun left_value -> map (fun right_value -> (left_value, right_value)) right)
		let ( and* ) = ( and+ )
		let ( << ) x y = bind x (fun left_value -> map (fun _ -> left_value) y)
		let ( >> ) x y = bind x (fun _ -> y)

		let pure = pure

		let get_state : ('s, 's) t =
			{
				recover = true;
				description = Parser_intf.Empty;
				action = (fun lexbuf state -> (Success (state, state, empty_info), lexbuf));
			}

		let set_state (state' : 's) : (unit, 's) t =
			make (fun lexbuf _state -> (Success ((), state', empty_info), lexbuf))

		let fix (f : ('a, 's) t -> ('a, 's) t) : ('a, 's) t =
			let rec parser = lazy (f (Lazy.force parser)) in
			make (fun lexbuf state -> run (Lazy.force parser) lexbuf state)
	end

	let debug (parser : ('a, 's) t) (state : 's) (input : string) : ('a, error list) result =
		match run parser (Lexer.of_string input) state with
		| (Success (value, _state, _info), _) -> Ok value
		| (ParseError errors, _) -> Error (List.map fst errors)

	let commit : (unit, 's) t =
		{
			recover = false;
			description = Parser_intf.Empty;
			action = (fun lexbuf state -> (Success ((), state, empty_info), lexbuf));
		}
end

module Sugar (P : PARSER) : S with module Lexer = P.Lexer = struct
	include P
end