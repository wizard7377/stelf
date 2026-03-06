open! Basis;;
(* General basis for parsing modules *);;
(* Author: Frank Pfenning *);;
module type PARSING = sig
                      module Stream : STREAM
                      (*
  structure Lexer : LEXER
    sharing Lexer.Stream = Stream
  *)
                      type nonrec lexResult = Lexer.token_ * Paths.region
                      type nonrec 'a parser =
                        lexResult Stream.front -> 'a * lexResult Stream.front
                      (* recursive parser (allows parsing functions that need to parse
     a signature expression to temporarily suspend themselves) *)
                      type 'a recParseResult_ =
                        | Done of 'a 
                        | Continuation of 'a recParseResult_ parser 
                      type nonrec 'a recparser = 'a recParseResult_ parser
                      (* useful combinator for recursive parsers *)
                      val
                        recwith : ('a recparser * ('a -> 'b)) -> 'b recparser
                      exception Error of string 
                      val error : (Paths.region * string) -> 'a
                      end;;
(* always raises Error *);;
(* signature PARSING *);;