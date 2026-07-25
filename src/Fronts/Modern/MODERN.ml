module type MODERN = sig
  module Paths : Paths.PATHS.PATHS
  module Cst : Cst.CST
  module Names : Names.NAMES.NAMES
  module N := Names
  module FX := N.Fixity
  module Parser : Parsing.PARSER.PARSER

  type 'a t = 'a Parser.t

  exception ParseError of string

  exception
    FullParseError of {
      title : Display.form option;
      subtitle : Display.form option;
      body : Display.form;
      loc : Cst.loc option;
    }

  val given_symbols : (string * string) list ref
  (** A list of symbols that refer to restricted names *)

  val parse_expr1 : unit -> Cst.Term.t t
  val parse_expr : unit -> Cst.Term.t t
  val parse_var : unit -> string t

  val parse_qualified : unit -> Cst.symbol t
  (** {v %val ( ... ) v} *)

  val parse_text : unit -> string t
  val parse_decl : unit -> Cst.decl t
  val parse_decl_simple : unit -> Cst.decl t
  val parse_mode : unit -> Cst.mode t
  val parse_mode_dec : unit -> Cst.modeDec t
  val parse_sigexp : unit -> Cst.sigexp t
  val parse_inst : unit -> Cst.inst t
  val parse_sigdef : unit -> Cst.sigdef t
  val parse_struct_dec : unit -> Cst.structDec t
  val parse_fixity : unit -> int t
  val parse_query : unit -> (int option * int option * int option * Cst.query) t
  val parse_define : unit -> Cst.define t
  val parse_solve : unit -> Cst.solve t
  val parse_bound : unit -> int option t
  val parse_id_list : unit -> string list t
  val parse_reduces_rel : unit -> string t
  val parse_block_item : unit -> Cst.block_item t
  val parse_fixity_kw : unit -> Cst.fixity t
  val parse_params : unit -> string list t
  val register_local_fixity : Cst.fixity -> int -> string list -> unit
  val parse_group : 'a t -> 'a list t
  val parse_parens : 'a t -> 'a t
  val parse_braced : 'a t -> 'a t
  val parse_bracketed : 'a t -> 'a t

  val debug_parser : 'a t -> string -> 'a
  [@@alert debug "This should only be used in the REPL"]

  val debug_parser_with_ops : (string * FX.fixity) list -> 'a t -> string -> 'a
  [@@alert debug "This should only be used in the REPL"]

  val run : 'a t -> N.namespace ref -> Cst.loc -> string -> 'a
end
