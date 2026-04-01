include module type of Parser_intf

module Parser (Parser__0 : sig
  (*! structure Parsing' : PARSING !*)
  module Stream' : STREAM

  (* result stream *)
  module ExtSyn' : Recon_term.EXTSYN

  (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
  module Names' : NAMES
  module ExtConDec' : Recon_condec.EXTCONDEC
  module ExtQuery' : Recon_query.EXTQUERY
  module ExtModes' : Recon_mode.EXTMODES
  module ThmExtSyn' : Recon_thm.THMEXTSYN
  module ModExtSyn' : Recon_module.MODEXTSYN

  module ParseConDec :
    Parse_condec.PARSE_CONDEC with module ExtConDec = ExtConDec'

  (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
  module ParseQuery : Parse_query.PARSE_QUERY with module ExtQuery = ExtQuery'

  (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
  module ParseFixity : Parse_fixity.PARSE_FIXITY with module Names = Names'

  (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
  module ParseMode : Parse_mode.PARSE_MODE with module ExtModes = ExtModes'

  (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
  module ParseThm : Parse_thm.PARSE_THM with module ThmExtSyn = ThmExtSyn'

  (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
  module ParseModule :
    Parse_module.PARSE_MODULE with module ModExtSyn = ModExtSyn'

  (*! sharing ParseModule.Parsing = Parsing' !*)
  module ParseTerm : Parse_term.PARSE_TERM with module ExtSyn = ExtSyn'
end) :
  PARSER
    with module ExtQuery = Parser__0.ExtQuery'
     and module Names = Parser__0.Names'
     and module ExtConDec = Parser__0.ExtConDec'
     and module ExtModes = Parser__0.ExtModes'
     and module ThmExtSyn = Parser__0.ThmExtSyn'
     and module ModExtSyn = Parser__0.ModExtSyn'
     and module Stream = Parser__0.Stream'
     and module ExtSyn = Parser__0.ExtSyn'
