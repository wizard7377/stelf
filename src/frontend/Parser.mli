include module type of Parser_intf

module Parser (Parser__0 : sig
  (*! structure Parsing' : PARSING !*)
  module Stream' : STREAM

  (* result stream *)
  module ExtSyn' : ReconTerm_intf.EXTSYN

  (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
  module Names' : NAMES
  module ExtConDec' : ReconCondec_intf.EXTCONDEC
  module ExtQuery' : ReconQuery_intf.EXTQUERY
  module ExtModes' : ReconMode_intf.EXTMODES
  module ThmExtSyn' : ReconThm_intf.THMEXTSYN
  module ModExtSyn' : ReconModule_intf.MODEXTSYN

  module ParseConDec :
    ParseCondec_intf.PARSE_CONDEC with module ExtConDec = ExtConDec'

  (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
  module ParseQuery : ParseQuery_intf.PARSE_QUERY with module ExtQuery = ExtQuery'

  (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
  module ParseFixity : ParseFixity_intf.PARSE_FIXITY with module Names = Names'

  (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
  module ParseMode : ParseMode_intf.PARSE_MODE with module ExtModes = ExtModes'

  (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
  module ParseThm : ParseThm_intf.PARSE_THM with module ThmExtSyn = ThmExtSyn'

  (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
  module ParseModule :
    ParseModule_intf.PARSE_MODULE with module ModExtSyn = ModExtSyn'

  (*! sharing ParseModule.Parsing = Parsing' !*)
  module ParseTerm : ParseTerm_intf.PARSE_TERM with module ExtSyn = ExtSyn'
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
