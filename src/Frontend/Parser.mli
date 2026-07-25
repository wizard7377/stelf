include module type of PARSER

module Parser (Parser__0 : sig
  (*! structure Parsing' : PARSING !*)
  module Stream' : STREAM

  (* result stream *)
  module ExtSyn' : RECONTERM.EXTSYN

  (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
  module Names' : NAMES
  module ExtConDec' : RECONCONDEC.EXTCONDEC
  module ExtQuery' : RECONQUERY.EXTQUERY
  module ExtModes' : RECONMODE.EXTMODES
  module ThmExtSyn' : RECONTHM.THMEXTSYN
  module ModExtSyn' : RECONMODULE.MODEXTSYN

  module ParseConDec :
    PARSECONDEC.PARSE_CONDEC with module ExtConDec = ExtConDec'

  (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
  module ParseQuery : PARSEQUERY.PARSE_QUERY with module ExtQuery = ExtQuery'

  (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
  module ParseFixity : PARSEFIXITY.PARSE_FIXITY with module Names = Names'

  (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
  module ParseMode : PARSEMODE.PARSE_MODE with module ExtModes = ExtModes'

  (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
  module ParseThm : PARSETHM.PARSE_THM with module ThmExtSyn = ThmExtSyn'

  (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
  module ParseModule :
    PARSEMODULE.PARSE_MODULE with module ModExtSyn = ModExtSyn'

  (*! sharing ParseModule.Parsing = Parsing' !*)
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ExtSyn'
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
