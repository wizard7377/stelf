open GrammarSig

module Make_Exp
    (L : Lexer.LEXER)
    (P : Parser.PARSER with module Lexer = L)
    (I : Lambda.Intsyn.INTSYN)
    :
  GRAMMAR with module Lexer = L and module Parser = P and type t = I.exp and module IntSyn = I =
struct
  module Lexer = L
  module IntSyn = I
  module Parser = P

  type t = I.exp
  let keyword_ (kw : string) : unit Parser.t =
    P.keyword @@ "%" ^ kw

  let rec parse' : t Parser.t =
    let open P in
    let open P.Monad in 
    alt_ [
      keyword_ "star", pure (I.Uni I.Type);
      keyword "(", assert false << keyword ")";
      keyword "[", assert false << keyword "]";
      keyword "{", assert false << keyword "}"
    ]
  and parse_head : I.head Parser.t = assert false 
  and parse_spine : I.spine Parser.t = assert false 
    let parse : t Parser.t = parse'

end
 
  