open GrammarSig

module Make_Dec
    (L : Lexer.LEXER)
    (P : Parser.PARSER with module Lexer = L)
    (I : Lambda.Intsyn.INTSYN)
    (E : GRAMMAR with module Lexer = L and module Parser = P and type t = I.exp) :
  GRAMMAR with module Lexer = L and module Parser = P and type t = I.dec and module IntSyn = I =
struct
  module Lexer = L
  module IntSyn = I
  module Parser = P

  type t = I.dec

  let parse : t Parser.t =
    let open P in
    assert false
end
  