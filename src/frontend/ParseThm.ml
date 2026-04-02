(* # 1 "src/frontend/ParseThm.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Theorems *)
(* Author: Carsten Schuermann *)
include ParseThm_intf
(* signature PARSE_THM *)

(* # 1 "src/frontend/ParseThm.fun.ml" *)
open! Parsing
open! Basis

(* Parsing Thm Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module ParseThm (ParseThm__0 : sig
  (*! structure Paths : PATHS *)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ThmExtSyn' : ReconThm_intf.THMEXTSYN

  (*! sharing ThmExtSyn'.Paths = Paths !*)
  (*! sharing ThmExtSyn'.ExtSyn.Paths = Paths !*)
  module ParseTerm :
    ParseTerm_intf.PARSE_TERM with module ExtSyn = ThmExtSyn'.ExtSyn
end) : PARSE_THM with module ThmExtSyn = ParseThm__0.ThmExtSyn' = struct
  (*! structure Parsing = Parsing' !*)
  module ThmExtSyn = ParseThm__0.ThmExtSyn'
  module ParseTerm = ParseThm__0.ParseTerm

  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream
    module E = ThmExtSyn
    module P = Paths

    let rec idToNat (r, name) =
      try L.stringToNat name with
      | Overflow -> Parsing.error (r, "Integer too large")
      | L.NotDigit _ -> Parsing.error (r, "Identifier not a natural number")

    let rec stripRParen = function
      | LS.Cons ((L.Rparen, r), s') -> LS.expose s'
      | LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected `)', found " ^ L.toString t)

    let rec decideRBrace = function
      | r0, (orders, LS.Cons ((L.Rbrace, r), s')) ->
          (Some (E.lex (r0, orders)), LS.expose s')
      | r0, (order, LS.Cons ((t, r), _)) ->
          Parsing.error (P.join (r0, r), "Expected `}', found " ^ L.toString t)

    let rec decideRBracket = function
      | r0, (orders, LS.Cons ((L.Rbracket, r), s')) ->
          (Some (E.simul (r0, orders)), LS.expose s')
      | r0, (order, LS.Cons ((t, r), _)) ->
          Parsing.error (P.join (r0, r), "Expected `]', found " ^ L.toString t)

    let rec decideRParen = function
      | r0, (ids, LS.Cons ((L.Rparen, r), s')) ->
          (Some (E.varg (r, ids)), LS.expose s')
      | r0, (order, LS.Cons ((t, r), _)) ->
          Parsing.error (P.join (r0, r), "Expected `)', found " ^ L.toString t)

    let rec parseIds = function
      | LS.Cons ((L.Id (L.Upper, id), r), s') ->
          let ids, f' = parseIds (LS.expose s') in
          (id :: ids, f')
      | LS.Cons (((L.Id (_, id) as t), r), s') ->
          Parsing.error
            (r, "Expecter upper case identifier, found " ^ L.toString t)
      | f -> ([], f)

    let rec parseArgPat = function
      | LS.Cons ((L.Id (L.Upper, id), r), s') ->
          let idOpts, f' = parseArgPat (LS.expose s') in
          (Some id :: idOpts, f')
      | LS.Cons ((L.Id (_, id), r), s') ->
          Parsing.error (r, "Expected upper case identifier, found " ^ id)
      | LS.Cons ((L.Underscore, r), s') ->
          let idOpts, f' = parseArgPat (LS.expose s') in
          (None :: idOpts, f')
      | f -> ([], f)

    let rec parseCallPat = function
      | LS.Cons ((L.Id (_, id), r), s') ->
          let idOpts, (LS.Cons ((_, r'), _) as f') =
            parseArgPat (LS.expose s')
          in
          ((id, idOpts, P.join (r, r')), f')
      | LS.Cons ((t, r), s) ->
          Parsing.error (r, "Expected call pattern, found token " ^ L.toString t)

    let rec parseCallPats = function
      | LS.Cons ((L.Lparen, r), s') ->
          let cpat, f' = parseCallPat (LS.expose s') in
          let cpats, f'' = parseCallPats (stripRParen f') in
          (cpat :: cpats, f'')
      | LS.Cons ((L.Dot, r), s') as f -> ([], f)
      | LS.Cons ((t, r), s) ->
          Parsing.error
            (r, "Expected call patterns, found token " ^ L.toString t)

    let rec parseOrderOpt = function
      | LS.Cons ((L.Lparen, r), s') -> decideRParen (r, parseIds (LS.expose s'))
      | LS.Cons ((L.Lbrace, r), s') ->
          decideRBrace (r, parseOrders (LS.expose s'))
      | LS.Cons ((L.Lbracket, r), s') ->
          decideRBracket (r, parseOrders (LS.expose s'))
      | LS.Cons ((L.Id (L.Upper, id), r), s') ->
          (Some (E.varg (r, [ id ])), LS.expose s')
      | LS.Cons (_, s') as f -> (None, f)

    and parseOrders f = parseOrders' (parseOrderOpt f)

    and parseOrders' = function
      | Some order, f' ->
          let orders, f'' = parseOrders f' in
          (order :: orders, f'')
      | None, f' -> ([], f')

    let rec parseOrder f = parseOrder' (parseOrderOpt f)

    and parseOrder' = function
      | Some order, f' -> (order, f')
      | None, LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected order, found " ^ L.toString t)

    let rec parseTDecl f =
      let order, f' = parseOrder f in
      let callpats, f'' = parseCallPats f' in
      (E.tdecl (order, E.callpats callpats), f'')

    let rec parseTerminates' (LS.Cons ((L.Terminates, r), s')) =
      parseTDecl (LS.expose s')

    let rec parseTotal' (LS.Cons ((L.Total, r), s')) = parseTDecl (LS.expose s')

    let rec parsePDecl = function
      | LS.Cons ((L.Id (_, id), r), s') ->
          let depth = idToNat (r, id) in
          let t', f' = parseTDecl (LS.expose s') in
          (E.prove (depth, t'), f')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t)

    let rec parseProve' (LS.Cons ((L.Prove, r), s')) = parsePDecl (LS.expose s')

    let rec parseEDecl = function
      | LS.Cons ((L.Id (_, id), r), s') ->
          let depth = idToNat (r, id) in
          let t', f' = parseTDecl (LS.expose s') in
          (E.establish (depth, t'), f')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t)

    let rec parseEstablish' (LS.Cons ((L.Establish, r), s')) =
      parseEDecl (LS.expose s')

    let rec parseAssert' (LS.Cons ((L.Assert, r), s')) =
      let callpats, f'' = parseCallPats (LS.expose s') in
      (E.assert_ (E.callpats callpats), f'')

    let rec stripRBrace = function
      | LS.Cons ((L.Rbrace, r), s') -> (LS.expose s', r)
      | LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected `}', found " ^ L.toString t)

    and parseDec (r, f) =
      let (x, yOpt), f' = ParseTerm.parseDec' f in
      let f'', r2 = stripRBrace f' in
      let dec =
        begin match yOpt with
        | None -> E.ExtSyn.dec0 (x, P.join (r, r2))
        | Some y -> E.ExtSyn.dec (x, y, P.join (r, r2))
        end
      in
      (dec, f'')

    and parseDecs' = function
      | drs_, (LS.Cons ((L.Lbrace, r), s') as bs_) ->
          let dr_, f' = parseDec (r, LS.expose s') in
          parseDecs' (E.decl (drs_, dr_), f')
      | drs_ -> drs_

    and parseDecs = function
      | LS.Cons ((L.Lbrace, r), s') as bs_ ->
          let dr_, f' = parseDec (r, LS.expose s') in
          parseDecs' (E.decl (E.null, dr_), f')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `{', found " ^ L.toString t)

    let rec parsePi = function
      | LS.Cons ((L.Id (_, "pi"), r), s') -> parseDecs (LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `pi', found " ^ L.toString t)

    let rec parseSome = function
      | gbs, LS.Cons ((L.Id (_, "some"), r), s') ->
          let g1, f' = parseDecs (LS.expose s') in
          let g2, f'' = parsePi f' in
          parseSome' ((g1, g2) :: gbs, f'')
      | gbs, (LS.Cons ((L.Id (_, "pi"), r), s') as f) ->
          let g2, f' = parsePi f in
          parseSome' ((E.null, g2) :: gbs, f')
      | gbs, (LS.Cons ((L.Rparen, r), s') as f) -> (gbs, f)
      | gbs, LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `some' or `pi', found " ^ L.toString t)

    and parseSome' = function
      | gbs, (LS.Cons ((L.Rparen, r), s') as f) -> (gbs, f)
      | gbs, LS.Cons ((L.Id (_, "|"), r), s') -> parseSome (gbs, LS.expose s')
      | gbs, LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `)' or `|', found " ^ L.toString t)

    let rec stripParen (gbs, LS.Cons ((L.Rparen, r), s')) = (gbs, LS.expose s')

    let rec parseGBs = function
      | LS.Cons ((L.Lparen, r), s') -> stripParen (parseSome ([], LS.expose s'))
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `(', found " ^ L.toString t)

    let rec forallG ((gbs', f'), r) =
      let t'', f'' = parseForallStar f' in
      (E.forallG (gbs', t''), f'')

    and forallStar ((g', f'), r) =
      let t'', f'' = parseForall f' in
      (E.forallStar (g', t''), f'')

    and forall ((g', f'), r) =
      let t'', f'' = parseExists f' in
      (E.forall (g', t''), f'')

    and exists ((g', f'), r) =
      let t'', f'' = parseTrue f' in
      (E.exists (g', t''), f'')

    and top (f', r) = (E.top, f')

    and parseTrue = function
      | LS.Cons ((L.Id (_, "true"), r), s') -> top (LS.expose s', r)
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `true', found " ^ L.toString t)

    and parseExists = function
      | LS.Cons ((L.Id (_, "exists"), r), s') ->
          exists (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "true"), r), s') -> top (LS.expose s', r)
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `exists' or `true', found " ^ L.toString t)

    and parseForall = function
      | LS.Cons ((L.Id (_, "forall"), r), s') ->
          forall (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "exists"), r), s') ->
          exists (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "true"), r), s') -> top (LS.expose s', r)
      | LS.Cons ((t, r), s') ->
          Parsing.error
            (r, "Expected `forall', `exists', or `true', found " ^ L.toString t)

    and parseForallStar = function
      | LS.Cons ((L.Id (_, "forall*"), r), s') ->
          forallStar (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "forall"), r), s') ->
          forall (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "exists"), r), s') ->
          exists (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "true"), r), s') -> top (LS.expose s', r)
      | LS.Cons ((t, r), s') ->
          Parsing.error
            ( r,
              "Expected `forall*', `forall', `exists', or `true', found "
              ^ L.toString t )

    and parseCtxScheme = function
      | LS.Cons ((L.Id (_, "forallG"), r), s') ->
          forallG (parseGBs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "forall*"), r), s') ->
          forallStar (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "forall"), r), s') ->
          forall (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "exists"), r), s') ->
          exists (parseDecs (LS.expose s'), r)
      | LS.Cons ((L.Id (_, "true"), r), s') -> top (LS.expose s', r)
      | LS.Cons ((t, r), s') ->
          Parsing.error
            ( r,
              "Expected `forallG', `forall*', `forall', `exists', or `true', \
               found " ^ L.toString t )

    let rec parseColon = function
      | LS.Cons ((L.Colon, r), s') -> parseCtxScheme (LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `:', found " ^ L.toString t)

    let rec parseThDec = function
      | LS.Cons ((L.Id (_, id), r), s') ->
          let t', f' = parseColon (LS.expose s') in
          (E.dec (id, t'), f')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected theorem identifier, found " ^ L.toString t)

    let rec parseTheoremDec' (LS.Cons ((L.Theorem, r), s')) =
      parseThDec (LS.expose s')

    let rec parsePredicate = function
      | LS.Cons ((L.Id (_, "<"), r), s') ->
          (E.predicate ("LESS", r), LS.expose s')
      | LS.Cons ((L.Id (_, "<="), r), s') ->
          (E.predicate ("LEQ", r), LS.expose s')
      | LS.Cons ((L.Equal, r), s') -> (E.predicate ("EQUAL", r), LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            (r, "Expected reduction predicate <, = or <=, found " ^ L.toString t)

    let rec parseRDecl f =
      let oOut, f1 = parseOrder f in
      let p, f2 = parsePredicate f1 in
      let oIn, f3 = parseOrder f2 in
      let callpats, f4 = parseCallPats f3 in
      (E.rdecl (p, oOut, oIn, E.callpats callpats), f4)

    let rec parseReduces' (LS.Cons ((L.Reduces, r), s')) =
      parseRDecl (LS.expose s')

    let rec parseTabledDecl (LS.Cons ((L.Id (_, id), r), s') as f) =
      begin match LS.expose s' with
      | LS.Cons ((L.Dot, r'), s) as f -> (E.tableddecl (id, r), f)
      | _ -> Parsing.error (r, "Expected .")
      end

    let rec parseTabled' (LS.Cons ((L.Tabled, r), s')) =
      parseTabledDecl (LS.expose s')

    let rec parseKeepTableDecl (LS.Cons ((L.Id (_, id), r), s') as f) =
      begin match LS.expose s' with
      | LS.Cons ((L.Dot, r'), s) as f -> (E.keepTabledecl (id, r), f)
      | _ -> Parsing.error (r, "Expected .")
      end

    let rec parseKeepTable' (LS.Cons ((L.Keeptable, r), s')) =
      parseKeepTableDecl (LS.expose s')

    let rec parseWDecl f =
      let qids, f1 = ParseTerm.parseQualIds' f in
      let callpats, f2 = parseCallPats f1 in
      (E.wdecl (qids, E.callpats callpats), f2)

    let rec parseWorlds' (LS.Cons ((L.Worlds, r), s')) =
      parseWDecl (LS.expose s')
  end

  (*--------------------------*)
  (* %terminates declarations *)
  (*--------------------------*)
  (* idToNat (region, (idCase, name)) = n
       where n an natural number indicated by name, which should consist
       of all digits.  Raises error otherwise, or if integer it too large
    *)
  (* parseIds ""id ... id"" = [""id"",...,""id""] *)
  (* terminated by non-identifier token *)
  (* parseArgPat ""_id ... _id"" = [idOpt,...,idOpt] *)
  (* terminated by token different from underscore or id *)
  (* parseCallPat ""id _id ... _id"" = (id, region, [idOpt,...,idOpt]) *)
  (* parseCallPats ""(id _id ... _id)...(id _id ... _id)."" *)
  (* Parens around call patterns no longer optional *)
  (* order ::= id | (id ... id)   virtual arguments = subterm ordering
               | {order ... order}  lexicgraphic order
               | [order ... order]  simultaneous order
    *)
  (* parseOrderOpt (f) = (SOME(order), f') or (NONE, f) *)
  (* returns an optional order and front of remaining stream *)
  (* parseOrders (f) = ([order1,...,ordern], f') *)
  (* returns a sequence of orders and remaining front of stream *)
  (* parseOrder (f) = (order, f') *)
  (* returns an order and front of remaining stream *)
  (* parseTDecl ""order callPats."" *)
  (* parses Termination Declaration, followed by `.' *)
  (* parseTerminates' ""%terminates tdecl."" *)
  (* ------------------- *)
  (* %total declaration  *)
  (* ------------------- *)
  (* parseTotal' ""%total tdecl."" *)
  (* ------------------- *)
  (* %prove declarations *)
  (* ------------------- *)
  (* parsePDecl ""id nat order callpats."" *)
  (* parseProve' ""%prove pdecl."" *)
  (* ----------------------- *)
  (* %establish declarations *)
  (* ----------------------- *)
  (* parseEDecl ""id nat order callpats."" *)
  (* parseEstablish' ""%establish pdecl."" *)
  (* -------------------- *)
  (* %assert declarations *)
  (* -------------------- *)
  (* parseAssert' ""%assert cp"" *)
  (* --------------------- *)
  (* %theorem declarations *)
  (* --------------------- *)
  (* parseDec ""{id:term} | {id}"" *)
  (* parseDecs' ""{id:term}...{id:term}"", zero or more, "":term"" optional *)
  (* parseDecs ""{id:term}...{id:term}"", one ore more, "":term"" optional *)
  (* parseTrue ""true"" *)
  (* parseExists ""exists decs mform | mform"" *)
  (* parseForall ""forall decs mform | mform"" *)
  (* parseForallStar ""forall* decs mform | mform"" *)
  (* parseColon "": mform"" *)
  (* parseThDec ""id : mform"" *)
  (* parseTheoremDec' ""%theorem thdec."" *)
  (* We enforce the quantifier alternation restriction syntactically *)
  (*  -bp6/5/99. *)
  (* parsePredicate f = (pred, f')               *)
  (* parses the reduction predicate, <, <=, =   *)
  (* parseRDecl ""order callPats."" *)
  (* parses Reducer Declaration, followed by `.' *)
  (* parseReduces' ""%reduces thedec. "" *)
  (* parseTabled' ""%tabled thedec. "" *)
  (* parseKeepTable' ""%keepTabled thedec. "" *)
  (*       val (GBs, f1) = parseGBs f *)
  let parseTotal' = parseTotal'
  let parseTerminates' = parseTerminates'
  let parseTheorem' = parseForallStar
  let parseTheoremDec' = parseTheoremDec'
  let parseProve' = parseProve'
  let parseEstablish' = parseEstablish'
  let parseAssert' = parseAssert'
  let parseReduces' = parseReduces'

  (*  -bp  6/05/99.*)
  let parseTabled' = parseTabled'

  (*  -bp 20/11/01.*)
  let parseKeepTable' = parseKeepTable'

  (*  -bp 20/11/01.*)
  let parseWorlds' = parseWorlds'
end
(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
(* local ... in *)
(* functor Parser *)

(* # 1 "src/frontend/ParseThm.sml.ml" *)
