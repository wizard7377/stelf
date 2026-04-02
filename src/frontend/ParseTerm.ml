(* # 1 "src/frontend/ParseTerm.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)
include ParseTerm_intf
(* signature PARSE_TERM *)

(* # 1 "src/frontend/ParseTerm.fun.ml" *)
open! Parsing
open! Basis

(* Parsing Terms and Variable Declarations *)
(* Author: Frank Pfenning *)
module ParseTerm (ParseTerm__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtSyn' : ReconTerm_intf.EXTSYN

  (*! sharing Parsing'.Lexer.Paths = ExtSyn'.Paths !*)
  module Names : NAMES
end) : PARSE_TERM with module ExtSyn = ParseTerm__0.ExtSyn' = struct
  (*! structure Parsing = Parsing' !*)
  module ExtSyn = ParseTerm__0.ExtSyn'

  open! struct
    module L = Lexer
    module LS = Stream
    module FX = Names.Fixity

    type 'a operator =
      | Atom of 'a
      | Infix of (FX.precedence * FX.associativity) * ('a * 'a -> 'a)
      | Prefix of FX.precedence * ('a -> 'a)
      | Postfix of FX.precedence * ('a -> 'a)

    let juxOp = Infix ((FX.inc FX.maxPrec, FX.Left), ExtSyn.app)
    let arrowOp = Infix ((FX.dec FX.minPrec, FX.Right), ExtSyn.arrow)
    let backArrowOp = Infix ((FX.dec FX.minPrec, FX.Left), ExtSyn.backarrow)
    let colonOp = Infix ((FX.dec (FX.dec FX.minPrec), FX.Left), ExtSyn.hastype)

    let rec infixOp (infixity, tm) =
      Infix
        (infixity, function tm1, tm2 -> ExtSyn.app (ExtSyn.app (tm, tm1), tm2))

    let rec prefixOp (prec, tm) =
      Prefix (prec, function tm1 -> ExtSyn.app (tm, tm1))

    let rec postfixOp (prec, tm) =
      Postfix (prec, function tm1 -> ExtSyn.app (tm, tm1))

    let rec idToTerm = function
      | L.Lower, ids, name, r -> ExtSyn.lcid (ids, name, r)
      | L.Upper, ids, name, r -> ExtSyn.ucid (ids, name, r)
      | L.Quoted, ids, name, r -> ExtSyn.quid (ids, name, r)

    let isQuoted = function L.Quoted -> true | _ -> false

    type nonrec stack = ExtSyn.term operator list
    type nonrec opr = ExtSyn.term operator

    module P : sig
      val reduce : stack -> stack
      val reduceAll : Paths.region * stack -> ExtSyn.term
      val shiftAtom : ExtSyn.term * stack -> stack
      val shift : Paths.region * opr * stack -> stack
      val resolve : Paths.region * opr * stack -> stack
    end = struct
      let rec reduce = function
        | Atom tm2 :: Infix (_, con) :: Atom tm1 :: p' ->
            Atom (con (tm1, tm2)) :: p'
        | Atom tm :: Prefix (_, con) :: p' -> Atom (con tm) :: p'
        | Postfix (_, con) :: Atom tm :: p' -> Atom (con tm) :: p'

      let rec reduceRec = function
        | Atom e :: [] -> e
        | p -> reduceRec (reduce p)

      let rec reduceAll = function
        | r, Atom e :: [] -> e
        | r, Infix _ :: p' -> Parsing.error (r, "Incomplete infix expression")
        | r, Prefix _ :: p' -> Parsing.error (r, "Incomplete prefix expression")
        | r, [] -> Parsing.error (r, "Empty expression")
        | r, p -> reduceRec (reduce p)

      let rec shiftAtom = function
        | tm, (Atom _ :: p' as p) -> reduce (Atom tm :: juxOp :: p)
        | tm, p -> Atom tm :: p

      let rec shift = function
        | r, (Atom _ as opr), (Atom _ :: p' as p) -> reduce (opr :: juxOp :: p)
        | r, Infix _, Infix _ :: p' ->
            Parsing.error (r, "Consective infix operators")
        | r, Infix _, Prefix _ :: p' ->
            Parsing.error (r, "Infix operator following prefix operator")
        | r, Infix _, [] -> Parsing.error (r, "Leading infix operator")
        | r, (Prefix _ as opr), (Atom _ :: p' as p) -> opr :: juxOp :: p
        | r, Postfix _, Infix _ :: p' ->
            Parsing.error (r, "Postfix operator following infix operator")
        | r, Postfix _, Prefix _ :: p' ->
            Parsing.error (r, "Postfix operator following prefix operator")
        | r, Postfix _, [] -> Parsing.error (r, "Leading postfix operator")
        | r, opr, p -> opr :: p

      let rec resolve = function
        | ( r,
            (Infix ((prec, assoc), _) as opr),
            (Atom _ :: Infix ((prec', assoc'), _) :: p' as p) ) -> begin
            match (FX.compare (prec, prec'), assoc, assoc') with
            | Greater, _, _ -> shift (r, opr, p)
            | Less, _, _ -> resolve (r, opr, reduce p)
            | Equal, FX.Left, FX.Left -> resolve (r, opr, reduce p)
            | Equal, FX.Right, FX.Right -> shift (r, opr, p)
            | _ ->
                Parsing.error
                  (r, "Ambiguous: infix following infix of identical precedence")
          end
        | ( r,
            (Infix ((prec, assoc), _) as opr),
            (Atom _ :: Prefix (prec', _) :: p' as p) ) -> begin
            match FX.compare (prec, prec') with
            | Greater -> shift (r, opr, p)
            | Less -> resolve (r, opr, reduce p)
            | Equal ->
                Parsing.error
                  ( r,
                    "Ambiguous: infix following prefix of identical precedence"
                  )
          end
        | r, (Prefix _ as opr), p -> shift (r, opr, p)
        | ( r,
            (Postfix (prec, _) as opr),
            (Atom _ :: Prefix (prec', _) :: p' as p) ) -> begin
            match FX.compare (prec, prec') with
            | Greater -> reduce (shift (r, opr, p))
            | Less -> resolve (r, opr, reduce p)
            | Equal ->
                Parsing.error
                  ( r,
                    "Ambiguous: postfix following prefix of identical \
                     precedence" )
          end
        | ( r,
            (Postfix (prec, _) as opr),
            (Atom _ :: Infix ((prec', _), _) :: p' as p) ) -> begin
            match FX.compare (prec, prec') with
            | Greater -> reduce (shift (r, opr, p))
            | Less -> resolve (r, opr, reduce p)
            | Equal ->
                Parsing.error
                  ( r,
                    "Ambiguous: postfix following infix of identical precedence"
                  )
          end
        | r, (Postfix _ as opr), (Atom _ :: [] as p) ->
            reduce (shift (r, opr, p))
        | r, opr, p -> shift (r, opr, p)
    end

    let rec parseQualId' = function
      | LS.Cons (((L.Id (_, id) as t), r), s') as f -> begin
          match LS.expose s' with
          | LS.Cons ((L.Pathsep, _), s'') ->
              let (ids, (t, r)), f' = parseQualId' (LS.expose s'') in
              ((id :: ids, (t, r)), f')
          | f' -> (([], (t, r)), f')
        end
      | LS.Empty -> assert false (* TODO *)

    let rec stripBar = function
      | LS.Cons ((L.Id (_, "|"), r), s') -> LS.expose s'
      | LS.Cons ((L.Rparen, r), s') as f -> f
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `|', found token " ^ L.toString t)

    let rec parseQualIds1 = function
      | ls, (LS.Cons (((L.Id (_, id) as t), r0), s') as f) ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          let r = Paths.join (r0, r1) in
          let f'' = stripBar f' in
          parseQualIds1 ((ids, name) :: ls, f'')
      | ls, LS.Cons ((L.Rparen, r), s') -> (ls, LS.expose s')
      | ls, LS.Cons ((t, r), s) ->
          Parsing.error (r, "Expected label, found token " ^ L.toString t)

    let rec parseQualIds' = function
      | LS.Cons ((L.Lparen, r), s') -> parseQualIds1 ([], LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            (r, "Expected list of labels, found token " ^ L.toString t)

    let rec stripRParen = function
      | LS.Cons ((L.Rparen, r), s') -> LS.expose s'
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected closing `)', found " ^ L.toString t)

    let rec parseSubordPair2 = function
      | (LS.Cons ((L.Id _, _), _) as f), qid ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          ((qid, (ids, name)), stripRParen f')
      | LS.Cons ((t, r), s'), qid ->
          Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

    let rec parseSubordPair1 = function
      | LS.Cons ((L.Id _, _), _) as f ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          parseSubordPair2 (f', (ids, name))
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

    let rec parseSubord' = function
      | LS.Cons ((L.Lparen, r), s'), qidpairs ->
          let qidpair, f = parseSubordPair1 (LS.expose s') in
          parseSubord' (f, qidpair :: qidpairs)
      | (LS.Cons ((L.Dot, _), _) as f), qidpairs -> (List.rev qidpairs, f)
      | LS.Cons ((t, r), s'), qidpairs ->
          Parsing.error
            (r, "Expected a pair of identifiers, found token " ^ L.toString t)

    let rec parseFreeze' = function
      | (LS.Cons ((L.Id _, _), _) as f), qids ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          parseFreeze' (f', (ids, name) :: qids)
      | (LS.Cons ((L.Dot, _), _) as f), qids -> (List.rev qids, f)
      | LS.Cons ((t, r), s'), qids ->
          Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

    let rec parseThaw' (f, qids) = parseFreeze' (f, qids)

    let rec parseDeterministic' = function
      | (LS.Cons ((L.Id _, _), _) as f), qids ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          parseDeterministic' (f', (ids, name) :: qids)
      | (LS.Cons ((L.Dot, _), _) as f), qids -> (List.rev qids, f)
      | LS.Cons ((t, r), s'), qids ->
          Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

    let rec parseCompile' = function
      | (LS.Cons ((L.Id _, _), _) as f), qids ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          parseCompile' (f', (ids, name) :: qids)
      | (LS.Cons ((L.Dot, _), _) as f), qids -> (List.rev qids, f)
      | LS.Cons ((t, r), s'), qids ->
          Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

    let rec parseExp (s, p) = parseExp' (LS.expose s, p)

    and parseExp' = function
      | (LS.Cons ((L.Id _, r0), _) as f), p ->
          let (ids, (L.Id (idCase, name), r1)), f' = parseQualId' f in
          let r = Paths.join (r0, r1) in
          let tm = idToTerm (idCase, ids, name, r) in
          begin if isQuoted idCase then parseExp' (f', P.shiftAtom (tm, p))
          else begin
            match Names.fixityLookup (Names.Qid (ids, name)) with
            | FX.Nonfix -> parseExp' (f', P.shiftAtom (tm, p))
            | FX.Infix (prec, assoc) ->
                parseExp' (f', P.resolve (r, infixOp ((prec, assoc), tm), p))
            | FX.Prefix prec ->
                parseExp' (f', P.resolve (r, prefixOp (prec, tm), p))
            | FX.Postfix prec ->
                parseExp' (f', P.resolve (r, postfixOp (prec, tm), p))
          end
          end
      | LS.Cons ((L.Underscore, r), s), p ->
          parseExp (s, P.shiftAtom (ExtSyn.omitted r, p))
      | LS.Cons ((L.Type, r), s), p ->
          parseExp (s, P.shiftAtom (ExtSyn.typ r, p))
      | LS.Cons ((L.Colon, r), s), p -> parseExp (s, P.resolve (r, colonOp, p))
      | LS.Cons ((L.Backarrow, r), s), p ->
          parseExp (s, P.resolve (r, backArrowOp, p))
      | LS.Cons ((L.Arrow, r), s), p -> parseExp (s, P.resolve (r, arrowOp, p))
      | LS.Cons ((L.Lparen, r), s), p -> decideRParen (r, parseExp (s, []), p)
      | (LS.Cons ((L.Rparen, r), s) as f), p -> (P.reduceAll (r, p), f)
      | LS.Cons ((L.Lbrace, r), s), p -> decideRBrace (r, parseDec s, p)
      | (LS.Cons ((L.Rbrace, r), s) as f), p -> (P.reduceAll (r, p), f)
      | LS.Cons ((L.Lbracket, r), s), p -> decideRBracket (r, parseDec s, p)
      | (LS.Cons ((L.Rbracket, r), s) as f), p -> (P.reduceAll (r, p), f)
      | (LS.Cons ((L.Equal, r), s) as f), p -> (P.reduceAll (r, p), f)
      | (LS.Cons ((L.Dot, r), s) as f), p -> (P.reduceAll (r, p), f)
      | (LS.Cons ((L.Eof, r), s) as f), p -> (P.reduceAll (r, p), f)
      | (LS.Cons ((L.Solve, r), s) as f), p -> (P.reduceAll (r, p), f)
      | (LS.Cons ((L.Define, r), s) as f), p -> (P.reduceAll (r, p), f)
      | LS.Cons ((L.String str, r), s), p ->
          parseExp (s, P.shiftAtom (ExtSyn.scon (str, r), p))
      | LS.Cons ((t, r), s), p ->
          Parsing.error
            (r, ("Unexpected token " ^ L.toString t) ^ " found in expression")

    and parseDec s = parseDec' (LS.expose s)

    and parseDec' = function
      | LS.Cons ((L.Id (L.Quoted, name), r), s') ->
          Parsing.error (r, "Illegal bound quoted identifier " ^ name)
      | LS.Cons ((L.Id (idCase, name), r), s') -> begin
          match Names.fixityLookup (Names.Qid ([], name)) with
          | FX.Nonfix -> parseDec1 (Some name, LS.expose s')
          | FX.Infix _ ->
              Parsing.error (r, "Cannot bind infix identifier " ^ name)
          | FX.Prefix _ ->
              Parsing.error (r, "Cannot bind prefix identifier " ^ name)
          | FX.Postfix _ ->
              Parsing.error (r, "Cannot bind postfix identifier " ^ name)
        end
      | LS.Cons ((L.Underscore, r), s') -> parseDec1 (None, LS.expose s')
      | LS.Cons ((L.Eof, r), s') ->
          Parsing.error (r, "Unexpected end of stream in declaration")
      | LS.Cons ((t, r), s') ->
          Parsing.error
            (r, "Expected variable name, found token " ^ L.toString t)

    and parseDec1 = function
      | x, LS.Cons ((L.Colon, r), s') ->
          let tm, f'' = parseExp (s', []) in
          ((x, Some tm), f'')
      | x, (LS.Cons ((L.Rbrace, _), _) as f) -> ((x, None), f)
      | x, (LS.Cons ((L.Rbracket, _), _) as f) -> ((x, None), f)
      | x, LS.Cons ((t, r), s') ->
          Parsing.error
            ( r,
              "Expected optional type declaration, found token " ^ L.toString t
            )

    and decideRParen = function
      | r0, (tm, LS.Cons ((L.Rparen, r), s)), p ->
          parseExp (s, P.shiftAtom (tm, p))
      | r0, (tm, LS.Cons ((_, r), s)), p ->
          Parsing.error (Paths.join (r0, r), "Unmatched open parenthesis")

    and decideRBrace = function
      | r0, ((x, yOpt), LS.Cons ((L.Rbrace, r), s)), p ->
          let dec =
            begin match yOpt with
            | None -> ExtSyn.dec0 (x, Paths.join (r0, r))
            | Some y -> ExtSyn.dec (x, y, Paths.join (r0, r))
            end
          in
          let tm, f' = parseExp (s, []) in
          parseExp' (f', P.shiftAtom (ExtSyn.pi (dec, tm), p))
      | r0, (dec, LS.Cons ((_, r), s)), p ->
          Parsing.error (Paths.join (r0, r), "Unmatched open brace")

    and decideRBracket = function
      | r0, ((x, yOpt), LS.Cons ((L.Rbracket, r), s)), p ->
          let dec =
            begin match yOpt with
            | None -> ExtSyn.dec0 (x, Paths.join (r0, r))
            | Some y -> ExtSyn.dec (x, y, Paths.join (r0, r))
            end
          in
          let tm, f' = parseExp (s, []) in
          parseExp' (f', P.shiftAtom (ExtSyn.lam (dec, tm), p))
      | r0, (dec, LS.Cons ((_, r), s)), p ->
          Parsing.error (Paths.join (r0, r), "Unmatched open bracket")

    let rec stripRBrace = function
      | LS.Cons ((L.Rbrace, r), s') -> (LS.expose s', r)
      | LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected `}', found " ^ L.toString t)

    and parseBracedDec (r, f) =
      let (x, yOpt), f' = parseDec' f in
      let f'', r2 = stripRBrace f' in
      let d =
        begin match yOpt with
        | None -> ExtSyn.dec0 (x, Paths.join (r, r2))
        | Some y -> ExtSyn.dec (x, y, Paths.join (r, r2))
        end
      in
      (d, f'')

    let rec parseCtx = function
      | b, ds, (LS.Cons ((L.Lbrace, r), s') as _bs) ->
          let d, f' = parseBracedDec (r, LS.expose s') in
          parseCtx (false, d :: ds, f')
      | b, ds, (LS.Cons ((t, r), s') as f) -> begin
          if b then Parsing.error (r, "Expected `{', found " ^ L.toString t)
          else (ds, f)
        end
  end

  (* some shorthands *)
  (*! structure Paths = Lexer.Paths !*)
  (* Operators and atoms for operator precedence parsing *)
  (* Predeclared infix operators *)
  (* juxtaposition *)
  (* The next section deals generically with fixity parsing          *)
  (* Because of juxtaposition, it is not clear how to turn this      *)
  (* into a separate module without passing a juxtaposition operator *)
  (* into the shift and resolve functions                            *)
  (* Stack invariants, refinements of operator list *)
  (*
         <p>       ::= <pStable> | <pRed>
         <pStable> ::= <pAtom> | <pOp?>
         <pAtom>   ::= Atom _ :: <pOp?>
         <pOp?>    ::= nil | <pOp>
         <pOp>     ::= Infix _ :: <pAtom> :: <pOp?>
                     | Prefix _ :: <pOp?>
         <pRed>    ::= Postfix _ :: Atom _ :: <pOp?>
                     | Atom _ :: <pOp>
      *)
  (* val reduce : <pRed> -> <p> *)
  (* no other cases should be possible by stack invariant *)
  (* val reduceRec : <pStable> -> ExtSyn.term *)
  (* val reduceAll : <p> -> ExtSyn.term *)
  (* val shiftAtom : term * <pStable> -> <p> *)
  (* does not raise Error exception *)
  (* insert juxOp operator and reduce *)
  (* juxtaposition binds most strongly *)
  (* val shift : Paths.region * opr * <pStable> -> <p> *)
  (* insert juxOp operator and reduce *)
  (* juxtaposition binds most strongly *)
  (* Atom/Infix: shift *)
  (* Atom/Prefix: shift *)
  (* Atom/Postfix cannot arise *)
  (* Atom/Empty: shift *)
  (* Infix/Atom: shift *)
  (* Infix/Postfix cannot arise *)
  (* insert juxtaposition operator *)
  (* will be reduced later *)
  (* Prefix/{Infix,Prefix,Empty}: shift *)
  (* Prefix/Postfix cannot arise *)
  (* Postfix/Atom: shift, reduced immediately *)
  (* Postfix/Postfix cannot arise *)
  (* val resolve : Paths.region * opr * <pStable> -> <p> *)
  (* Decides, based on precedence of opr compared to the top of the
         stack whether to shift the new operator or reduce the stack
      *)
  (* infix/atom/atom cannot arise *)
  (* infix/atom/postfix cannot arise *)
  (* infix/atom/<empty>: shift *)
  (* always shift prefix *)
  (* always reduce postfix, possibly after prior reduction *)
  (* always reduce postfix *)
  (* default is shift *)
  (* structure P *)
  (* parseQualifier' f = (ids, f')
       pre: f begins with L.ID

       Note: precondition for recursive call is enforced by the Lexer. *)
  (* Copied from parse-mode, should probably try to abstract all
       of the strip* functions into a common location - gaw *)
  (* t = `.' or ? *)
  (* same syntax as %freeze *)
  (* ABP 4/4/03 *)
  (* val parseExp : (L.token * L.region) LS.stream * <p>
                        -> ExtSyn.term * (L.token * L.region) LS.front *)
  (* Currently, we cannot override fixity status of identifiers *)
  (* Thus isQuoted always returns false *)
  (* for some reason, there's no dot after %define decls -kw *)
  (* possible error recovery: insert DOT *)
  (* cannot happen at present *)
  (* Parses contexts of the form  G ::= {id:term} | G, {id:term} *)
  (* parseDec ""{id:term} | {id}"" *)
  (* parseCtx (b, ds, f) = ds'
       if   f is a stream ""{x1:V1}...{xn:Vn} s""
       and  b is true if no declarations has been parsed yet
       and  ds is a context of declarations
       then ds' = ds, x1:V1, ..., xn:Vn
    *)
  let parseQualId' = parseQualId'
  let parseQualIds' = parseQualIds'
  let parseSubord' f = parseSubord' (f, [])
  let parseFreeze' f = parseFreeze' (f, [])
  let parseThaw' f = parseThaw' (f, [])
  let parseDeterministic' f = parseDeterministic' (f, [])
  let parseCompile' f = parseCompile' (f, [])

  (* -ABP 4/4/03 *)
  let parseTerm' f = parseExp' (f, [])
  let parseDec' = parseDec'
  let parseCtx' f = parseCtx (true, [], f)
end
(* local ... in *)
(* functor ParseTerm *)

(* # 1 "src/frontend/ParseTerm.sml.ml" *)
