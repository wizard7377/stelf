(* # 1 "src/frontend/parse_mode.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)
include Parse_mode_intf
(* signature PARSE_MODE *)

(* # 1 "src/frontend/parse_mode.fun.ml" *)
open! Parsing
open! Basis

(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)
module ParseMode (ParseMode__0 : sig
  (*! structure Paths : PATHS !*)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ExtModes' : Recon_mode.EXTMODES

  (*! sharing ExtModes'.Paths = Paths !*)
  (*! sharing ExtModes'.ExtSyn.Paths = Paths !*)
  module ParseTerm : Parse_term.PARSE_TERM with module ExtSyn = ExtModes'.ExtSyn
end) : PARSE_MODE with module ExtModes = ParseMode__0.ExtModes' = struct
  (*! structure Parsing = Parsing' !*)
  module ExtModes = ParseMode__0.ExtModes'
  module ParseTerm = ParseMode__0.ParseTerm

  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream
    module E = ExtModes
    module P = Paths

    let rec extract (s, i) =
      begin if i = String.size s then None
      else Some (String.extract (s, i, None))
      end

    let rec splitModeId (r, id) =
      begin match String.sub (id, 0) with
      | '*' -> (E.star r, extract (id, 1))
      | '-' -> begin
          if String.size id > 1 && String.sub (id, 1) = '1' then
            (E.minus1 r, extract (id, 2))
          else (E.minus r, extract (id, 1))
        end
      | '+' -> (E.plus r, extract (id, 1))
      | _ ->
          Parsing.error (r, "Expected mode `+', `-', `*', or `-1'  found " ^ id)
      end

    let rec validateMArg = function
      | r, ((mode, Some id) as mId) -> begin
          if L.isUpper id then mId
          else Parsing.error (r, "Expected free uppercase variable, found " ^ id)
        end
      | r, (_, None) -> Parsing.error (r, "Missing variable following mode")

    let rec validateMode = function
      | r, (mode, None) -> mode
      | r, (_, Some id) ->
          Parsing.error
            (r, "Expected simple mode, found mode followed by identifier " ^ id)

    let rec stripRParen = function
      | LS.Cons ((L.Rparen, r), s') -> (LS.expose s', r)
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected closing `)', found " ^ L.toString t)

    let rec stripRBrace = function
      | LS.Cons ((L.Rbrace, r), s') -> (LS.expose s', r)
      | LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected `}', found " ^ L.toString t)

    let rec parseShortSpine = function
      | LS.Cons ((L.Dot, r), s') as f -> (E.Short.mnil r, f)
      | LS.Cons ((L.Rparen, r), s') as f -> (E.Short.mnil r, f)
      | LS.Cons ((L.Id (_, id), r), s') ->
          let mId = validateMArg (r, splitModeId (r, id)) in
          let mS', f' = parseShortSpine (LS.expose s') in
          (E.Short.mapp (mId, mS'), f')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected mode or `.', found " ^ L.toString t)

    let rec parseFull = function
      | LS.Cons (((L.Id (c, id), r0) as t0), s'), r1 -> begin
          match LS.expose s' with
          | LS.Cons ((L.Lbrace, r), s'') ->
              let mId = splitModeId (r0, id) in
              let m = validateMode (r0, mId) in
              let (x, yOpt), f' = ParseTerm.parseDec' (LS.expose s'') in
              let f'', r' = stripRBrace f' in
              let dec =
                begin match yOpt with
                | None -> ParseTerm.ExtSyn.dec0 (x, P.join (r, r'))
                | Some y -> ParseTerm.ExtSyn.dec (x, y, P.join (r, r'))
                end
              in
              let t', f''' = parseFull (f'', r1) in
              (E.Full.mpi (m, dec, t'), f''')
          | LS.Cons _ as ts_ ->
              let t', (LS.Cons ((_, r), s') as f') =
                ParseTerm.parseTerm'
                  (LS.Cons (t0, LS.delay (function () -> ts_)))
              in
              (E.Full.mroot (t', P.join (r, r1)), f')
        end
      | LS.Cons ((L.Lparen, r0), s'), r1 ->
          let t', f' = ParseTerm.parseTerm' (LS.expose s') in
          let f'', r' = stripRParen f' in
          (E.Full.mroot (t', P.join (r', r1)), f'')
      | LS.Cons ((t, r), s'), _ ->
          Parsing.error (r, "Expected mode or identifier, found " ^ L.toString t)

    let rec parseMode2 = function
      | lexid, (LS.Cons ((L.Lbrace, r), s') as bs_), r1 ->
          let t', f' =
            parseFull (LS.Cons (lexid, LS.delay (function () -> bs_)), r1)
          in
          (E.Full.toModedec t', f')
      | (L.Id (_, name), r), f, _ ->
          let mS', f' = parseShortSpine f in
          (E.Short.toModedec (E.Short.mroot ([], name, r, mS')), f')

    let rec parseModeParen = function
      | LS.Cons ((L.Id (_, name), r0), s'), r ->
          let mS', f' = parseShortSpine (LS.expose s') in
          let f'', r' = stripRParen f' in
          ( E.Short.toModedec (E.Short.mroot ([], name, P.join (r, r'), mS')),
            f'' )
      | LS.Cons ((t, r), s'), _ ->
          Parsing.error (r, "Expected identifier, found " ^ L.toString t)

    let rec parseMode1 = function
      | LS.Cons (((L.Id _, r) as lexid), s') ->
          parseModeNext (parseMode2 (lexid, LS.expose s', r))
      | LS.Cons ((L.Lparen, r), s') ->
          parseModeNext (parseModeParen (LS.expose s', r))
      | LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected identifier or mode, found " ^ L.toString t)

    and parseModeNext = function
      | modedec, (LS.Cons ((L.Dot, _), s') as f) -> ([ modedec ], f)
      | modedec, f ->
          let mdecs, f' = parseMode1 f in
          (modedec :: mdecs, f')

    let rec parseMode' = function
      | LS.Cons ((L.Mode, r), s') -> parseMode1 (LS.expose s')
      | LS.Cons ((L.Unique, r), s') -> parseMode1 (LS.expose s')
      | LS.Cons ((L.Covers, r), s') -> parseMode1 (LS.expose s')
  end

  (* extract (s, i) = substring of s starting at index i
       Effect: raises Subscript if i > |s|
    *)
  (* splitModeId (r, id) = (mode, idOpt) where id = ""<mode><idOpt>""
       Invariant: id <> """"
    *)
  (* t = `.' or ? *)
  (* parseShortSpine ""modeid ... modeid."" *)
  (* parseFull ""mode {id:term} ... mode {x:term} term"" *)
  (* Look ahead one token to decide if quantifier follows *)
  (* found quantifier --- id must be mode *)
  (* no quantifier --- parse atomic type *)
  (* Left paren --- parse atomic type *)
  (* parseMode2 switches between full and short mode declarations *)
  (* lexid could be mode or other identifier *)
  (* parseMode1 parses mdecl *)
  (* parseMode' : lexResult front -> modedec * lexResult front
       Invariant: exposed input stream starts with MODE
    *)
  let parseMode' = parseMode'
end
(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
(* local *)
(* functor ParseMode *)

(* # 1 "src/frontend/parse_mode.sml.ml" *)
