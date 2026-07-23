module type PARSER = PARSER.PARSER

module Parser : PARSER = struct
  include Angstrom

  let with_fc p =
    let* start_pos = pos in
    let* res = p in
    let* end_pos = pos in
    return (res, start_pos, end_pos)

  (* Raw whitespace: spaces, tabs, newlines only — no comment handling.
     [blank] and the [%[ ... %]] string scanner build on this so they never
     accidentally swallow a line comment that crosses a newline. *)
  let ws0 = skip_while (function ' ' | '\t' | '\n' -> true | _ -> false)

  (* [whitespace] also skips [% ...] line comments: a [%] immediately followed
     by whitespace runs to end of line.  The probe fires only on [%]+whitespace,
     so [%%] (escape), [%[] (string) and [%name] (keyword) fail it and — thanks
     to Angstrom's default backtracking — are left intact for the token
     parsers.  This gives line comments "anywhere whitespace is allowed" in the
     inner (term) context. *)
  let whitespace =
    fix (fun self ->
        ws0
        *> option ()
             ((string "%;" <|> string "%")
             *> satisfy (function ' ' | '\t' | '\n' -> true | _ -> false)
             *> skip_while (fun c -> c <> '\n')
             *> self))

  let blank = skip (function ' ' | '\t' -> true | _ -> false) *> ws0
  let token s = (string s <* whitespace) *> return ()

  (* Require that the character after the keyword body is either EOF
     or one of the identifier-delimiters used by [ident1] below.
     Without this, [keyword "term"] succeeds on the [%term] prefix of
     [%terminates], and the [Cmd.ml] [choice] (which tries [term]
     before [terminates]) commits to the wrong branch. *)
  let keyword s =
    let s' = "%" ^ s in
    let boundary =
      peek_char >>= function
      | None -> return ()
      | Some (' ' | '\t' | '\n' | '(' | ')' | '{' | '}' | '[' | ']' | '%') ->
          return ()
      | Some c ->
          fail
            (Printf.sprintf
               "expected whitespace or delimiter after '%s', found '%c'" s' c)
    in
    string s' *> boundary *> whitespace

  let keywords ss = choice (List.map keyword ss)

  (* [%%X] escapes the next character [X] to a literal, so it can appear inside
     an identifier without being lexed specially.  A run of [%] decomposes by
     greedily consuming [%%] pairs: [%%%] is a literal [%], [%%%term] is the
     identifier [%term] (not the keyword), [%% ] is a literal space. *)
  let esc_char = string "%%" *> any_char >>| String.make 1

  let ident_chunk =
    take_while1 (function
      | ' ' | '\t' | '\n' | '(' | ')' | '{' | '}' | '[' | ']' | '%' -> false
      | _ -> true) (* TODO Generalize to unicode ws *)

  let ident =
    many (ident_chunk <|> esc_char) >>| String.concat "" <* whitespace

  let ident1 =
    many1 (ident_chunk <|> esc_char) >>| String.concat "" <* whitespace

  let ( let* ) = ( >>= )

  let ( and* ) p q =
    let* p = p in
    let* q = q in
    return (p, q)

  let ( let+ ) x f = f <$> x
  let ( and+ ) = ( and* )

  let ( let| ) x f =
    let* x = x in
    whitespace *> f x

  let ( and| ) p q =
    let* p = p in
    whitespace *> q >>= fun q -> return (p, q)

  let ( let@ ) p f =
    let* p, fc_start, fc_end = with_fc p in
    f (p, fc_start, fc_end)

  let given b p = if b then p else fail "failed test"
  let inside x y p = token x *> p <* token y
  let extend _p _q = assert false
  let forget p = p *> return ()

  let string_lit () : string t =
    let rec scan closing_len buf =
      take_while (function '%' -> false | _ -> true) >>= fun chunk ->
      Buffer.add_string buf chunk;
      peek_char >>= function
      | None -> fail "unterminated string literal"
      | Some '%' -> (
          any_char
          *>
          let rec read_closer consumed remaining =
            if remaining = 0 then return (`Close ())
            else
              peek_char >>= function
              | Some ']' ->
                  any_char *> read_closer (']' :: consumed) (remaining - 1)
              | _ -> return (`Not_close (List.rev consumed))
          in
          let* close_result = read_closer [] closing_len in
          match close_result with
          | `Close () -> return (Buffer.contents buf)
          | `Not_close suffix ->
              Buffer.add_char buf '%';
              List.iter (Buffer.add_char buf) suffix;
              scan closing_len buf)
      | Some c ->
          let* c = any_char in
          Buffer.add_char buf c;
          scan closing_len buf
    in
    string "%[" *> many (char '[') >>= fun extra_opens ->
    let closing_len = 1 + List.length extra_opens in
    let buf = Buffer.create 32 in
    scan closing_len buf
end
