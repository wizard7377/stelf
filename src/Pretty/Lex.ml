(** Lexical concerns of STELF's surface syntax: turning arbitrary strings back
    into tokens that the modern lexer reads as the same strings.

    This module knows nothing about the CST. Everything here mirrors
    [Lang/Parsing/Parser.ml] -- if the lexer's delimiter set or escape
    convention changes, it changes here too. *)

(** The characters that terminate an identifier chunk. Mirrors [ident_chunk] in
    [Lang/Parsing/Parser.ml]: anything in this set has to be escaped to appear
    inside a name. *)
let is_delimiter (c : char) : bool =
  match c with
  | ' ' | '\t' | '\n' | '(' | ')' | '{' | '}' | '[' | ']' | '%' -> true
  | _ -> false

(** Does [s] lex as a single identifier when written verbatim? *)
let is_plain_ident (s : string) : bool =
  s <> "" && not (String.exists is_delimiter s)

(** [escape_ident s] renders [s] so the lexer reads back exactly [s].

    Each delimiter is escaped as [%%c], which the lexer's [esc_char] turns back
    into the literal [c]. The empty string has no representation as a bare
    identifier -- the lexer's [ident1] needs at least one chunk -- so it is
    rendered as an escaped underscore, which is a name no source file can
    collide with. *)
let escape_ident (s : string) : string =
  if s = "" then "%%_"
  else if is_plain_ident s then s
  else begin
    let buf = Buffer.create (String.length s + 8) in
    String.iter
      (fun c ->
        if is_delimiter c then Buffer.add_string buf "%%";
        Buffer.add_char buf c)
      s;
    Buffer.contents buf
  end

(** Lexical class of a bare identifier, as [Modern.parse_id] decides it. A name
    in the wrong class cannot be written bare without changing which CST node it
    parses back to. *)
let is_uppercase_ident (s : string) : bool =
  s <> "" && (s.[0] = '_' || (s.[0] >= 'A' && s.[0] <= 'Z'))

(** The longest run of [']'] that immediately follows a ['%'] anywhere in [s].
    A text literal closed by [n] brackets is safe exactly when this is [< n],
    because the lexer closes at the first ['%'] followed by [n] brackets. *)
let max_closer_run (s : string) : int =
  let n = String.length s in
  let best = ref 0 in
  let i = ref 0 in
  while !i < n do
    if s.[!i] = '%' then begin
      let j = ref (!i + 1) in
      while !j < n && s.[!j] = ']' do
        incr j
      done;
      if !j - !i - 1 > !best then best := !j - !i - 1;
      (* Resume at [!j] rather than [!i + 1]: the brackets just scanned cannot
         start another run, and a ['%'] at [!j] is picked up next iteration. *)
      i := !j
    end
    else incr i
  done;
  !best

(** [quote_text s] renders [s] as a STELF text literal.

    The delimiters grow with the payload: a literal opened by
    [%[[] is closed by [%]]], and the lexer closes at the first ['%'] followed
    by that many brackets. Choosing one more bracket than the payload's longest
    such run makes every payload representable, including ones that contain the
    closing delimiter of a shorter form. *)
let quote_text (s : string) : string =
  let n = max_closer_run s + 1 in
  let buf = Buffer.create (String.length s + (2 * n) + 2) in
  Buffer.add_string buf "%[";
  for _ = 2 to n do
    Buffer.add_char buf '['
  done;
  Buffer.add_string buf s;
  Buffer.add_char buf '%';
  for _ = 1 to n do
    Buffer.add_char buf ']'
  done;
  Buffer.contents buf
