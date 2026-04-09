(** {1 STELF Lexing Primitives}

  The lexer is intentionally small: it exposes a minimal state machine over
  raw strings, plus the combinators needed by the STELF parser layer. *)

open Lexer_intf

module type LEXER = Lexer_intf.LEXER

module Make_Lexer () : LEXER = struct
  type nonrec source = Tag.Pos.source
  type nonrec pos = Tag.Pos.pos
  type nonrec lexbuf = Tag.Pos.lexbuf
  type +'a t = lexbuf -> (lexbuf * 'a) option

  let of_string ?(source = Tag.Pos.Interactive) (buffer : string) : lexbuf =
    { buffer; source; current_offset = 0; current_source = source }

  let take (f : lexbuf -> (lexbuf * 'a) option) : 'a t = f
  let run (f : 'a t) : lexbuf -> (lexbuf * 'a) option = f
  let get_source (lexbuf : lexbuf) : source = lexbuf.current_source
  let get_offset (lexbuf : lexbuf) : int = lexbuf.current_offset

  let get_pos (lexbuf : lexbuf) : pos =
    let limit = min lexbuf.current_offset (String.length lexbuf.buffer) in
    let line = ref 1 in
    let column = ref 1 in
    for index = 0 to limit - 1 do
      match String.get lexbuf.buffer index with
      | '\n' ->
          incr line;
          column := 1
      | _ -> incr column
    done;
    { source = lexbuf.current_source; line = !line; column = !column }

  module Monad = struct
    let map (f : 'a -> 'b) (parser : 'a t) : 'b t =
     fun lexbuf ->
      match parser lexbuf with
      | Some (new_lexbuf, result) -> Some (new_lexbuf, f result)
      | None -> None

    let bind (parser : 'a t) (f : 'a -> 'b t) : 'b t =
     fun lexbuf ->
      match parser lexbuf with
      | Some (new_lexbuf, result) -> f result new_lexbuf
      | None -> None

    let ( let* ) (x : 'a t) (f : 'a -> 'b t) : 'b t = bind x f
    let ( let+ ) (x : 'a t) (f : 'a -> 'b) : 'b t = map f x

    let ( and+ ) (p1 : 'a t) (p2 : 'b t) : ('a * 'b) t =
     fun lexbuf ->
      match p1 lexbuf with
      | Some (lexbuf1, result1) -> (
          match p2 lexbuf1 with
          | Some (lexbuf2, result2) -> Some (lexbuf2, (result1, result2))
          | None -> None)
      | None -> None

    let ( and* ) = ( and+ )
    let pure (x : 'a) : 'a t = fun lexbuf -> Some (lexbuf, x)
    let state : lexbuf t = fun lexbuf -> Some (lexbuf, lexbuf)
  end

  let repeat (p : 'a t) : 'a list t =
   fun lexbuf ->
    let rec aux acc lexbuf =
      match p lexbuf with
      | Some (new_lexbuf, result) -> aux (result :: acc) new_lexbuf
      | None -> Some (lexbuf, List.rev acc)
    in
    aux [] lexbuf

  let exact (n : int) : string t =
   fun lexbuf ->
    let buffer = lexbuf.buffer in
    let offset = lexbuf.current_offset in
    if offset + n <= String.length buffer then
      let result = String.sub buffer offset n in
      let new_lexbuf = { lexbuf with current_offset = offset + n } in
      Some (new_lexbuf, result)
    else None

  let until (pred : char -> bool) : string t =
   fun lexbuf ->
    let buffer = lexbuf.buffer in
    let offset = lexbuf.current_offset in
    let rec find_end i =
      if i >= String.length buffer then None
      else if pred (String.get buffer i) then Some i
      else find_end (i + 1)
    in
    match find_end offset with
    | Some end_offset ->
        let result = String.sub buffer offset (end_offset - offset) in
        let new_lexbuf = { lexbuf with current_offset = end_offset } in
        Some (new_lexbuf, result)
    | None -> None

  let is_whitespace (c : char) : bool =
    c = ' ' || c = '\t' || c = '\n' || c = '\r'

  let space1 : string t = until (fun c -> not (is_whitespace c))
  let symbol1 : string t = until (fun c -> is_whitespace c)

  let keyword (kw : string) : bool t =
   fun lexbuf ->
    let buffer = lexbuf.buffer in
    let offset = lexbuf.current_offset in
    if String.length buffer - offset >= String.length kw then
      let candidate = String.sub buffer offset (String.length kw) in
      if candidate = kw then
        let new_lexbuf =
          { lexbuf with current_offset = offset + String.length kw }
        in
        Some (new_lexbuf, true)
      else None
    else None
end

module Lexer = Make_Lexer ()
