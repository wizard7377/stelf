module Make_Modern
  (I : Syntax.SYNTAX)
    (Lexer : Lexer.LEXER)
    (P : Parser.PARSER with module Lexer = Lexer) : GrammarSig.GRAMMAR =
struct
  module Lexer = Lexer
  module Parser = P
  module Syntax = I
  module Decl = struct
    type decl =
      | Dec of Syntax.Ast.dec
      | Define of string * Syntax.Ast.exp
      | Symbol of string * Syntax.Ast.exp
      | Fixity of string * Names.Names_.Fixity.fixity
      | Sort of string * Syntax.Ast.exp
      | Term of string * Syntax.Ast.exp
      | Rule of string * Syntax.Ast.exp
      | Prose of string
  end

  type state = { fixities : (string, Names.Names_.Fixity.fixity) Hashtbl.t }
  type 'a t = ('a, state) Parser.t

  let is_ws (c : char) =
    c = ' ' || c = '\t' || c = '\n' || c = '\r'

  let is_delim (c : char) =
    is_ws c
    || c = '{'
    || c = '}'
    || c = '(' 
    || c = ')'
    || c = '['
    || c = ']'
    || c = '%'

  let take_while1 (pred : char -> bool) : string Lexer.t =
    Lexer.take (fun lexbuf ->
        let buffer = lexbuf.buffer in
        let len = String.length buffer in
        let start = lexbuf.current_offset in
        if start >= len then None
        else if not (pred (String.get buffer start)) then None
        else
          let rec loop i =
            if i >= len then i
            else if pred (String.get buffer i) then loop (i + 1)
            else i
          in
          let stop = loop start in
          let value = String.sub buffer start (stop - start) in
          let next = { lexbuf with current_offset = stop } in
          Some (next, value))

  let take_until_percent1 : string Lexer.t =
    Lexer.take (fun lexbuf ->
        let buffer = lexbuf.buffer in
        let len = String.length buffer in
        let start = lexbuf.current_offset in
        if start >= len then None
        else if String.get buffer start = '%' then None
        else
          let rec loop i =
            if i >= len then i
            else if String.get buffer i = '%' then i
            else loop (i + 1)
          in
          let stop = loop start in
          let value = String.sub buffer start (stop - start) in
          let next = { lexbuf with current_offset = stop } in
          Some (next, value))

  let take_exact (s : string) : unit Lexer.t =
    Lexer.take (fun lexbuf ->
        let buffer = lexbuf.buffer in
        let len = String.length buffer in
        let n = String.length s in
        let start = lexbuf.current_offset in
        if start + n > len then None
        else if String.sub buffer start n = s then
          let next = { lexbuf with current_offset = start + n } in
          Some (next, ())
        else None) 

  let take_until_string (term : string) : string Lexer.t =
    Lexer.take (fun lexbuf ->
        let buffer = lexbuf.buffer in
        let len = String.length buffer in
        let n = String.length term in
        let start = lexbuf.current_offset in
        let rec search i =
          if i + n > len then None
          else if String.sub buffer i n = term then Some i
          else search (i + 1)
        in
        match search start with
        | None -> None
        | Some stop ->
            let value = String.sub buffer start (stop - start) in
            let next = { lexbuf with current_offset = stop } in
            Some (next, value))

  let eof_lexer : unit Lexer.t =
    Lexer.take (fun lexbuf ->
        if lexbuf.current_offset >= String.length lexbuf.buffer then Some (lexbuf, ())
        else None)

  let ws1 : string t = Parser.lex (take_while1 is_ws)
  let ws : unit t =
    Parser.(
      let* _ = opt ws1 in
      pure ())

  let kw (s : string) : unit t =
    Parser.(
      let* _ = ws in
      let* _ = keyword s in
      pure ())

  let symbol_token : string t = Parser.lex (take_while1 (fun c -> not (is_delim c)))

  let name : string t =
    Parser.(
      let* _ = ws in
      let* token = symbol_token in
      if token = "_"
      then err "expected identifier, found wildcard"
      else pure token)

  let wildcard : unit t = kw "_"

  let mk_ident (id : string) : Syntax.Ast.exp =
    Syntax.Ast.Root
      ( Syntax.Ast.FVar
          (id, Syntax.Ast.Uni Syntax.Ast.Type, Syntax.Ast.Shift 0),
        Syntax.Ast.Nil )

  let app_fold (head : Syntax.Ast.exp) (args : Syntax.Ast.exp list) : Syntax.Ast.exp =
    let rec to_spine = function
      | [] -> Syntax.Ast.Nil
      | x :: xs -> Syntax.Ast.App (x, to_spine xs)
    in
    match args with
    | [] -> head
    | _ -> Syntax.Ast.Redex (head, to_spine args)

  let lam_fold (dec : Syntax.Ast.dec) (body : Syntax.Ast.exp) : Syntax.Ast.exp =
    Syntax.Ast.Lam (dec, body)

  let pi_fold (dec : Syntax.Ast.dec) (body : Syntax.Ast.exp) : Syntax.Ast.exp =
    Syntax.Ast.Pi ((dec, Syntax.Ast.Maybe), body)

  let dec_of_name (x : string option) (ty : Syntax.Ast.exp option) : Syntax.Ast.dec =
    match ty with
    | None -> Syntax.Ast.NDec x
    | Some t -> Syntax.Ast.Dec (x, t)

  let exp : Syntax.Ast.exp t =
    Parser.Monad.fix (fun exp' ->
        let open Parser in
        let atom =
          alt
            [ (let* _ = kw "(" in
               let* e = exp' in
               let* _ = kw ")" in
               pure e)
            ; (let* _ = ws in
               let* tok = symbol_token in
               if tok = "_" then pure (Syntax.Ast.NVar 0) else pure (mk_ident tok))
            ]
        in
        let app =
          let* hd = atom in
          let* tl = many atom in
          pure (app_fold hd tl)
        in
        let lambda =
          let* _ = kw "[" in
          let* binder =
            alt
              [ (let* _ = wildcard in
                 pure (None, None))
              ; (let* x = name in
                 pure (Some x, None))
              ]
          in
          let* _ = kw "]" in
          let* body = exp' in
          pure (lam_fold (dec_of_name (fst binder) (snd binder)) body)
        in
        let pi =
          let* _ = kw "{" in
          let* binder =
            alt
              [ (let* _ = wildcard in
                 let* ty = exp' in
                 pure (None, Some ty))
              ; (let* x = name in
                 let* ty = opt exp' in
                 pure (Some x, ty))
              ]
          in
          let* _ = kw "}" in
          let* body = exp' in
          pure (pi_fold (dec_of_name (fst binder) (snd binder)) body)
        in
        let ascription =
          let* _ = kw "%the" in
          let* _ty = exp' in
          let* value = exp' in
          pure value
        in
        alt [ lambda; pi; ascription; app ])

  let typ : Syntax.Ast.exp t = exp

  let dec : Syntax.Ast.dec t =
    Parser.(
      let* _ = ws in
      alt
        [ (let* _ = wildcard in
           let* ty = opt typ in
           pure (dec_of_name None ty))
        ; (let* x = name in
           let* ty = opt typ in
           pure (dec_of_name (Some x) ty))
        ])

  let full_dec : Syntax.Ast.dec t = dec

  let optional_clause_end : unit t =
    Parser.(
      let* _ = ws in
      let* _ = opt (keyword "%.") in
      pure ())

  let parse_int : int t =
    Parser.(
      let* _ = ws in
      let* raw = Parser.lex (take_while1 (fun c -> c >= '0' && c <= '9')) in
      try pure (int_of_string raw) with Failure _ -> err ("invalid integer: " ^ raw))

  let register_fixity (op : string) (fx : Names.Names_.Fixity.fixity) : unit t =
    Parser.(
      let* st = Monad.get_state in
      Hashtbl.replace st.fixities op fx;
      pure ())

  let sort_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%sort" in
      let* n = name in
      let* e = typ in
      let* _ = optional_clause_end in
      pure (Decl.Sort (n, e)))

  let term_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%term" in
      let* n = name in
      let* e = typ in
      let* _ = optional_clause_end in
      pure (Decl.Term (n, e)))

  let rule_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%decl" in
      let* e = exp in
      let* _ = optional_clause_end in
      pure (Decl.Rule ("_", e)))

  let define_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%define" in
      let* n = name in
      let* e = exp in
      let* _ = optional_clause_end in
      pure (Decl.Define (n, e)))

  let symbol_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%symbol" in
      let* n = name in
      let* e = exp in
      let* _ = optional_clause_end in
      pure (Decl.Symbol (n, e)))

  let infixl_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%infixl" in
      let* op = name in
      let* prec = parse_int in
      let fx = Names.Names_.Fixity.Infix (Names.Names_.Fixity.Strength prec, Names.Names_.Fixity.Left) in
      let* _ = register_fixity op fx in
      let* _ = optional_clause_end in
      pure (Decl.Fixity (op, fx)))

  let infixr_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%infixr" in
      let* op = name in
      let* prec = parse_int in
      let fx = Names.Names_.Fixity.Infix (Names.Names_.Fixity.Strength prec, Names.Names_.Fixity.Right) in
      let* _ = register_fixity op fx in
      let* _ = optional_clause_end in
      pure (Decl.Fixity (op, fx)))

  let prefix_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%prefix" in
      let* op = name in
      let* prec = parse_int in
      let fx = Names.Names_.Fixity.Prefix (Names.Names_.Fixity.Strength prec) in
      let* _ = register_fixity op fx in
      let* _ = optional_clause_end in
      pure (Decl.Fixity (op, fx)))

  let postfix_decl : Decl.decl t =
    Parser.(
      let* _ = kw "%postfix" in
      let* op = name in
      let* prec = parse_int in
      let fx = Names.Names_.Fixity.Postfix (Names.Names_.Fixity.Strength prec) in
      let* _ = register_fixity op fx in
      let* _ = optional_clause_end in
      pure (Decl.Fixity (op, fx)))

  let opaque_directive : Decl.decl t =
    Parser.(
      let* _ = ws in
      let* _ = keyword "%" in
      let* body = Parser.lex (take_until_string "%.") in
      let* _ = Parser.lex (take_exact "%.") in
      pure (Decl.Prose ("%" ^ body ^ "%.")))

  let declaration : Decl.decl t =
    Parser.alt
      [ sort_decl
      ; term_decl
      ; rule_decl
      ; define_decl
      ; symbol_decl
      ; infixl_decl
      ; infixr_decl
      ; prefix_decl
      ; postfix_decl
      ; opaque_directive
      ]

  let comment_or_markup : unit t =
    Parser.(
      alt
        [ (let* _ = kw "%[" in
           let* _ = Parser.lex (take_until_string "%]") in
           let* _ = Parser.lex (take_exact "%]") in
           pure ())
        ; (let* _ = kw "%(" in
           let* _ = Parser.lex (take_until_string "%)") in
           let* _ = Parser.lex (take_exact "%)") in
           pure ())
        ])

  let prose : Decl.decl t =
    Parser.(
      let* chunk = Parser.lex take_until_percent1 in
      pure (Decl.Prose chunk))

  let doc : Decl.decl list t =
    Parser.Monad.fix (fun doc' ->
        let open Parser in
        alt
          [ (let* _ = lex eof_lexer in
             pure [])
          ; (let* _ = ws1 in
             let* rest = doc' in
             pure rest)
          ; (let* _ = comment_or_markup in
             let* rest = doc' in
             pure rest)
          ; (let* d = declaration in
             let* rest = doc' in
             pure (d :: rest))
          ; (let* p = prose in
             let* rest = doc' in
             pure (p :: rest))
          ])
end
