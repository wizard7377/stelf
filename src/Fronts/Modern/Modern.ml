module Make_Modern
    (Paths : Paths.PATHS.PATHS)
    (Cst : Cst.CST with module Paths = Paths)
    (Names : Names.NAMES.NAMES)
    (Parser : Parsing.PARSER.PARSER) :
  MODERN.MODERN
    with module Names = Names
     and module Cst = Cst
     and module Paths = Paths = struct
  module Paths = Paths
  module Cst = Cst
  module Names = Names
  module N = Names
  module Parser = Parser

  type arrow_last = LeftArrow | RightArrow | NoArrow

  exception ParseError of string

  exception
    FullParseError of {
      title : Display.form option;
      subtitle : Display.form option;
      body : Display.form;
      loc : Cst.loc option;
    }

  open Parser

  let given_symbols : (string * string) list ref = ref []
  let currently_uppercase : string list ref = ref []

  let keyword' kw =
    keyword kw
    <|> choice
          (List.filter_map
             (fun (sym, kw') -> if kw = kw' then Some (token sym) else None)
             !given_symbols)

  (* Several spellings of the same keyword, e.g. [%in] and its quantifier
     alias [%forall].  Each alternative still honours user-declared [%symbol]
     aliases, since this goes through [keyword'] rather than [keyword]. *)
  let keywords' kws = choice (List.map keyword' kws)

  let with_uppercase : string list -> (unit -> 'a t) -> 'a t =
   fun names p ->
    let old = !currently_uppercase in
    currently_uppercase := old @ names;
    let* res = p () in
    let+ () = return @@ (currently_uppercase := old) in
    res

  type 'a t = 'a Parser.t

  let rec break (s : string list) : string list * string =
    match s with
    | [] -> ([], "")
    | x :: xs ->
        let y, z = break xs in
        (x :: y, z)

  let mk_loc : int -> int -> Cst.loc = fun x y -> Cst.View.mk_loc x y
  let ghost' = Cst.View.Loc.(review Ghost)

  let combine_fc (r1 : Paths.region) (r2 : Paths.region) : Paths.region =
    Paths.join r1 r2

  let loc_union (l1 : Cst.loc) (l2 : Cst.loc) : Cst.loc =
    let open Cst.View.Loc in
    match (view l1, view l2) with
    | Loc (_, s1, e1), Loc (_, s2, e2) -> mk_loc (min s1 s2) (max e1 e2)
    | Ghost, _ -> l2
    | _, Ghost -> l1

  let term_loc (tm : Cst.Term.t) : Cst.loc =
    let open Cst.View.Term in
    match view tm with
    | Lowercase (loc, _)
    | Uppercase (loc, _)
    | Qualified (loc, _, _)
    | Text (loc, _)
    | ExistVar (loc, _)
    | FreeVar (loc, _)
    | Pi (loc, _, _)
    | Lam (loc, _, _)
    | App (loc, _, _)
    | HasType (loc, _, _)
    | Omitted loc
    | Typ loc
    | Arrow (loc, _, _)
    | BackArrow (loc, _, _)
    | Foreign (loc, _)
    | MacroParam (loc, _, _)
    | Local (loc, _, _)
    | Internal (loc, _, _) ->
        loc

  module FX = Names.Fixity

  let local_fixity : (string, FX.fixity) Hashtbl.t = Hashtbl.create 16

  let register_local_fixity (fix : Cst.fixity) (n : int) (ids : string list) :
      unit =
    let prec = FX.Strength n in
    let open Cst.View.Fixity in
    let fx =
      match !>fix with
      | Left _ -> FX.Infix (prec, FX.Left)
      | Right _ -> FX.Infix (prec, FX.Right)
      | Prefix _ -> FX.Prefix prec
      | Postfix _ -> FX.Postfix prec
      | Middle _ -> FX.Infix (prec, FX.None)
      | None _ -> FX.Infix (prec, FX.None)
    in
    List.iter (fun id -> Hashtbl.replace local_fixity id fx) ids

  type operator =
    | Atom of Cst.Term.t
    | Infix_ of
        (FX.precedence * FX.associativity)
        * (Cst.Term.t * Cst.Term.t -> Cst.Term.t)
    | Prefix_ of FX.precedence * (Cst.Term.t -> Cst.Term.t)
    | Postfix_ of FX.precedence * (Cst.Term.t -> Cst.Term.t)

  let jux_op =
    Infix_
      ( (FX.inc FX.maxPrec, FX.Left),
        fun (f, x) ->
          let loc = loc_union (term_loc f) (term_loc x) in
          Cst.View.Term.(review @@ App (loc, f, [ x ])) )

  let infix_op (infixity, tm) =
    Infix_
      ( infixity,
        fun (tm1, tm2) ->
          let loc = loc_union (term_loc tm1) (term_loc tm2) in
          Cst.View.Term.(
            review
            @@ App (loc, review @@ App (term_loc tm1, tm, [ tm1 ]), [ tm2 ])) )

  let prefix_op (prec, tm) =
    Prefix_
      ( prec,
        fun tm1 ->
          let loc = loc_union (term_loc tm) (term_loc tm1) in
          Cst.View.Term.(review @@ App (loc, tm, [ tm1 ])) )

  let postfix_op (prec, tm) =
    Postfix_
      ( prec,
        fun tm1 ->
          let loc = loc_union (term_loc tm1) (term_loc tm) in
          Cst.View.Term.(review @@ App (loc, tm, [ tm1 ])) )

  let classify (tm : Cst.Term.t) : operator =
    let open Cst.View.Term in
    match !>tm with
    | Qualified _ ->
        (* %(name sort) constructor-reference syntax is always an atom —
           explicit qualification opts out of operator status *)
        Atom tm
    | Lowercase (_, (ns, name)) | Uppercase (_, (ns, name)) ->
        let fixity =
          match Hashtbl.find_opt local_fixity name with
          | Some fx -> fx
          | None -> Names.fixityLookup (Names.Qid (ns, name))
        in
        begin match fixity with
        | FX.Nonfix -> Atom tm
        | FX.Infix (prec, assoc) -> infix_op ((prec, assoc), tm)
        | FX.Prefix prec -> prefix_op (prec, tm)
        | FX.Postfix prec -> postfix_op (prec, tm)
        end
    | _ -> Atom tm

  module P = struct
    let reduce = function
      | Atom tm2 :: Infix_ (_, con) :: Atom tm1 :: p' ->
          Atom (con (tm1, tm2)) :: p'
      | Atom tm :: Prefix_ (_, con) :: p' -> Atom (con tm) :: p'
      | Postfix_ (_, con) :: Atom tm :: p' -> Atom (con tm) :: p'
      | p ->
          failwith
            (Printf.sprintf "process_app: cannot reduce stack of length %d"
               (List.length p))

    let rec reduce_rec = function [ Atom e ] -> e | p -> reduce_rec (reduce p)

    let reduce_all = function
      | [ Atom e ] -> e
      | Infix_ _ :: _ -> raise (ParseError "Incomplete infix expression")
      | Prefix_ _ :: _ -> raise (ParseError "Incomplete prefix expression")
      | [] -> raise (ParseError "Empty expression")
      | p -> reduce_rec (reduce p)

    let shift_atom (tm, p) =
      match p with
      | Atom _ :: _ -> reduce (Atom tm :: jux_op :: p)
      | _ -> Atom tm :: p

    let shift (opr, p) =
      match (opr, p) with
      | (Atom _ as o), (Atom _ :: _ as p') -> reduce (o :: jux_op :: p')
      | Infix_ _, Infix_ _ :: _ ->
          raise (ParseError "Consecutive infix operators")
      | Infix_ _, Prefix_ _ :: _ ->
          raise (ParseError "Infix operator following prefix operator")
      | Infix_ _, [] -> raise (ParseError "Leading infix operator")
      | (Prefix_ _ as o), (Atom _ :: _ as p') -> o :: jux_op :: p'
      | Postfix_ _, Infix_ _ :: _ ->
          raise (ParseError "Postfix operator following infix operator")
      | Postfix_ _, Prefix_ _ :: _ ->
          raise (ParseError "Postfix operator following prefix operator")
      | Postfix_ _, [] -> raise (ParseError "Leading postfix operator")
      | o, p' -> o :: p'

    let rec resolve (opr, p) =
      match (opr, p) with
      | ( (Infix_ ((prec, assoc), _) as o),
          (Atom _ :: Infix_ ((prec', assoc'), _) :: _ as p') ) ->
          begin match (FX.compare prec prec', assoc, assoc') with
          | Greater, _, _ -> shift (o, p')
          | Less, _, _ -> resolve (o, reduce p')
          | Equal, FX.Left, FX.Left -> resolve (o, reduce p')
          | Equal, FX.Right, FX.Right -> shift (o, p')
          | _ ->
              raise
                (ParseError
                   "Ambiguous: infix following infix of identical precedence")
          end
      | (Infix_ ((prec, _), _) as o), (Atom _ :: Prefix_ (prec', _) :: _ as p')
        ->
          begin match FX.compare prec prec' with
          | Greater -> shift (o, p')
          | Less -> resolve (o, reduce p')
          | Equal ->
              raise
                (ParseError
                   "Ambiguous: infix following prefix of identical precedence")
          end
      | (Prefix_ _ as o), p' -> shift (o, p')
      | (Postfix_ (prec, _) as o), (Atom _ :: Prefix_ (prec', _) :: _ as p') ->
          begin match FX.compare prec prec' with
          | Greater -> reduce (shift (o, p'))
          | Less -> resolve (o, reduce p')
          | Equal ->
              raise
                (ParseError
                   "Ambiguous: postfix following prefix of identical precedence")
          end
      | (Postfix_ (prec, _) as o), (Atom _ :: Infix_ ((prec', _), _) :: _ as p')
        ->
          begin match FX.compare prec prec' with
          | Greater -> reduce (shift (o, p'))
          | Less -> resolve (o, reduce p')
          | Equal ->
              raise
                (ParseError
                   "Ambiguous: postfix following infix of identical precedence")
          end
      | (Postfix_ _ as o), ([ Atom _ ] as p') -> reduce (shift (o, p'))
      | o, p' -> shift (o, p')
  end

  let process_app (ts : Cst.Term.t list) : Cst.Term.t =
    let rec go p = function
      | [] -> P.reduce_all p
      | t :: rest ->
          let p' =
            match classify t with
            | Atom tm -> P.shift_atom (tm, p)
            | opr -> P.resolve (opr, p)
          in
          go p' rest
    in
    match ts with
    | [] -> failwith "process_app: called with empty list"
    | _ -> go [] ts

  let split_qid ns =
    match List.rev ns with
    | [] -> failwith "Expected qualified name"
    | name :: rev_scopes -> (List.rev rev_scopes, name)

  let rec parse_arg () : string option t =
    (* [_] alone is an anonymous binder, but the test has to be made on the
       whole identifier: [token "_"] would match the leading underscore of
       [_0] and leave [0] behind, silently turning [{_0 nat}] into an
       anonymous binder of type [0 nat]. Names of that shape are exactly what
       [Names.decLUName] hands to anonymous binders, so they arrive whenever
       printed output is read back. *)
    (let+ s = ident1 in
     if s = "_" then None else Some s)
    <?> "argument"

  and parse_qid_body (form : Cst.qid_form) : Cst.Term.t t =
    inside "(" ")"
      (let@ ns, s, e = many1 ident1 in
       let loc = mk_loc s e in
       return Cst.View.Term.(review @@ Qualified (loc, split_qid ns, form)))
    <|> let@ name, s, e = ident1 in
        let loc = mk_loc s e in
        return Cst.View.Term.(review @@ Qualified (loc, ([], name), form))

  and parse_id () : Cst.Term.t t =
    (* [%type] is the universe of types.  It is spelled with the [%] sigil so
       that the bare identifier [type] stays available as an ordinary name.

       No command currently accepts it in a type-correct position -- [%sort]
       supplies the universe implicitly, so [%sort c %type] is a level clash,
       not a longhand.  It exists so that the printer has a token for
       [IntSyn.Uni Type] that parses back to the same term; see [Resugar]. *)
    (let@ (), s, e = keyword' "type" in
     return Cst.View.Term.(review @@ Typ (mk_loc s e)))
    <|> keyword' "val" *> commit *> parse_qid_body Cst.Val
    <|> keyword' "abs" *> commit *> parse_qid_body Cst.Abs
    <|> (string "%(" *> commit
        *> let@ tm, s, e =
             let* ns = many1 ident1 in
             (let+ body =
                inside "(" ")" (parse_expr ()) <* string ")" <* whitespace
              in
              `Local (ns, body))
             <|> let+ () = string ")" *> whitespace in
                 `Qualified ns
           in
           let loc = mk_loc s e in
           return
             (match tm with
             | `Local (ns, body) ->
                 Cst.View.Term.(review @@ Local (loc, ns, body))
             | `Qualified ns ->
                 Cst.View.Term.(
                   review @@ Qualified (loc, split_qid ns, Cst.Val))))
    <|>
    let@ name, s, e = ident1 in
    let loc = mk_loc s e in
    let is_upper =
      String.length name > 0
      && (name.[0] = '_' || (name.[0] >= 'A' && name.[0] <= 'Z'))
    in
    return
      (if name = "_" then
         (* A lone `_` is an omitted term: a fresh placeholder solved by
            reconstruction at each occurrence.  (Underscore-prefixed names
            like `_C1` remain ordinary uppercase-class variables; making `_`
            one of those would alias every `_` in a declaration to a single
            rigid free variable named "_".) *)
         Cst.View.Term.(review @@ Omitted loc)
       else if is_upper || List.mem name !currently_uppercase then
         Cst.View.Term.(review @@ Uppercase (loc, ([], name)))
       else Cst.View.Term.(review @@ Lowercase (loc, ([], name))))

  and parse_expr_trail () : Cst.Term.t t =
    (let@ d, s, e = inside "[" "]" (parse_decl ()) in
     let loc = mk_loc s e in
     let+ body = parse_expr () in
     let full_loc = loc_union loc (term_loc body) in
     Cst.View.Term.(review @@ Lam (full_loc, [ d ], body)))
    <|> (let@ d, s, e = inside "{" "}" (parse_decl ()) in
         let loc = mk_loc s e in
         let+ body = parse_expr () in
         let full_loc = loc_union loc (term_loc body) in
         Cst.View.Term.(review @@ Pi (full_loc, [ d ], body)))
    <|> ((let* ids = inside "{{" "}}" (many @@ parse_var ()) in
          let+ body = with_uppercase ids parse_expr in
          body)
        <?> "expression with implicit variables")
    <|>
    (* %if A %-> B  %-> C  ==>  {_ A} {_ B} C  (last arg is the body) *)
    (* %if A %<- B  %<- C  ==>  {_ C} {_ B} A  (first arg is the body) *)
    (* commit fires only after the first separator is confirmed *)
    (keywords [ "if"; "do"; "pi"; "fn" ]
    *>
    let* first = return () >>= fun () -> parse_expr () in
    (keyword' "->" *> commit
    *>
    let+ rest =
      sep_by1 (keyword' "->") (return () >>= fun () -> parse_expr ())
    in
    let all = first :: rest in
    let rev = List.rev all in
    let body = List.hd rev in
    let init = List.rev (List.tl rev) in
    (* Non-dependent arrows: elaborate as [Arrow] (not an anonymous-binder [Pi]),
       so the codomain (clause head) is reconstructed WITHOUT the domain
       (premise) in scope.  Routing through [Pi] over-scopes the head's omitted
       EVars under the premise binder, which later derails coverage checking. *)
    List.fold_right
      (fun t acc ->
        let loc = loc_union (term_loc t) (term_loc acc) in
        Cst.View.Term.(review @@ Arrow (loc, t, acc)))
      init body)
    <|> keyword' "<-" *> commit
        *>
        let+ rest =
          sep_by1 (keyword' "<-") (return () >>= fun () -> parse_expr ())
        in
        let rest_rev = List.rev rest in
        (* Non-dependent arrows: see the [%->] case above.  Elaborate as
           [Arrow] so the head ([first]) is not scoped under premise binders. *)
        List.fold_right
          (fun t acc ->
            let loc = loc_union (term_loc t) (term_loc acc) in
            Cst.View.Term.(review @@ Arrow (loc, t, acc)))
          rest_rev first)
    <|> parse_id () <?> "trailing expression"

  and parse_expr_app () : Cst.Term.t t =
    (let* head = parse_expr1 () in
     let+ args = many (parse_expr1 ()) in
     process_app (head :: args))
    <?> "application"

  and parse_expr1 () : Cst.Term.t t =
    begin
      choice
        [
          parse_id ();
          inside "(" ")" (return () >>= fun () -> parse_expr ());
          (let@ str, s, e = parse_text () in
           let loc = mk_loc s e in
           return Cst.View.Term.(review @@ Text (loc, str)));
        ]
    end
    <?> "small expression"

  and parse_expr () : Cst.Term.t t =
    begin
      (let@ (ty, body), s, e =
         keyword' "the" *> commit
         *>
         let* ty = parse_expr1 () in
         let+ body = parse_expr () in
         (ty, body)
       in
       let loc = mk_loc s e in
       return Cst.View.Term.(review @@ HasType (loc, body, ty)))
      <|> (let@ (ns_id, body), s, e =
             keyword' "local" *> commit
             *>
             let* ns_id = ident1 in
             let+ body = parse_expr () in
             (ns_id, body)
           in
           let loc = mk_loc s e in
           return Cst.View.Term.(review @@ Local (loc, [ ns_id ], body)))
      (*
            %<- A
            %<- B
            %<- C  ==>  {_ C} {_ B} A  (first arg is the body) *)
      <|>
      let* atoms = many @@ parse_expr1 () in
      let* trail_opt =
        option None
          (let+ t = parse_expr_trail () in
           Some t)
      in
      match (atoms, trail_opt) with
      | [], None -> fail "expected expression"
      | [], Some trail -> return trail
      | head :: rest, None -> return (process_app (head :: rest))
      | head :: rest, Some trail ->
          return (process_app (head :: (rest @ [ trail ])))
    end
    <?> "expression"

  and parse_var () : string t =
    begin
      ident1
    end
    <?> "variable"

  and parse_qualified () : Cst.symbol t =
    begin
      keyword' "val" *> commit
      *> ((let* ident in
           return ([], ident))
         <|> inside "(" ")"
               (let* ns = many1 ident in
                return @@ split_qid ns))
      <|> (keyword' "("
          *> let* ns = many1 ident <* string ")" in
             return @@ split_qid ns)
      <|> keyword "(" *> commit
          *> let* ns = many1 ident <* string ")" in
             return @@ split_qid ns
    end
    <?> "qualified name"

  and parse_text () : string t =
    string_lit () <* whitespace <?> "string literal"

  and parse_decl () : Cst.decl t =
    begin
      (let@ names, s, e = inside "(" ")" (many1 (parse_arg ())) in
       let loc = mk_loc s e in
       (* An omitted type is anchored on the binder it belongs to, so that
          reconstruction's "Omitted term has ambiguous type" underlines the
          binder rather than pointing nowhere. *)
       let+ typ =
         option Cst.View.Term.(review @@ Omitted loc) (parse_expr ())
       in
       Cst.View.Decl.(
         review
         @@ Decl1 (loc, names, typ, Cst.View.Term.(review @@ Omitted ghost'))))
      <|> let@ name, s, e = parse_arg () in
          let loc = mk_loc s e in
          let+ typ =
            option Cst.View.Term.(review @@ Omitted loc) (parse_expr ())
          in
          Cst.View.Decl.(
            review
            @@ Decl1
                 (loc, [ name ], typ, Cst.View.Term.(review @@ Omitted ghost')))
    end
    <?> "declaration"

  and parse_decl_simple () : Cst.decl t =
    begin
      let@ typ, s, e = parse_id () <|> inside "(" ")" (parse_expr ()) in
      let loc = mk_loc s e in
      return
      @@ Cst.View.Decl.(
           review
           @@ Decl1
                (loc, [ None ], typ, Cst.View.Term.(review @@ Omitted ghost')))
    end

  and parse_mode () : Cst.mode t =
    begin
      (let@ (), s, e = keyword' "out1" *> commit *> return () in
       return Cst.View.Mode.(review @@ Minus1 (mk_loc s e)))
      <|> (let@ (), s, e =
             keywords' [ "out"; "exists" ] *> commit *> return ()
           in
           return Cst.View.Mode.(review @@ Minus (mk_loc s e)))
      <|> (let@ (), s, e =
             keywords' [ "in"; "forall" ] *> commit *> return ()
           in
           return Cst.View.Mode.(review @@ Plus (mk_loc s e)))
      <|> let@ (), s, e = keyword' "star" *> commit *> return () in
          return Cst.View.Mode.(review @@ Star (mk_loc s e))
    end
    <?> "mode"

  and parse_mode_dec () : Cst.modeDec t =
    begin
      let* braced_args =
        many
        @@ inside "{" "}"
             (let* m = parse_mode () and* d = parse_decl () in
              return (m, d))
      in
      let* body = parse_expr () in
      let+ bare_modes = many (parse_mode ()) in
      let rec head_sym tm =
        match Cst.View.Term.view tm with
        | Cst.View.Term.Lowercase (_, s) | Cst.View.Term.Uppercase (_, s) -> s
        | Cst.View.Term.Qualified (_, s, _) -> s
        | Cst.View.Term.App (_, f, _) -> head_sym f
        | _ ->
            raise (ParseError "mode declaration: expected identifier as head")
      in
      let root =
        Cst.View.Mode.Term.(
          review
          @@ ModeTerm
               ( ghost',
                 head_sym body,
                 Cst.View.Mode.Spine.(review @@ ModeNil ghost') ))
      in
      let name_of_decl d =
        match Cst.View.Decl.view d with
        | Cst.View.Decl.Decl1 (_, ns, _, _) | Cst.View.Decl.Decl0 (_, ns, _)
          -> (
            match ns with n :: _ -> n | [] -> None)
      in
      let braced_spine =
        List.map (fun (m, d) -> (m, name_of_decl d)) braced_args
      in
      let bare_spine = List.map (fun m -> (m, None)) bare_modes in
      Cst.View.Mode.Dec.(
        review @@ ModeDec (ghost', braced_spine @ bare_spine, root))
    end
    <?> "mode declaration"

  and parse_simple_mode_dec () : Cst.modeDec t =
    parse_mode_dec () <?> "simple mode declaration"

  and parse_inst () : Cst.inst t =
    begin
      let* name, s, e = with_fc ident1 in
      let loc = mk_loc s e in
      let sym = ([], name) in
      token "="
      *>
      let+ tm = parse_expr () in
      Cst.View.Struct.Inst.(review @@ ConInst (ghost', sym, loc, tm))
    end
    <?> "instance declaration"

  and parse_sigexp () : Cst.sigexp t =
    begin
      let* base =
        keyword' "the" *> commit
        *> return Cst.View.Struct.SigExp.(review @@ Thesig ghost')
        <|> let+ name = ident1 in
            Cst.View.Struct.SigExp.(review @@ SigId (ghost', name))
      in
      let+ wheres = many (keyword' "where" *> commit *> parse_inst ()) in
      match wheres with
      | [] -> base
      | _ -> Cst.View.Struct.SigExp.(review @@ WhereSig (ghost', base, wheres))
    end

  and parse_sigdef () : Cst.sigdef t =
    begin
      let+ se = parse_sigexp () in
      Cst.View.Struct.SigDef.(review @@ SigDef (ghost', None, se))
    end
    <?> "signature definition"

  and parse_struct_dec () : Cst.structDec t =
    begin
      let* name = ident1 in
      (token ":"
      *> let+ se = parse_sigexp () in
         Cst.View.Struct.StructDec.(
           review @@ StructDecl (ghost', Some name, se)))
      <|> token "="
          *>
          let+ sym = parse_qualified () in
          Cst.View.Struct.StructDec.(
            review
            @@ StructDef
                 ( ghost',
                   Some name,
                   Cst.View.Struct.StrExp.(review @@ StrExp (ghost', sym)) ))
    end
    <?> "structure declaration"

  and parse_fixity () : int t =
    begin
      let+ s = take_while1 (fun c -> c >= '0' && c <= '9') <* whitespace in
      int_of_string s
    end
    <?> "fixity level"

  and parse_query () : (int option * int option * int option * Cst.query) t =
    begin
      let* n = parse_bound () in
      let* b = parse_bound () in
      let* d = parse_bound () in
      let+ tm = parse_expr () in
      (n, b, d, Cst.View.Query.(review @@ Query (ghost', None, tm)))
    end
    <?> "query"

  and parse_define () : Cst.define t =
    begin
      let* id =
        (fun s -> Some s) <$> parse_var () <|> Parser.string "_" *> return None
      in

      let* ty =
        let+ t = parse_expr1 () in
        match Cst.View.Term.view t with
        | Cst.View.Term.Omitted _ -> None
        | Cst.View.Term.Uppercase (_, ([], "_")) -> None
        | _ -> Some t
      in
      let+ tm = parse_expr () in
      Cst.View.(Define.(review @@ Define (Loc.(review Ghost), id, tm, ty)))
    end
    <?> "definition"

  and parse_solve () : Cst.solve t =
    begin
      let+ term = parse_expr () in
      Cst.View.Solve.(review @@ Solve (ghost', None, term))
    end
    <?> "solve command"

  and parse_bound () : int option t =
    begin
      token "_" *> return None
      <|> let+ s = take_while1 (fun c -> c >= '0' && c <= '9') <* whitespace in
          Some (int_of_string s)
    end
    <?> "bound"

  and parse_id_list () : string list t =
    begin
      inside "(" ")" (many1 (parse_var ()))
      <|> let+ id = parse_var () in
          [ id ]
    end
    <?> "identifier list"

  and parse_reduces_rel () : string t =
    begin
      token "<=" *> commit *> return "<="
      <|> token ">=" *> commit *> return ">="
      <|> token "<" *> commit *> return "<"
      <|> token ">" *> commit *> return ">"
      <|> token "=" *> commit *> return "="
    end
    <?> "reduces predicate"

  and parse_block_item () : Cst.block_item t =
    (* [x t] binds a some-variable (instantiated per world, like a lambda
       binder); {x t} declares a block-body hypothesis (like a pi binder). *)
    begin
      inside "[" "]"
        (let+ d = parse_decl () in
         Cst.View.BlockItem.(review @@ Any (ghost', d)))
      <|> inside "{" "}"
            (let+ d = parse_decl () in
             Cst.View.BlockItem.(review @@ All (ghost', d)))
    end
    <?> "block item"

  and parse_fixity_kw () : Cst.fixity t =
    begin
      keyword' "left" *> commit
      *> return Cst.View.Fixity.(review @@ Left ghost')
      <|> keyword' "right" *> commit
          *> return Cst.View.Fixity.(review @@ Right ghost')
      <|> keyword' "prefix" *> commit
          *> return Cst.View.Fixity.(review @@ Prefix ghost')
      <|> keyword' "postfix" *> commit
          *> return Cst.View.Fixity.(review @@ Postfix ghost')
      <|> keyword' "middle" *> commit
          *> return Cst.View.Fixity.(review @@ Middle ghost')
      <|> keyword' "none" *> commit
          *> return Cst.View.Fixity.(review @@ None ghost')
    end
    <?> "fixity keyword'"

  and parse_params () : string list t =
    begin
      inside "(" ")" (many (parse_var ()))
    end
    <?> "parameters"

  and parse_group : 'a. 'a t -> 'a list t = fun p -> many p
  and parse_parens : 'a. 'a t -> 'a t = fun p -> inside "(" ")" p
  and parse_braced : 'a. 'a t -> 'a t = fun p -> inside "{" "}" p
  and parse_bracketed : 'a. 'a t -> 'a t = fun p -> inside "[" "]" p

  and debug_parser : 'a t -> string -> 'a =
   fun p x ->
    Display.(
      debug @@ ((style Style.bold @@ string "Parsing") ++ nl () ++ string x));
    match Parser.parse_string ~consume:All (p : _ Parser.t) x with
    | Ok res -> res
    | Error msg -> raise (ParseError msg)

  and debug_parser_with_ops : (string * FX.fixity) list -> 'a t -> string -> 'a
      =
   fun f p x ->
    List.iter (fun (id, fix) -> Hashtbl.replace local_fixity id fix) f;
    debug_parser p x

  and source_context (src : string) (pos : int) : Display.form =
    let len = String.length src in
    let pos = Int.min pos (Int.max 0 (len - 1)) in
    let line_start =
      let i = ref pos in
      while !i > 0 && src.[!i - 1] <> '\n' do
        decr i
      done;
      !i
    in
    let line_end =
      let i = ref pos in
      while !i < len && src.[!i] <> '\n' do
        incr i
      done;
      !i
    in
    let line_text = String.sub src line_start (line_end - line_start) in
    let col = pos - line_start in
    let caret = String.make col ' ' ^ "^" in
    let line_num =
      let n = ref 1 in
      String.iteri (fun i c -> if i < line_start && c = '\n' then incr n) src;
      !n
    in
    Display.Form.(
      string (Printf.sprintf "Line %d:\n  %s\n  %s" line_num line_text caret))

  and run : 'a. 'a t -> N.namespace ref -> Cst.loc -> string -> 'a =
   fun p _ns _loc s ->
    try
      let full_parser = whitespace *> p in
      let state =
        Parser.Buffered.(
          (parse full_parser |> fun st -> feed st (`String s)) |> fun st ->
          feed st `Eof)
      in
      match state with
      | Parser.Buffered.Done (unconsumed, res) when unconsumed.len = 0 -> res
      | Parser.Buffered.Done (unconsumed, _) ->
          (* The parser stopped early without failing (e.g. [many] gave up at
             an unparseable construct).  Treating this as success would
             silently discard the rest of the input, so report it. *)
          let err_pos = String.length s - unconsumed.len in
          let loc =
            Some (mk_loc err_pos (min (err_pos + 1) (String.length s)))
          in
          let body =
            Display.Form.(
              string "Input left over after parsing (unrecognized command?)\n"
              +++ source_context s err_pos)
          in
          raise
            (FullParseError
               {
                 title = Some Display.Form.(string "Parse error");
                 subtitle = None;
                 body;
                 loc;
               })
      | Parser.Buffered.Partial _ ->
          raise (ParseError "Unexpected end of input")
      | Parser.Buffered.Fail (unconsumed, marks, msg) ->
          let err_pos = String.length s - unconsumed.len in
          let loc =
            Some (mk_loc err_pos (min (err_pos + 1) (String.length s)))
          in
          let label =
            match List.rev marks with label :: _ -> label | [] -> msg
          in
          let body =
            Display.Form.(
              string (Printf.sprintf "Expected %s\n" label)
              +++ source_context s err_pos)
          in
          raise
            (FullParseError
               {
                 title = Some Display.Form.(string "Parse error");
                 subtitle = None;
                 body;
                 loc;
               })
    with
    | ParseError m ->
        (* P-module operator-precedence errors: no offset available *)
        let body = Display.Form.(string m +++ nl () +++ source_context s 0) in
        Error.Error.err ~stage:Error.Error.Parse
          Display.Form.(string "Parse error" +++ nl () +++ body)
    | FullParseError { title; body; _ } ->
        let title_form =
          Option.value title ~default:Display.Form.(string "Parse error")
        in
        Error.Error.err ~stage:Error.Error.Parse
          Display.Form.(title_form +++ nl () +++ body)
end

module ModernCst = Cst.Make_Cst (Paths.Paths_)

module Modern : MODERN.MODERN =
  Make_Modern (Paths.Paths_) (ModernCst) (Names.Names_) (Parsing.Parser.Parser)

let () =
  Printexc.register_printer (function
    | Modern.ParseError msg -> Some msg
    | _ -> None)

let () =
  Printexc.register_printer (function
    | Modern.FullParseError _ -> Some "Parse error"
    | _ -> None)

(* Re-export sub-modules so they are accessible outside the library *)
module Cmd = Cmd
module CMD = CMD
module MODERN = MODERN
module Debug_Cmd = Cmd.Make_Cmd (Modern)
