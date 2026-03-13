open! Basis

(* Lexer *)
(* Author: Frank Pfenning *)
(* Modified: Brigitte Pientka *)
module MakeLexer (Lexer__0 : sig
  module Stream' : STREAM
end) : LEXER = struct
  module Stream = Lexer__0.Stream'

  (*! structure Paths = Paths' !*)
  open! struct
    module P = Paths
  end

  type idCase_ = Upper | Lower | Quoted

  (* [A-Z]<id> or _<id> *)
  (* any other <id> *)
  (* '<id>', currently unused *)
  type token_ =
    | Eof
    | Dot
    | Pathsep
    | Colon
    | Lparen
    | Rparen
    | Lbracket
    | Rbracket
    | Lbrace
    | Rbrace
    | Backarrow
    | Arrow
    | Type
    | Equal
    | Id of idCase_ * string
    | Underscore
    | Infix
    | Prefix
    | Postfix
    | Name
    | Define
    | Solve
    | Query
    | Fquery
    | Compile
    | Querytabled
    | Mode
    | Unique
    | Covers
    | Total
    | Terminates
    | Block
    | Worlds
    | Reduces
    | Tabled
    | Keeptable
    | Theorem
    | Prove
    | Establish
    | Assert
    | Abbrev
    | Trustme
    | Freeze
    | Thaw
    | Subord
    | Deterministic
    | Clause
    | Sig
    | Struct
    | Where
    | Include
    | Open
    | Use
    | String of string

  (* end of file or stream, also `%.' *)
  (* `.' *)
  (* `.' between <id>s *)
  (* `:' *)
  (* `(' `)' *)
  (* `[' `]' *)
  (* `{' `}' *)
  (* `<-' `->' *)
  (* `type' *)
  (* `=' *)
  (* identifer *)
  (* `_' *)
  (* `%infix' `%prefix' `%postfix' *)
  (* `%name' *)
  (* `%define' *)
  (* -rv 8/27/01 *)
  (* `%solve' *)
  (* `%query' *)
  (* `%fquery' *)
  (* '%compile' *)
  (* -ABP 4/4/03 *)
  (* `%querytabled *)
  (* `%mode' *)
  (* `%unique' *)
  (* -fp 8/17/03 *)
  (* `%covers' *)
  (* -fp 3/7/01 *)
  (* `%total' *)
  (* -fp 3/18/01 *)
  (* `%terminates' *)
  (* `%reduces' *)
  (* -bp  6/05/99 *)
  (* `%tabled' *)
  (* -bp 11/20/01 *)
  (* `%keepTable' *)
  (* -bp 11/20/01 *)
  (* `%theorem' *)
  (* `%block' *)
  (* -cs 5/29/01 *)
  (* `%worlds' *)
  (* `%prove' *)
  (* `%establish' *)
  (* `%assert' *)
  (* `%abbrev' *)
  (* `%trustme' *)
  (* -fp 8/26/05 *)
  (* `%freeze' *)
  (* `%thaw' *)
  (* `%subord' *)
  (* -gaw 07/11/08 *)
  (* `%deterministic' *)
  (* -rv 11/27/01 *)
  (* `%clause' *)
  (* -fp 8/9/02 *)
  (* `%sig' *)
  (* `%struct' *)
  (* `%where' *)
  (* `%include' *)
  (* `%open' *)
  (* `%use' *)
  (* string constants *)
  exception Error of string

  let rec error (r, msg) = raise (Error (P.wrap (r, msg)))

  (* isSym (c) = B iff c is a legal symbolic identifier constituent *)
  (* excludes quote character and digits, which are treated specially *)
  (* Char.contains stages its computation *)
  let isSym : char -> bool = Char.contains "_!&$^+/<=>?@~|#*`;,-\\"

  (* isUFT8 (c) = assume that if a character is not ASCII it must be
     part of a UTF8 Unicode encoding.  Treat these as lowercase
     identifiers.  Somewhat of a hack until there is native Unicode
     string support. *)
  let rec isUTF8 c = not (Char.isAscii c)

  (* isQuote (c) = B iff c is the quote character *)
  let rec isQuote c = c = '\''

  (* isIdChar (c) = B iff c is legal identifier constituent *)
  let rec isIdChar c =
    Char.isLower c || Char.isUpper c || Char.isDigit c || isSym c || isQuote c
    || isUTF8 c

  (* stringToToken (idCase, string, region) = (token, region)
     converts special identifiers into tokens, returns ID token otherwise
  *)
  let rec stringToToken = function
    | Lower, "<-", r -> (Backarrow, r)
    | Lower, "->", r -> (Arrow, r)
    | Upper, "_", r -> (Underscore, r)
    | Lower, "=", r -> (Equal, r)
    | Lower, "type", r -> (Type, r)
    | idCase, s, r -> (Id (idCase, s), r)

  (* lex (inputFun) = (token, region) stream

     inputFun maintains state, reading input one line at a time and
     returning a string terminated by <newline> each time.
     The end of the stream is signalled by a string consisting only of ^D
     Argument to inputFun is the character position.
  *)
  let rec lex (inputFun : int -> string) =
    let s = ref "" and left = ref 0 and right = ref 0 in
    let _ = P.resetLines () in
    let eOFString_ = String.str '\004' in
    let rec readNext () =
      let nextLine = inputFun !right in
      let nextSize = String.size nextLine in
      begin if nextSize = 0 then begin
        s := eOFString_;
        begin
          left := !right;
          right := !right + 1
        end
      end
      (* fake EOF character string *) else begin
        s := nextLine;
        begin
          left := !right;
          begin
            right := !right + nextSize;
            P.newLine !left
          end
        end
      end
      end
      (* end of file? *)
      (* remember new line position *)
    in
    let rec char i =
      begin if i >= !right then begin
        readNext ();
        char i
      end
      else String.sub (!s, i - !left)
      end
    in
    let rec string (i, j) = String.substring (!s, i - !left, j - i) in
    let rec idToToken (idCase, P.Reg (i, j)) =
      stringToToken (idCase, string (i, j), P.Reg (i, j))
    in
    let rec qidToToken (P.Reg (i, j)) =
      (Id (Lower, string (i, j + 1)), P.Reg (i, j + 1))
    in
    let rec lexInitial = function
      | ':', i -> (Colon, P.Reg (i - 1, i))
      | '.', i -> (Dot, P.Reg (i - 1, i))
      | '(', i -> (Lparen, P.Reg (i - 1, i))
      | ')', i -> (Rparen, P.Reg (i - 1, i))
      | '[', i -> (Lbracket, P.Reg (i - 1, i))
      | ']', i -> (Rbracket, P.Reg (i - 1, i))
      | '{', i -> (Lbrace, P.Reg (i - 1, i))
      | '}', i -> (Rbrace, P.Reg (i - 1, i))
      | '%', i -> lexPercent (char i, i + 1)
      | '_', i -> lexID (Upper, P.Reg (i - 1, i))
      | '\'', i -> lexID (Lower, P.Reg (i - 1, i))
      | '\004', i -> (Eof, P.Reg (i - 1, i - 1))
      | '"', i -> lexString (P.Reg (i - 1, i))
      | c, i -> begin
          if Char.isSpace c then lexInitial (char i, i + 1)
          else begin
            if Char.isUpper c then lexID (Upper, P.Reg (i - 1, i))
            else begin
              if Char.isDigit c then lexID (Lower, P.Reg (i - 1, i))
              else begin
                if Char.isLower c then lexID (Lower, P.Reg (i - 1, i))
                else begin
                  if isSym c then lexID (Lower, P.Reg (i - 1, i))
                  else begin
                    if isUTF8 c then lexID (Lower, P.Reg (i - 1, i))
                    else
                      error
                        ( P.Reg (i - 1, i),
                          "Illegal character " ^ Char.toString c )
                  end
                end
              end
            end
          end
        end
    (* lexQUID (i-1,i) *)
    and lexID (idCase, P.Reg (i, j)) =
      let rec lexID' j =
        begin if isIdChar (char j) then lexID' (j + 1)
        else idToToken (idCase, P.Reg (i, j))
        end
      in
      lexID' j
    and lexQUID (P.Reg (i, j)) =
      begin if Char.isSpace (char j) then
        error (P.Reg (i, j + 1), "Whitespace in quoted identifier")
      else begin
        if isQuote (char j) then qidToToken (P.Reg (i, j))
        else lexQUID (P.Reg (i, j + 1))
      end
      end
    (* recover by adding implicit quote? *)
    (* qidToToken (i, j) *)
    and lexPercent = function
      | '.', i -> (Eof, P.Reg (i - 2, i))
      | '{', i -> lexPercentBrace (char i, i + 1)
      | '%', i -> lexComment ('%', i)
      | c, i -> begin
          if isIdChar c then lexPragmaKey (lexID (Quoted, P.Reg (i - 1, i)))
          else begin
            if Char.isSpace c then lexComment (c, i)
            else
              error
                ( P.Reg (i - 1, i),
                  "Comment character `%' not followed by white space" )
          end
        end
    and lexPragmaKey = function
      | Id (_, "infix"), r -> (Infix, r)
      | Id (_, "prefix"), r -> (Prefix, r)
      | Id (_, "postfix"), r -> (Postfix, r)
      | Id (_, "mode"), r -> (Mode, r)
      | Id (_, "unique"), r -> (Unique, r)
      | Id (_, "terminates"), r -> (Terminates, r)
      | Id (_, "block"), r -> (Block, r)
      | Id (_, "worlds"), r -> (Worlds, r)
      | Id (_, "covers"), r -> (Covers, r)
      | Id (_, "total"), r -> (Total, r)
      | Id (_, "reduces"), r -> (Reduces, r)
      | Id (_, "tabled"), r -> (Tabled, r)
      | Id (_, "keepTable"), r -> (Keeptable, r)
      | Id (_, "theorem"), r -> (Theorem, r)
      | Id (_, "prove"), r -> (Prove, r)
      | Id (_, "establish"), r -> (Establish, r)
      | Id (_, "assert"), r -> (Assert, r)
      | Id (_, "abbrev"), r -> (Abbrev, r)
      | Id (_, "name"), r -> (Name, r)
      | Id (_, "define"), r -> (Define, r)
      | Id (_, "solve"), r -> (Solve, r)
      | Id (_, "query"), r -> (Query, r)
      | Id (_, "fquery"), r -> (Fquery, r)
      | Id (_, "compile"), r -> (Compile, r)
      | Id (_, "querytabled"), r -> (Querytabled, r)
      | Id (_, "trustme"), r -> (Trustme, r)
      | Id (_, "subord"), r -> (Subord, r)
      | Id (_, "freeze"), r -> (Freeze, r)
      | Id (_, "thaw"), r -> (Thaw, r)
      | Id (_, "deterministic"), r -> (Deterministic, r)
      | Id (_, "clause"), r -> (Clause, r)
      | Id (_, "sig"), r -> (Sig, r)
      | Id (_, "struct"), r -> (Struct, r)
      | Id (_, "where"), r -> (Where, r)
      | Id (_, "include"), r -> (Include, r)
      | Id (_, "open"), r -> (Open, r)
      | Id (_, "use"), r -> (Use, r)
      | Id (_, s), r ->
          error
            ( r,
              ("Unknown keyword %" ^ s)
              ^ " (single line comment starts with `%<whitespace>' or `%%')" )
    (* -fp 08/09/02 *)
    (* -rv 11/27/01 *)
    (* -gaw 07/11/08 *)
    (* -ABP 4/4/03 *)
    (* -rv 8/27/01 *)
    (* -bp 20/11/04 *)
    (* -bp 20/11/01 *)
    (* -bp 6/5/99 *)
    (* -fp 3/18/01 *)
    (* -cs 6/3/01 *)
    (* -fp 8/17/03 *)
    and lexComment = function
      | '\n', i -> lexInitial (char i, i + 1)
      | '%', i -> lexCommentPercent (char i, i + 1)
      | '\004', i ->
          error
            (P.Reg (i - 1, i - 1), "Unclosed single-line comment at end of file")
      | c, i -> lexComment (char i, i + 1)
    (* recover: (EOF, (i-1,i-1)) *)
    and lexCommentPercent = function
      | '.', i -> (Eof, P.Reg (i - 2, i))
      | c, i -> lexComment (c, i)
    and lexPercentBrace (c, i) = lexDComment (c, 1, i)
    and lexDComment = function
      | '}', l, i -> lexDCommentRBrace (char i, l, i + 1)
      | '%', l, i -> lexDCommentPercent (char i, l, i + 1)
      | '\004', l, i ->
          error
            (P.Reg (i - 1, i - 1), "Unclosed delimited comment at end of file")
      | c, l, i -> lexDComment (char i, l, i + 1)
    (* recover: (EOF, (i-1,i-1)) *)
    (* pass comment beginning for error message? *)
    and lexDCommentPercent = function
      | '{', l, i -> lexDComment (char i, l + 1, i + 1)
      | '.', l, i ->
          error
            ( P.Reg (i - 2, i),
              "Unclosed delimited comment at end of file token `%.'" )
      | c, l, i -> lexDComment (c, l, i)
    (* recover: (EOF, (i-2,i)) *)
    and lexDCommentRBrace = function
      | '%', 1, i -> lexInitial (char i, i + 1)
      | '%', l, i -> lexDComment (char i, l - 1, i + 1)
      | c, l, i -> lexDComment (c, l, i)
    and lexString (P.Reg (i, j)) =
      begin match char j with
      | '"' -> (String (string (i, j + 1)), P.Reg (i, j + 1))
      | '\n' ->
          error (P.Reg (i - 1, i - 1), "Unclosed string constant at end of line")
      | '\004' ->
          error (P.Reg (i - 1, i - 1), "Unclosed string constant at end of file")
      | _ -> lexString (P.Reg (i, j + 1))
      end
      (* recover: (EOL, (i-1,i-1)) *)
      (* recover: (EOF, (i-1,i-1)) *)
    in
    let rec lexContinue j = Stream.delay (function () -> lexContinue' j)
    and lexContinue' j = lexContinue'' (lexInitial (char j, j + 1))
    and lexContinue'' = function
      | (Id _, P.Reg (i, j)) as mt -> Stream.Cons (mt, lexContinueQualId j)
      | (token, P.Reg (i, j)) as mt -> Stream.Cons (mt, lexContinue j)
    and lexContinueQualId j =
      Stream.delay (function () -> lexContinueQualId' j)
    and lexContinueQualId' j =
      begin if char j = '.' then begin
        if isIdChar (char (j + 1)) then
          Stream.Cons ((Pathsep, P.Reg (j, j + 1)), lexContinue (j + 1))
        else Stream.Cons ((Dot, P.Reg (j, j + 1)), lexContinue (j + 1))
      end
      else lexContinue' j
      end
    in
    lexContinue 0

  (* local state maintained by the lexer *)
  (* current string (line) *)
  (* position of first character in s *)
  (* position after last character in s *)
  (* initialize line counter *)
  (* neither lexer nor parser should ever try to look beyond EOF *)
  (* readNext () = ()
         Effect: read the next line, updating s, left, and right

         readNext relies on the invariant that identifiers are never
         spread across lines
      *)
  (* char (i) = character at position i
         Invariant: i >= !left
         Effects: will read input if i >= !right
      *)
  (* string (i,j) = substring at region including i, excluding j
         Invariant: i >= !left and i < j and j < !right
                    Note that the relevant parts must already have been read!
         Effects: None
      *)
  (* The remaining functions do not access the state or *)
  (* stream directly, using only functions char and string *)
  (* Quote characters are part of the name *)
  (* Treat quoted identifiers as lowercase, since they no longer *)
  (* override infix state.  Quoted identifiers are now only used *)
  (* inside pragmas *)
  (* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).

       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
  (* recover by ignoring: lexInitial (char(i), i+1) *)
  (* lexQUID is currently not used --- no quoted identifiers *)
  (* comments are now started by %<whitespace> *)
  (*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)
  (* functions lexing delimited comments below take nesting level l *)

  (* fun lex (inputFun) = let ... in ... end *)
  let rec inputLine97 instream =
    begin match TextIO.inputLine instream with Some s -> s | None -> ""
    end

  let rec lexStream instream = lex (function i -> inputLine97 instream)

  let rec lexTerminal (prompt0, prompt1) =
    lex (function
      | 0 -> begin
          print prompt0;
          inputLine97 TextIO.stdIn
        end
      | i -> begin
          print prompt1;
          inputLine97 TextIO.stdIn
        end)

  let rec toString' = function
    | Dot -> "."
    | Pathsep -> "."
    | Colon -> ":"
    | Lparen -> "("
    | Rparen -> ")"
    | Lbracket -> "["
    | Rbracket -> "]"
    | Lbrace -> "{"
    | Rbrace -> "}"
    | Backarrow -> "<-"
    | Arrow -> "->"
    | Type -> "type"
    | Equal -> "="
    | Underscore -> "_"
    | Infix -> "%infix"
    | Prefix -> "%prefix"
    | Postfix -> "%postfix"
    | Name -> "%name"
    | Define -> "%define"
    | Solve -> "%solve"
    | Query -> "%query"
    | Fquery -> "%fquery"
    | Compile -> "%compile"
    | Querytabled -> "%querytabled"
    | Mode -> "%mode"
    | Unique -> "%unique"
    | Covers -> "%covers"
    | Total -> "%total"
    | Terminates -> "%terminates"
    | Block -> "%block"
    | Worlds -> "%worlds"
    | Reduces -> "%reduces"
    | Tabled -> "%tabled"
    | Keeptable -> "%keepTable"
    | Theorem -> "%theorem"
    | Prove -> "%prove"
    | Establish -> "%establish"
    | Assert -> "%assert"
    | Abbrev -> "%abbrev"
    | Trustme -> "%trustme"
    | Subord -> "%subord"
    | Freeze -> "%freeze"
    | Thaw -> "%thaw"
    | Deterministic -> "%deterministic"
    | Clause -> "%clause"
    | Sig -> "%sig"
    | Struct -> "%struct"
    | Where -> "%where"
    | Include -> "%include"
    | Open -> "%open"
    | Use -> "%use"
  (* -fp 08/09/02 *)
  (* -rv 11/27/01. *)
  (*  -bp 04/11/03. *)
  (*  -bp 20/11/01. *)
  (*  -bp 6/5/99. *)
  (* -cs 6/3/01. *)
  (* -ABP 4/4/03 *)
  (* -rv 8/27/01 *)

  let rec toString = function
    | Id (_, s) -> ("identifier `" ^ s) ^ "'"
    | Eof -> "end of file or `%.'"
    | String s -> "constant string " ^ s
    | token -> ("`" ^ toString' token) ^ "'"

  exception NotDigit of char

  (* charToNat(c) = n converts character c to decimal equivalent *)
  (* raises NotDigit(c) if c is not a digit 0-9 *)
  let rec charToNat c =
    let digit = Char.ord c - Char.ord '0' in
    begin if digit < 0 || digit > 9 then raise (NotDigit c) else digit
    end

  (* stringToNat(s) = n converts string s to a natural number *)
  (* raises NotDigit(c) if s contains character c which is not a digit *)
  let rec stringToNat s =
    let l = String.size s in
    let rec stn (i, n) =
      begin if i = l then n
      else stn (i + 1, (10 * n) + charToNat (String.sub (s, i)))
      end
    in
    stn (0, 0)

  (* isUpper (s) = true, if s is a string starting with an uppercase
     letter or underscore (_).
  *)
  let rec isUpper = function
    | "" -> false
    | s ->
        let c = String.sub (s, 0) in
        Char.isUpper c || c = '_'
end

(*! structure Paths' : PATHS !*)
(* local ... *)
(* functor Lexer *)
module Lexer = MakeLexer (struct
  module Stream' = Stream
end)
(*! structure Paths' = Paths !*)
