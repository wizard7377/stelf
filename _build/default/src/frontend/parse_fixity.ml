# 1 "src/frontend/parse_fixity.sig.ml"
open! Basis;;
(* Parsing Fixity Declarations *);;
(* Author: Frank Pfenning *);;
module type PARSE_FIXITY = sig
                           (*! structure Parsing : PARSING !*)
                           module Names : NAMES
                           val
                             parseFixity' : ((Names.qid_ * Paths.region) *
                                             Names.Fixity.fixity)
                             Parsing.parser
                           val
                             parseNamePref' : ((Names.qid_ * Paths.region) *
                                               (string list * string list))
                             Parsing.parser
                           end;;
(* signature PARSE_FIXITY *);;
# 1 "src/frontend/parse_fixity.fun.ml"
open! Parsing;;
open! Basis;;
(* Parsing Fixity and Name Preference Declarations *);;
(* Author: Frank Pfenning *);;
module ParseFixity(ParseFixity__0: sig module Names' : NAMES end) : PARSE_FIXITY
  =
  struct
    (*! structure Parsing = Parsing' !*);;
    module Names = Names';;
    open!
      struct
        module L = Lexer;;
        module LS = Lexer.Stream;;
        module FX = Names.Fixity;;
        let rec fixToString (FX.Strength p) = Int.toString p;;
        let rec idToPrec (r, (_, name)) =
          let prec =
            try (FX.Strength (L.stringToNat name))
            with 
                 | Overflow -> Parsing.error (r, "Precedence too large")
                 | L.NotDigit _
                     -> Parsing.error (r, "Precedence not a natural number")
            in begin
            if (FX.less (prec, FX.minPrec)) || (FX.less (FX.maxPrec, prec))
            then
            Parsing.error
            (r,
             ((("Precedence out of range [" ^ (fixToString FX.minPrec)) ^ ",")
                ^ (fixToString FX.maxPrec))
               ^ "]")
            else prec end;;
        let rec parseFixCon =
          function 
                   | (fixity, LS.Cons ((L.Id (_, name), r), s'))
                       -> ((((Names.Qid ([], name)), r), fixity),
                           LS.expose s')
                   | (fixity, LS.Cons ((t, r), s'))
                       -> Parsing.error
                          (r,
                           "Expected identifier to assign fixity, found " ^
                             (L.toString t));;
        let rec parseFixPrec =
          function 
                   | (fixity, LS.Cons ((L.Id id, r), s'))
                       -> parseFixCon
                          (fixity (idToPrec (r, id)), LS.expose s')
                   | (fixity, LS.Cons ((t, r), s'))
                       -> Parsing.error
                          (r, "Expected precedence, found " ^ (L.toString t));;
        let rec parseInfix =
          function 
                   | LS.Cons ((L.Id (lower_, "none"), r), s')
                       -> parseFixPrec
                          (function 
                                    | p -> (FX.Infix (p, FX.none_)),
                           LS.expose s')
                   | LS.Cons ((L.Id (lower_, "left"), r), s')
                       -> parseFixPrec
                          (function 
                                    | p -> (FX.Infix (p, FX.left_)),
                           LS.expose s')
                   | LS.Cons ((L.Id (lower_, "right"), r), s')
                       -> parseFixPrec
                          (function 
                                    | p -> (FX.Infix (p, FX.right_)),
                           LS.expose s')
                   | LS.Cons ((t, r), s')
                       -> Parsing.error
                          (r,
                           "Expected associatitivy `left', `right', or `none', found "
                             ^ (L.toString t));;
        let rec parsePrefix f = parseFixPrec (FX.prefix_, f);;
        let rec parsePostfix f = parseFixPrec (FX.postfix_, f);;
        let rec parseFixity' =
          function 
                   | LS.Cons ((infix_, r), s') -> parseInfix (LS.expose s')
                   | LS.Cons ((prefix_, r), s') -> parsePrefix (LS.expose s')
                   | LS.Cons ((postfix_, r), s')
                       -> parsePostfix (LS.expose s');;
        let rec parseFixity s = parseFixity' (LS.expose s);;
        let rec parseName5 =
          function 
                   | (name, r0, prefENames, prefUNames, LS.Cons
                      ((L.Id (_, prefUName), r), s'))
                       -> parseName5
                          (name, r0, prefENames, prefUNames @ [prefUName],
                           LS.expose s')
                   | (name, r0, prefENames, prefUNames, LS.Cons
                      ((rparen_, r), s'))
                       -> ((((Names.Qid ([], name)), r0),
                            (prefENames, prefUNames)),
                           LS.expose s')
                   | (name, r0, prefENames, prefUNames, LS.Cons ((t, r), s'))
                       -> Parsing.error
                          (r,
                           "Expected name preference or ')', found " ^
                             (L.toString t));;
        let rec parseName3 =
          function 
                   | (name, r0, prefEName, LS.Cons
                      ((L.Id (_, prefUName), r), s'))
                       -> ((((Names.Qid ([], name)), r0),
                            (prefEName, [prefUName])),
                           LS.expose s')
                   | (name, r0, prefEName, LS.Cons ((lparen_, r), s'))
                       -> parseName5 (name, r0, prefEName, [], LS.expose s')
                   | (name, r0, prefEName, f)
                       -> ((((Names.Qid ([], name)), r0), (prefEName, [])),
                           f);;
        let rec parseName4 =
          function 
                   | (name, r0, prefENames, LS.Cons
                      ((L.Id (_, prefEName), r), s')) -> begin
                       if L.isUpper prefEName then
                       parseName4
                       (name, r0, prefENames @ [prefEName], LS.expose s')
                       else
                       Parsing.error
                       (r,
                        "Expected uppercase identifer, found " ^ prefEName)
                       end
                   | (name, r0, prefENames, LS.Cons ((rparen_, r), s'))
                       -> parseName3 (name, r0, prefENames, LS.expose s')
                   | (name, r0, prefENames, LS.Cons ((t, r), s'))
                       -> Parsing.error
                          (r,
                           "Expected name preference or ')', found " ^
                             (L.toString t));;
        let rec parseName2 =
          function 
                   | (name, r0, LS.Cons ((L.Id (_, prefEName), r), s'))
                       -> begin
                       if L.isUpper prefEName then
                       parseName3 (name, r0, [prefEName], LS.expose s') else
                       Parsing.error
                       (r,
                        "Expected uppercase identifer, found " ^ prefEName)
                       end
                   | (name, r0, LS.Cons ((lparen_, r), s'))
                       -> parseName4 (name, r0, [], LS.expose s')
                   | (name, r0, LS.Cons ((t, r), s'))
                       -> Parsing.error
                          (r,
                           "Expected name preference, found " ^
                             (L.toString t));;
        let rec parseName1 =
          function 
                   | LS.Cons ((L.Id (_, name), r), s')
                       -> parseName2 (name, r, LS.expose s')
                   | LS.Cons ((t, r), s')
                       -> Parsing.error
                          (r,
                           "Expected identifer to assign name preference, found "
                             ^ (L.toString t));;
        let rec parseNamePref' (LS.Cons ((name_, r), s')) =
          parseName1 (LS.expose s');;
        let rec parseNamePref s = parseNamePref' (LS.expose s);;
        end;;
    (* some shorthands *);;
    (* idToPrec (region, (idCase, name)) = n
       where n is the precedence indicated by name, which should consists
       of all digits.  Raises error otherwise, or if precedence it too large
    *);;
    (*-----------------------------*);;
    (* Parsing fixity declarations *);;
    (*-----------------------------*);;
    (* parseFixCon ""id"" *);;
    (* parseFixPrec ""n id"" where n is precedence *);;
    (* parseInfix ""none|left|right n id"" where n is precedence *);;
    (* parsePrefix ""n id"" where n is precedence *);;
    (* parsePostfix ""n id"" where n is precedence *);;
    (* parseFixity' : lexResult stream -> (name,fixity) * lexResult stream
       Invariant: token stream starts with %infix, %prefix or %postfix
    *);;
    (* anything else should be impossible *);;
    (*------------------------------------*);;
    (* Parsing name preferences %name ... *);;
    (*------------------------------------*);;
    (* parseName5 ""string ... )"" or "")"" *);;
    (* prefUName should be lower case---not enforced *);;
    (* parseName3 ""string"" or """" *);;
    (* prefUName should be lower case---not enforced *);;
    (* parseName4 ""string ... )"" or "")"" *);;
    (* parseName2 ""string"" or ""string string""
              or ""(string ... ) string""  or "" string (string ...)""
              or ""(string ... ) (string ...)"" *);;
    (* parseName1 ""id string"" or ""id string string"" *);;
    (* parseNamePref' ""%name id string"" or ""%name id string string""
       Invariant: token stream starts with %name
    *);;
    let parseFixity' = parseFixity';;
    let parseNamePref' = parseNamePref';;
    end;;
(*! structure Parsing' : PARSING !*);;
(* local ... in *);;
(* functor ParseFixity *);;
# 1 "src/frontend/parse_fixity.sml.ml"
