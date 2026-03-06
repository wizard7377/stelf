open! Basis;;
module PrintOMDoc(PrintOMDoc__0: sig
                                 (* Printing *)
                                 (* Author: Frank Pfenning *)
                                 (* Modified: Jeff Polakow *)
                                 (* Modified: Carsten Schuermann *)
                                 (* Modified: Florian Rabe *)
                                 (*! structure IntSyn' : INTSYN !*)
                                 module Whnf : WHNF
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 module Abstract : ABSTRACT
                                 (*! sharing Abstract.IntSyn = IntSyn' !*)
                                 module Constraints : CONSTRAINTS
                                 (*! sharing Constraints.IntSyn = IntSyn' !*)
                                 module Names : NAMES
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 module Formatter' : FORMATTER
                                 end) : PRINT_OMDOC
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    module Formatter = Formatter';;
    open!
      struct
        module I = IntSyn;;
        let indent = ref 0;;
        let tabstring = "   ";;
        let rec tabs n = begin
          if n <= 0 then "" else tabstring ^ (tabs (n - 1)) end;;
        let rec ind_reset () = indent := 0;;
        let rec ind n = indent := ((! indent) + n);;
        let rec unind n = indent := ((! indent) - n);;
        let rec nl_ind () =
          begin
            indent := ((! indent) + 1);"\n" ^ (tabs (! indent))
            end;;
        let rec nl_unind () =
          begin
            indent := ((! indent) - 1);"\n" ^ (tabs (! indent))
            end;;
        let rec nl () = "\n" ^ (tabs (! indent));;
        let rec escape s =
          let rec escapelist =
            function 
                     | [] -> []
                     | ('&' :: rest)
                         -> (String.explode "&amp;") @ (escapelist rest)
                     | ('<' :: rest)
                         -> (String.explode "&lt;") @ (escapelist rest)
                     | ('>' :: rest)
                         -> (String.explode "&gt;") @ (escapelist rest)
                     | (c :: rest) -> (c :: escapelist rest)
            in String.implode (escapelist (String.explode s));;
        let namesafe = ref true;;
        let rec replace c = begin
          if (Char.isAlphaNum c) || (Char.contains ":_-." c) then
          String.str c else "_" end;;
        let rec name_ cid =
          let n = I.conDecName (I.sgnLookup cid)
            in let name = String.translate replace n
                 in let start = begin
                      if
                      (Char.isAlpha (String.sub (name, 0))) ||
                        ((String.sub (name, 0)) = '_')
                      then "" else "_" end in begin
                      if ! namesafe then
                      ((start ^ name) ^ "__c") ^ (Int.toString cid) else n
                      end;;
        let rec varName_ (x, n) =
          let name = String.translate replace n
            in let start = begin
                 if
                 (Char.isAlpha (String.sub (name, 0))) ||
                   ((String.sub (name, 0)) = '_')
                 then "" else "_" end in begin
                 if ! namesafe then
                 ((start ^ name) ^ "__v") ^ (Int.toString x) else n end;;
        let rec str_ s = s;;
        let rec sexp l = String.concat l;;
        let rec spineLength =
          function 
                   | nil_ -> 0
                   | I.SClo (s_, _) -> spineLength s_
                   | I.App (_, s_) -> 1 + (spineLength s_);;
        let rec fmtCon =
          function 
                   | (g_, I.BVar x)
                       -> let I.Dec (Some n, _) = I.ctxDec (g_, x)
                            in sexp
                               [(Str
                                 (("<om:OMV name=\"" ^
                                     (varName_
                                      (((I.ctxLength g_) - x) + 1, n)))
                                    ^ "\"/>"))]
                   | (g_, I.Const cid)
                       -> sexp
                          [(Str "<om:OMS cd=\"global\" name=\""); name_ cid;
                           (Str "\"/>")]
                   | (g_, I.Def cid)
                       -> sexp
                          [(Str "<om:OMS cd=\"global\" name=\""); name_ cid;
                           (Str "\"/>")]
                   | (g_, I.FgnConst (csid, Condec_))
                       -> sexp [(Str "FgnConst")];;
        let rec fmtUni =
          function 
                   | type_ -> (Str "<om:OMS cd=\"twelf\" name=\"type\"/>")
                   | kind_ -> (Str "<om:OMS cd=\"twelf\" name=\"kind\"/>");;
        let rec fmtExpW =
          function 
                   | (g_, (I.Uni l_, s), _) -> sexp [fmtUni l_]
                   | (g_, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s), imp)
                       -> begin
                          match p_
                          with 
                               | maybe_
                                   -> let (I.Dec (Some name, v1'_) as d'_) =
                                        Names.decLUName (g_, d_)
                                        in let g'_ = (I.Decl (g_, d'_))
                                             in let _ = ind 1
                                                  in let fmtBody =
                                                       fmtExp
                                                       (g'_, (v2_, I.dot1 s),
                                                        Int.max (0, imp - 1))
                                                       in let _ = ind 1
                                                            in let fmtType =
                                                                 fmtExp
                                                                 (g_,
                                                                  (v1'_, s),
                                                                  0)
                                                                 in let _ =
                                                                    unind 2
                                                                    in 
                                                                    let Pi_ =
                                                                    begin
                                                                    if
                                                                    imp > 0
                                                                    then
                                                                    "implicit_Pi"
                                                                    else "Pi"
                                                                    end
                                                                    in 
                                                                    let id =
                                                                    varName_
                                                                    (I.ctxLength
                                                                    g'_,
                                                                    name)
                                                                    in 
                                                                    fmtBinder
                                                                    (Pi_,
                                                                    name, id,
                                                                    fmtType,
                                                                    fmtBody)
                               | no_
                                   -> let g'_ = (I.Decl (g_, d_))
                                        in sexp
                                           [(Str "<om:OMA>"); nl_ind ();
                                            (Str
                                             "<om:OMS cd=\"twelf\" name=\"arrow\"/>");
                                            nl (); fmtExp (g_, (v1_, s), 0);
                                            nl ();
                                            fmtExp (g'_, (v2_, I.dot1 s), 0);
                                            nl_unind (); (Str "</om:OMA>")]
                          end
                   | (g_, (I.Root (h_, s_), s), _)
                       -> let l = spineLength s_
                            in let out = ref ""
                                 in let _ = begin
                                      if l = 0 then
                                      out := ((! out) ^ (fmtCon (g_, h_)))
                                      else
                                      let _ =
                                        out :=
                                          (((! out) ^ "<om:OMA>") ^
                                             (nl_ind ()))
                                        in let (test, cid) =
                                             begin
                                             match h_
                                             with 
                                                  | I.Const c -> (true, c)
                                                  | I.Skonst c -> (true, c)
                                                  | I.Def c -> (true, c)
                                                  | I.NSDef c -> (true, c)
                                                  | _ -> (false, 0)
                                             end
                                             in let imp =
                                                  IntSyn.conDecImp
                                                  (IntSyn.sgnLookup cid)
                                                  in let (test, args) = begin
                                                       if test then
                                                       begin
                                                       match Names.getFixity
                                                             cid
                                                       with 
                                                            | Names.Fixity.Infix
                                                                (_, _)
                                                                -> (true,
                                                                    imp + 2)
                                                            | _ -> (false, 0)
                                                       end else (false, 0)
                                                       end
                                                       in let _ = begin
                                                            if
                                                            test &&
                                                              (l > args)
                                                            then
                                                            out :=
                                                              (((! out) ^
                                                                  "<om:OMA>")
                                                                 ^
                                                                 (nl_ind ()))
                                                            else () end
                                                            in out :=
                                                                 ((((! out) ^
                                                                    (fmtCon
                                                                    (g_, h_)))
                                                                    ^
                                                                    (fmtSpine
                                                                    (g_,
                                                                    (s_, s),
                                                                    args))) ^
                                                                    "</om:OMA>")
                                      end in ! out
                   | (g_, (I.Lam (d_, u_), s), imp)
                       -> let (I.Dec (Some name, v_) as d'_) =
                            Names.decLUName (g_, d_)
                            in let g'_ = (I.Decl (g_, d'_))
                                 in let _ = ind 1
                                      in let fmtBody =
                                           fmtExp
                                           (g'_, (u_, I.dot1 s),
                                            Int.max (0, imp - 1))
                                           in let _ = ind 1
                                                in let fmtType =
                                                     fmtExp (g_, (v_, s), 0)
                                                     in let _ = unind 2
                                                          in let Lam_ = begin
                                                               if imp > 0
                                                               then
                                                               "implicit_lambda"
                                                               else "lambda"
                                                               end
                                                               in let id =
                                                                    varName_
                                                                    (I.ctxLength
                                                                    g'_,
                                                                    name)
                                                                    in 
                                                                    fmtBinder
                                                                    (Lam_,
                                                                    name, id,
                                                                    fmtType,
                                                                    fmtBody)
                   | (g_, (I.FgnExp (csid, f_), s), 0)
                       -> sexp [(Str "FgnExp")]
        and fmtExp (g_, (u_, s), imp) = fmtExpW (g_, Whnf.whnf (u_, s), imp)
        and fmtSpine =
          function 
                   | (g_, (nil_, _), _) -> nl_unind ()
                   | (g_, (I.SClo (s_, s'), s), args)
                       -> fmtSpine (g_, (s_, I.comp (s', s)), args)
                   | (g_, (I.App (u_, s_), s), args)
                       -> let out = ref ((nl ()) ^ (fmtExp (g_, (u_, s), 0)))
                            in let _ = begin
                                 if (args = 1) && ((spineLength s_) > 0) then
                                 out :=
                                   (((! out) ^ (nl_unind ())) ^ "</om:OMA>")
                                 else () end
                                 in (! out) ^
                                      (fmtSpine (g_, (s_, s), args - 1))
        and fmtExpTop (g_, (u_, s), imp) =
          sexp
          [(Str "<om:OMOBJ>"); nl_ind (); fmtExp (g_, (u_, s), imp);
           nl_unind (); (Str "</om:OMOBJ>")]
        and fmtBinder (binder, varname, varid, Typ_, Body_) =
          (((((((((((((((((((((((("<om:OMBIND>" ^ (nl_ind ())) ^
                                   "<om:OMS cd=\"twelf\" name=\"")
                                  ^ binder)
                                 ^ "\"/>")
                                ^ (nl ()))
                               ^ "<om:OMBVAR><om:OMATTR>")
                              ^ (nl_ind ()))
                             ^
                             (begin
                              if ! namesafe then
                              ((((("<om:OMATP><om:OMS cd=\"omdoc\" name=\"notation\"/><om:OMFOREIGN encoding=\"application/omdoc+xml\">"
                                     ^ "<presentation for=\"#")
                                    ^ varid)
                                   ^ "\"><use format=\"twelf\">")
                                  ^ varname)
                                 ^ "</use></presentation>")
                                ^ "</om:OMFOREIGN></om:OMATP>"
                              else "" end))
                            ^ "<om:OMATP>")
                           ^ (nl ()))
                          ^ "<om:OMS cd=\"twelf\" name=\"oftype\"/>")
                         ^ (nl ()))
                        ^ Typ_)
                       ^ (nl ()))
                      ^ "</om:OMATP>")
                     ^ (nl ()))
                    ^ "<om:OMV name=\"")
                   ^ varid)
                  ^ "\"/>")
                 ^ (nl_unind ()))
                ^ "</om:OMATTR></om:OMBVAR>")
               ^ (nl ()))
              ^ Body_)
             ^ (nl_unind ()))
            ^ "</om:OMBIND>"
        and fmtSymbol (name, v_, imp) =
          ((((((((("<symbol name=\"" ^ name) ^ "\">") ^ (nl_ind ())) ^
                  "<type system=\"twelf\">")
                 ^ (nl_ind ()))
                ^ (fmtExpTop (I.null_, (v_, I.id), imp)))
               ^ (nl_unind ()))
              ^ "</type>")
             ^ (nl_unind ()))
            ^ "</symbol>"
        and fmtDefinition (name, u_, imp) =
          ((((((("<definition xml:id=\"" ^ name) ^ ".def\" for=\"#") ^ name)
                ^ "\">")
               ^ (nl_ind ()))
              ^ (fmtExpTop (I.null_, (u_, I.id), imp)))
             ^ (nl_unind ()))
            ^ "</definition>"
        and fmtPresentation cid =
          let imp = I.conDecImp (I.sgnLookup cid)
            in let fixity = Names.getFixity cid
                 in let fixString =
                      (" fixity=\"" ^
                         (begin
                          match fixity
                          with 
                               | nonfix_ -> "prefix"
                               | Names.Fixity.Infix (prec, assoc)
                                   -> begin
                                      match assoc
                                      with 
                                           | left_ -> "infixl"
                                           | right_ -> "infixr"
                                           | none_ -> "infix"
                                      end
                               | Names.Fixity.Prefix prec -> "prefix"
                               | Names.Fixity.Postfix prec -> "postfix"
                          end))
                        ^ "\""
                      in let precString =
                           (" precedence=\"" ^
                              (Int.toString
                               (Names.Fixity.precToIntAsc fixity)))
                             ^ "\""
                           in let bracString =
                                " bracket-style=\"lisp\" lbrack=\"(\" rbrack=\")\""
                                in let sepString = " separator=\" \""
                                     in let implicitString =
                                          (" implicit=\"" ^
                                             (Int.toString imp))
                                            ^ "\""
                                          in let useString1 =
                                               "<use format=\"twelf\""
                                               in let useString2 =
                                                    (">" ^
                                                       (escape
                                                        (I.conDecName
                                                         (I.sgnLookup cid))))
                                                      ^ "</use>"
                                                    in let presString1 =
                                                         ("<presentation for=\"#"
                                                            ^ (name_ cid))
                                                           ^ "\""
                                                         in let presString2 =
                                                              "</presentation>"
                                                              in (((((((((((((((((((presString1
                                                                    ^ ">") ^
                                                                    (nl_ind
                                                                    ())) ^
                                                                    useString1)
                                                                    ^
                                                                    useString2)
                                                                    ^
                                                                    (nl_unind
                                                                    ())) ^
                                                                    presString2)
                                                                    ^ (nl ()))
                                                                    ^
                                                                    presString1)
                                                                    ^
                                                                    " role=\"applied\"")
                                                                    ^
                                                                    fixString)
                                                                    ^
                                                                    precString)
                                                                    ^
                                                                    bracString)
                                                                    ^
                                                                    sepString)
                                                                    ^
                                                                    implicitString)
                                                                    ^ ">") ^
                                                                    (nl_ind
                                                                    ())) ^
                                                                    useString1)
                                                                    ^
                                                                    useString2)
                                                                    ^
                                                                    (nl_unind
                                                                    ()))
                                                                   ^
                                                                   presString2
        and fmtFixity cid =
          let fixity = Names.getFixity cid
            in let name = I.conDecName (I.sgnLookup cid) in begin
                 if fixity = Names.Fixity.nonfix_ then "" else
                 (((((((((((nl ()) ^ "<private for=\"#") ^ (name_ cid)) ^
                           "\">")
                          ^ (nl_ind ()))
                         ^ "<data format=\"twelf\"><![CDATA[")
                        ^ (Names.Fixity.toString fixity))
                       ^ " ")
                      ^ name)
                     ^ ".]]></data>")
                    ^ (nl_unind ()))
                   ^ "</private>"
                 end;;
        let rec fmtConDec =
          function 
                   | (cid, I.ConDec (name, parent, imp, _, v_, l_))
                       -> let _ = Names.varReset IntSyn.null_
                            in let name = name_ cid
                                 in fmtSymbol (name, v_, imp)
                   | (_, I.SkoDec (name, parent, imp, v_, l_))
                       -> (Str
                           (("<!-- Skipping Skolem constant " ^ name) ^ "-->"))
                   | (cid, I.ConDef (name, parent, imp, u_, v_, l_, _))
                       -> let _ = Names.varReset IntSyn.null_
                            in let name = name_ cid
                                 in ((fmtSymbol (name, v_, imp)) ^ (nl ())) ^
                                      (fmtDefinition (name, u_, imp))
                   | (cid, I.AbbrevDef (name, parent, imp, u_, v_, l_))
                       -> let _ = Names.varReset IntSyn.null_
                            in let name = name_ cid
                                 in ((fmtSymbol (name, v_, imp)) ^ (nl ())) ^
                                      (fmtDefinition (name, u_, imp))
                   | (_, I.BlockDec (name, _, _, _))
                       -> (Str
                           (("<!-- Skipping Skolem constant " ^ name) ^ "-->"));;
        end;;
    (* Shorthands *);;
    (* The Formatter isn't really helpful for OMDoc output. So the basic functions are reimplemented here.
     indent : current indentatioin width
     nl_ind()() : newline and indent
     nl_unind()() : newline and unindent
     nl() : newline (with current indentation) *);;
    (* If namesafe is true during printing, the output is guaranteed to be namesafe (no duplicate names).
    But it doesn't look good. If the user knows that are no overloaded constants, namesafe can be set to false. *);;
    (* XML start characters: "":"" | ""_"" | [A-Z] | [a-z], further characters: ""-"" | ""."" | [0-9] *);;
    (* x must be the number of the varialbe in left ro right order in the context *);;
    (* Some original Formatter functions replaced with trivial functions. *);;
    (* val Str  = F.String
  fun Str0 (s, n) = F.String0 n s
  fun Integer (n) = (""\"""" ^ Int.toString n ^ ""\"""") *);;
    (* fun sexp (fmts) = F.Hbox [F.HVbox fmts] *);;
    (* This is probably defined elsewhere, too. It's needed to check how many arguments there will be in an om:OMA element *);;
    (* fmtCon (c) = ""c"" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding ""`"" (backquote) character
  *);;
    (* FIX -cs Fri Jan 28 17:45:35 2005*);;
    (* I.Skonst, I.FVar cases should be impossible *);;
    (* fmtUni (L) = ""L"" *);;
    (* fmtExpW (G, (U, s)) = fmt

     format the expression U[s].

     Invariants:
       G is a ""printing context"" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *);;
    (* if Pi is dependent but anonymous, invent name here *);;
    (* could sometimes be EName *);;
    (* temporary indentation *);;
    (* no arguments *);;
    (* an application *);;
    (* If there are more than two explicit arguments to an infix operator,
                   the implict and the first two explicit arguments have to be wrapped in their own om:OMA element.
                   In this case, the output will not be in normal form. *);;
    (* print constant and arguments,
           args is passed to fmtSpine so that fmtSpine can insert a closing tag after args arguments, 0 means no effect *);;
    (* temporary indentation *);;
    (* FIX -cs Fri Jan 28 17:45:43 2005 *);;
    (* I.EClo, I.Redex, I.EVar not possible *);;
    (* fmtSpine (G, (S, s), args) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
     args is the number of arguments after which </om:OMA> must be inserted, no effect if negative
  *);;
    (* print first argument, 0 is dummy value *);;
    (* close application if args reaches 0 *);;
    (* print remaining arguments *);;
    (* top-level and shared OMDoc output, used in fmtConDec *);;
    (* In the presentation information for variables can be omitted since it's their name anyway *);;
    (* case identified by @precedence = Names.Fixity.minPrefInt *);;
    (* fixity string attached to omdoc file in private element (no escaping, fixity string cannot contain ]]>) *);;
    (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *);;
    (* In the functions below, G must be a ""printing context"", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *);;
    let rec formatExp (g_, u_, imp) = fmtExp (g_, (u_, I.id), imp);;
    (*  fun formatSpine (G, S) = sexp (fmtSpine (G, (S, I.id))) *);;
    let rec formatConDec Condec_ = fmtConDec Condec_;;
    (* fun expToString (G, U) = F.makestring_fmt (formatExp (G, U, 0)) *);;
    let rec conDecToString Condec_ = formatConDec Condec_;;
    let rec fmtConst cid =
      (((formatConDec (cid, IntSyn.sgnLookup cid)) ^ "\n") ^
         (fmtPresentation cid))
        ^ (fmtFixity cid);;
    let rec printConst cid = begin
                               namesafe := false;fmtConst cid
                               end;;
    let rec printSgn filename ns =
      let _ = namesafe := ns
        in let _ = ind_reset ()
             in let file = TextIO.openOut filename
                  in let oMDocPrefix_ =
                       ((((((("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                                ^
                                "<!DOCTYPE omdoc PUBLIC \"-//OMDoc//DTD OMDoc V1.2//EN\" ")
                               ^ "\"../../dtd/omdoc.dtd\">\n")
                              ^ "<omdoc xml:id=\"")
                             ^ filename)
                            ^ "\" ")
                           ^ "xmlns=\"http://www.mathweb.org/omdoc\" ")
                          ^ "xmlns:om=\"http://www.openmath.org/OpenMath\" ")
                         ^ "version=\"1.2\">\n\n"
                       (* ""\""https://svn.mathweb.org/repos/mathweb.org/branches/omdoc-1.2/dtd/omdoc.dtd\"">\n"" ^ *)
                       in let _ =
                            TextIO.output
                            (file,
                             oMDocPrefix_ ^ "<theory xml:id=\"global\">\n\n")
                            in let _ =
                                 IntSyn.sgnApp
                                 (function 
                                           | cid
                                               -> begin
                                                    TextIO.output
                                                    (file, fmtConst cid);
                                                    TextIO.output
                                                    (file, "\n\n")
                                                    end)
                                 in let _ =
                                      TextIO.output
                                      (file, "</theory>\n\n</omdoc>")
                                      in let _ = TextIO.closeOut file in ();;
    end;;
(* local ... *);;
(* functor PrintXml *);;