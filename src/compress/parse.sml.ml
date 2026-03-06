open! Basis;;
module Parse = struct
                 open Parsing;;
                 open Tok;;
                 let _bq = literal;;
                 type mode = | MMINUS_ 
                             | MPLUS_ 
                             | MOMIT_ ;;
                 type term =
                   | Id of string 
                   | App of term * term 
                   | Lam of (string * term option) * term 
                   | Type 
                   | Pi of mode * (string * term option) * term 
                   | Arrow of term * term 
                   | PlusArrow of term * term 
                   | Ascribe of term * term 
                   | Omit ;;
                 let rec piMinus_ ((s, to_), t) = (Pi (MMINUS_, (s, to_), t));;
                 let rec piPlus_ ((s, to_), t) = (Pi (MPLUS_, (s, to_), t));;
                 let rec piOmit_ ((s, to_), t) = (Pi (MOMIT_, (s, to_), t));;
                 let rec modeToString =
                   function 
                            | MMINUS_ -> ""
                            | MPLUS_ -> "+ "
                            | MOMIT_ -> "* ";;
                 let rec termToString =
                   function 
                            | Id s -> s
                            | App (t, u)
                                -> ((("(" ^ (termToString t)) ^ " ") ^
                                      (termToString u))
                                     ^ ")"
                            | Lam (vd, t)
                                -> (("[" ^ (vardecToString vd)) ^ "] ") ^
                                     (termToString t)
                            | Pi (m, vd, t)
                                -> ((("{" ^ (modeToString m)) ^
                                       (vardecToString vd))
                                      ^ "} ")
                                     ^ (termToString t)
                            | Type -> "type"
                            | Arrow (t, u)
                                -> ((("(" ^ (termToString t)) ^ " -> ") ^
                                      (termToString u))
                                     ^ ")"
                            | PlusArrow (t, u)
                                -> ((("(" ^ (termToString t)) ^ " +> ") ^
                                      (termToString u))
                                     ^ ")"
                            | Ascribe (t, u)
                                -> ((("(" ^ (termToString t)) ^ " : ") ^
                                      (termToString u))
                                     ^ ")"
                            | Omit -> "*"
                 and vardecToString =
                   function 
                            | (v, Some t) -> (v ^ ":") ^ (termToString t)
                            | (v, None) -> v;;
                 let id = maybe (function 
                                          | Id s -> (Some s)
                                          | _ -> None);;
                 let rec swap (x, y) = (y, x);;
                 let rec vardec () =
                   id
                   (fun (x__op, y__op) -> x__op << y__op)
                   _bq
                   colon_
                   (fun (x__op, y__op) -> x__op && y__op)
                   ((( $ ) (term, wth, Some)))
                   (fun (x__op, y__op) -> x__op || y__op)
                   id
                   wth
                   (function 
                             | s -> (s, None))
                 and term () =
                   parsefixityadj
                   (alt
                    [id wth (fun x -> atm_ (Id x));
                     _bq
                     lparen_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     rparen_
                     wth
                     atm_;
                     _bq
                     lparen_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     colon_
                     (fun (x__op, y__op) -> x__op && y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     rparen_
                     wth
                     (fun x -> atm_ (Ascribe x));
                     _bq
                     lbracket_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     vardec
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     rbracket_
                     (fun (x__op, y__op) -> x__op && y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     wth
                     (fun x -> atm_ (Lam x));
                     _bq
                     lbrace_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     _bq
                     star_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     vardec
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     rbrace_
                     (fun (x__op, y__op) -> x__op && y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     wth
                     (fun x -> atm_ (piOmit_ x));
                     _bq
                     lbrace_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     _bq
                     plus_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     vardec
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     rbrace_
                     (fun (x__op, y__op) -> x__op && y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     wth
                     (fun x -> atm_ (piPlus_ x));
                     _bq
                     lbrace_
                     (fun (x__op, y__op) -> x__op >> y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     vardec
                     (fun (x__op, y__op) -> x__op << y__op)
                     _bq
                     rbrace_
                     (fun (x__op, y__op) -> x__op && y__op)
                     (fun (x__op, y__op) -> x__op $ y__op)
                     term
                     wth
                     (fun x -> atm_ (piMinus_ x));
                     _bq type_ return (atm_ Type);
                     _bq arrow_ return opr_ (infix_ (right_, 5, Arrow));
                     _bq
                     plusarrow_
                     return
                     opr_
                     (infix_ (right_, 5, PlusArrow));
                     _bq
                     backarrow_
                     return
                     opr_
                     (infix_ (left_, 5, fun x -> Arrow (swap x)));
                     _bq star_ return (atm_ Omit)])
                   left_
                   App;;
                 let condec =
                   opt
                   (_bq minus_)
                   wth
                   (fun x -> not (Option.isSome x))
                   (fun (x__op, y__op) -> x__op && y__op)
                   id
                   (fun (x__op, y__op) -> x__op << y__op)
                   _bq
                   colon_
                   (fun (x__op, y__op) -> x__op && y__op)
                   (fun (x__op, y__op) -> x__op $ y__op)
                   term
                   (fun (x__op, y__op) -> x__op << y__op)
                   _bq
                   dot_;;
                 let rec parseof x =
                   Stream.toList
                   (Parsing.transform
                    ((fun (x__op, y__op) -> x__op $ y__op) term)
                    (Parsing.transform
                     (!! tok)
                     (Pos.markstream (StreamUtil.stostream (x ^ "\n%.")))));;
                 end;;