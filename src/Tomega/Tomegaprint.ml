open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Formatter.Formatter_
open! Names.Names_
open! Print.Print_

(* # 1 "src/tomega/Tomegaprint.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
include TOMEGAPRINT

(*  val lemmaDecToString : FunSyn.LemmaDec -> string *)
(* signature TOMEGAPRINT *)

(* # 1 "src/tomega/Tomegaprint.fun.ml" *)
open! Basis

(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module TomegaPrint (TomegaPrint__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  (*   structure Normalize : NORMALIZE *)
  (*! sharing Normalize.IntSyn = IntSyn' !*)
  (*! sharing Normalize.Tomega = Tomega' !*)
  module Formatter : FORMATTER
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Print : PRINT with module Formatter = Formatter
end) : TOMEGAPRINT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module Formatter = TomegaPrint__0.Formatter

  exception Error = Error

  (* is just here because we don't have a
     module yet for Names. move later
     --cs Tue Apr 27 12:04:45 2004 *)
  module Fmt = TomegaPrint__0.Formatter
  module P = TomegaPrint__0.Print

  open! struct
    module I = IntSyn
    module T = Tomega
    module Names = TomegaPrint__0.Names

    let evarList : T.prg list ref = ref []
    let evarReset () = evarList := []

    let evarName n =
      let rec evarName' = function
        | [] -> raise (Error "not found")
        | (T.EVar (_, _, _, _, _, (I.EVar (_, g, r, _) as x)) as y) :: l ->
            begin if Names.evarName g x = n then y else evarName' l
            end
      in
      evarName' !evarList

    let nameEVar (T.EVar (_, _, _, _, _, (I.EVar (_, g, r, _) as x))) =
      Names.evarName g x

    let rec formatCtxBlock (g, a) = match a with
      | (I.Null, s) -> (g, s, [])
      | (I.Decl (I.Null, d), s) ->
          let d' = I.decSub d s in
          let fmt = P.formatDec g d' in
          (I.Decl (g, d'), I.dot1 s, [ fmt ])
      | (I.Decl (g', d), s) ->
          let g'', s'', fmts = formatCtxBlock (g, (g', s)) in
          let d'' = I.decSub d s'' in
          let fmt = P.formatDec g'' d'' in
          ( I.Decl (g'', d''),
            I.dot1 s'',
            fmts @ [ Fmt.string ","; Fmt.break_; fmt ] )

    let constName c = I.conDecName (I.sgnLookup c)

    let rec formatWorld = function
      | [] -> []
      | c :: [] -> [ Fmt.string (constName c) ]
      | c :: cids ->
          [ Fmt.string (constName c); Fmt.string ","; Fmt.break_ ]
          @ formatWorld cids

    let rec formatFor' (psi, a) = match a with
      | T.All ((d, explicit), f) ->
          begin match d with
          | T.UDec d ->
              let g = T.coerceCtx psi in
              let d' = Names.decName g d in
              [
                Fmt.string "all {";
                P.formatDec g d';
                Fmt.string "}";
                Fmt.break_;
              ]
              @ formatFor' (I.Decl (psi, T.UDec d'), f)
          end
      | T.All ((d, implicit), f) ->
          begin match d with
          | T.UDec d ->
              let g = T.coerceCtx psi in
              let d' = Names.decName g d in
              [
                Fmt.string "all^ {";
                P.formatDec g d';
                Fmt.string "}";
                Fmt.break_;
              ]
              @ formatFor' (I.Decl (psi, T.UDec d'), f)
          end
      | T.Ex ((d, explicit), f) ->
          let g = T.coerceCtx psi in
          let d' = Names.decName g d in
          [
            Fmt.string "exists {";
            P.formatDec g d';
            Fmt.string "}";
            Fmt.break_;
          ]
          @ formatFor' (I.Decl (psi, T.UDec d'), f)
      | T.Ex ((d, implicit), f) ->
          let g = T.coerceCtx psi in
          let d' = Names.decName g d in
          [
            Fmt.string "exists^ {";
            P.formatDec g d';
            Fmt.string "}";
            Fmt.break_;
          ]
          @ formatFor' (I.Decl (psi, T.UDec d'), f)
      | T.And (f1, f2) ->
          [
            Fmt.string "(";
            Fmt.hVbox (formatFor' (psi, f1));
            Fmt.string ")";
            Fmt.break_;
            Fmt.string "/\\";
            Fmt.space;
            Fmt.string "(";
            Fmt.hVbox (formatFor' (psi, f2));
            Fmt.string ")";
          ]
      | T.True -> [ Fmt.string "true" ]
      | T.World (T.Worlds l, f) ->
          [
            Fmt.string "world (";
            Fmt.hVbox (formatWorld l);
            Fmt.string ")";
            Fmt.break_;
          ]
          @ formatFor' (psi, f)

    let formatFor g f = Fmt.hVbox (formatFor' (g, T.forSub f T.id))
    let forToString psi f = Fmt.makestring_fmt (formatFor psi f)

    let decName a1 b1 = match a1, b1 with
      | g, T.UDec d -> T.UDec (Names.decName g d)
      | g, T.PDec (None, f, tc1, tc2) -> T.PDec (Some "xx", f, tc1, tc2)
      | g, d -> d

    let psiName (psi1, s, psi2, l) =
      let nameDec (a, name) = match a with
        | (I.Dec (Some _, _) as d) -> d
        | I.Dec (None, v) -> I.Dec (Some name, v)
      in
      let rec namePsi (a, n, name) = match a, n with
        | I.Decl (psi, T.UDec d), 1 ->
            I.Decl (psi, T.UDec (nameDec (d, name)))
        | I.Decl (psi, (T.UDec d as ld)), n ->
            I.Decl (namePsi (psi, n - 1, name), ld)
      and nameG (psi, a, n, name, k) = match a, n with
        | I.Null, n -> (k n, I.Null)
        | I.Decl (g, d), 1 ->
            (psi, I.Decl (g, nameDec (d, name)))
        | I.Decl (g, d), n ->
            let psi', g' = nameG (psi, g, n - 1, name, k) in
            (psi', I.Decl (g', d))
      in
      let rec ignore = function
        | s, 0 -> s
        | T.Dot (_, s), k -> ignore (s, k - 1)
        | T.Shift n, k -> ignore (T.Dot (T.Idx (n + 1), T.Shift (n + 1)), k - 1)
      in
      let rec copyNames arg__1 arg__2 =
        begin match (arg__1, arg__2) with
        | (T.Shift n, (I.Decl _ as g)), psi1 ->
            copyNames (T.Dot (T.Idx (n + 1), T.Shift (n + 1)), g) psi1
        | (T.Dot (T.Exp _, s), I.Decl (g, _)), psi1 -> copyNames (s, g) psi1
        | (T.Dot (T.Idx k, s), I.Decl (g, T.UDec (I.Dec (None, _)))), psi1 ->
            copyNames (s, g) psi1
        | (T.Dot (T.Idx k, s), I.Decl (g, T.UDec (I.Dec (Some name, _)))), psi1
          ->
            let psi1' = namePsi (psi1, k, name) in
            copyNames (s, g) psi1'
        | (T.Dot (T.Prg k, s), I.Decl (g, T.PDec (None, _, _, _))), psi1 ->
            copyNames (s, g) psi1
        | (T.Dot (T.Prg k, s), I.Decl (g, T.PDec (Some name, _, _, _))), psi1
          ->
            copyNames (s, g) psi1
        | (T.Shift _, I.Null), psi1 -> psi1
        end
      in
      let rec psiName' = function
        | I.Null -> I.Null
        | I.Decl (psi, d) ->
            let psi' = psiName' psi in
            I.Decl (psi', decName (T.coerceCtx psi') d)
      in
      psiName' psi1

    let rec fmtSpine arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | callname, (psi, T.Nil) -> []
      | callname, (psi, T.AppExp (u, s)) ->
          Fmt.hVbox (P.formatSpine (T.coerceCtx psi) (I.App (u, I.Nil)))
          :: fmtSpine' callname (psi, s)
      | callname, (psi, T.AppPrg (p, s)) ->
          formatPrg3 callname (psi, p) :: fmtSpine' callname (psi, s)
      end

    and fmtSpine' arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | callname, (psi, T.Nil) -> []
      | callname, (psi, s) -> Fmt.break_ :: fmtSpine callname (psi, s)
      end

    and argsToSpine (a, k, s_) = match a, k with
      | s, 0 -> s_
      | T.Shift n, k ->
          argsToSpine (T.Dot (T.Idx (n + 1), T.Shift (n + 1)), k, s_)
      | T.Dot (T.Idx n, s), k ->
          argsToSpine (s, k - 1, T.AppExp (I.Root (I.BVar n, I.Nil), s_))
      | T.Dot (T.Exp u, s), k -> argsToSpine (s, k - 1, T.AppExp (u, s_))
      | T.Dot (T.Prg p, s), k -> argsToSpine (s, k - 1, T.AppPrg (p, s_))

    and formatTuple (psi, p) =
      let rec formatTuple' = function
        | T.Unit -> []
        | T.PairExp (m, T.Unit) -> [ P.formatExp (T.coerceCtx psi) m ]
        | T.PairExp (m, p') ->
            P.formatExp (T.coerceCtx psi) m
            :: Fmt.string "," :: Fmt.break_ :: formatTuple' p'
      in
      begin match p with
      | T.PairExp (_, T.Unit) -> Fmt.hbox (formatTuple' p)
      | _ ->
          Fmt.hVbox0 1 1 1
            ((Fmt.string "(" :: formatTuple' p) @ [ Fmt.string ")" ])
      end

    and formatRedex arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | callname, (psi, T.Var k, s) ->
          let (T.PDec (Some name, _, _, _)) = I.ctxLookup psi k in
          let fspine = fmtSpine callname (psi, s) in
          Fmt.hbox
            [ Fmt.space; Fmt.hVbox (Fmt.string name :: Fmt.break_ :: fspine) ]
      | callname, (psi, T.Const l, s) ->
          let (T.ValDec (name, _, _)) = T.lemmaLookup l in
          let fspine = fmtSpine callname (psi, s) in
          Fmt.hbox
            [ Fmt.space; Fmt.hVbox (Fmt.string name :: Fmt.break_ :: fspine) ]
      | callname, (psi, T.Redex (T.Const l, _), s) ->
          let name = callname l in
          let fspine = fmtSpine callname (psi, s) in
          Fmt.hbox
            [ Fmt.space; Fmt.hVbox (Fmt.string name :: Fmt.break_ :: fspine) ]
      end

    and formatCase callname (max, psi', s, psi) =
      let s_ = argsToSpine (s, I.ctxLength psi - max, T.Nil) in
      let fspine = fmtSpine callname (psi', s_) in
      Fmt.hbox [ Fmt.hVbox fspine ]

    and formatCases (max, psi, a, callname) = match a with
      | [] -> []
      | (psi', s, p) :: [] ->
          let psi'' = psiName (psi', s, psi, 0) in
          ignore (Names.varReset I.Null);
          [
            Fmt.hVbox0 1 5 1
              [
                formatCase callname (max, psi'', s, psi);
                Fmt.space;
                Fmt.string "=";
                Fmt.break_;
                formatPrg3 callname (psi'', p);
              ];
            Fmt.break_;
          ]
      | (psi', s, p) :: o ->
          let psi'' = psiName (psi', s, psi, 0) in
          ignore (Names.varReset I.Null);
          formatCases (max, psi, o, callname)
          @ [
              Fmt.hVbox0 1 5 1
                [
                  Fmt.string "|";
                  Fmt.space;
                  formatCase callname (max, psi'', s, psi);
                  Fmt.space;
                  Fmt.string "=";
                  Fmt.break_;
                  formatPrg3 callname (psi'', p);
                ];
              Fmt.break_;
            ]

    and formatPrg3 arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | callname, (psi, T.Unit) -> Fmt.string "<>"
      | callname, (psi, T.PairExp (u, p)) ->
          Fmt.hVbox
            [
              Fmt.string "<";
              P.formatExp (T.coerceCtx psi) u;
              Fmt.string ",";
              Fmt.break_;
              formatPrg3 callname (psi, p);
              Fmt.string ">";
            ]
      | callname, (psi, (T.Let _ as p)) -> formatLet callname (psi, p, [])
      | callname, (psi, (T.LetPairExp (d1, d2, p1, p2) as p)) ->
          formatLet callname (psi, p, [])
      | callname, (psi, (T.LetUnit (p1, p2) as p)) ->
          formatLet callname (psi, p, [])
      | callname, (psi, (T.New (T.Lam (T.UDec (I.BDec (l, (c, s))), _)) as p))
        ->
          formatNew callname (psi, p, [])
      | callname, (psi, T.Redex (p, s)) -> formatRedex callname (psi, p, s)
      | callname, (psi, T.Lam ((T.UDec d' as d), p)) ->
          Fmt.hVbox
            [
              Fmt.string "lam";
              Fmt.space;
              Fmt.string "(";
              P.formatDec (T.coerceCtx psi) d';
              Fmt.string ")";
              Fmt.space;
              formatPrg3 callname (I.Decl (psi, d), p);
            ]
      | callname, (psi, T.Rec ((T.PDec (Some name, f, None, None) as d), p))
        ->
          Fmt.hVbox
            [
              Fmt.string "fix*";
              Fmt.space;
              Fmt.string "(";
              Fmt.string name;
              Fmt.string ":";
              formatFor psi f;
              Fmt.string ")";
              Fmt.space;
              formatPrg3 callname (I.Decl (psi, d), p);
            ]
      | ( callname,
          (psi, T.Rec ((T.PDec (Some name, f, Some tc1, Some tc2) as d), p))
        ) ->
          Fmt.hVbox
            [
              Fmt.string "fix";
              Fmt.space;
              Fmt.string "(";
              Fmt.string name;
              Fmt.string ":";
              formatFor psi f;
              Fmt.string ")";
              Fmt.space;
              formatPrg3 callname (I.Decl (psi, d), p);
            ]
      | callname, (psi, T.PClo (p, t)) ->
          Fmt.hVbox [ formatPrg3 callname (psi, p); Fmt.string "..." ]
      | callname, (psi, (T.EVar (_, { contents = Some p }, _, _, _, _) as x))
        ->
          formatPrg3 callname (psi, p)
      | callname, (psi, (T.EVar (_, { contents = None }, _, _, _, _) as x)) ->
          Fmt.string (nameEVar x)
      | callname, (psi, T.Case (T.Cases cs)) ->
          Fmt.hVbox
            (Fmt.string "case" :: Fmt.break_
             :: formatCases (1, psi, cs, callname)
            @ [ Fmt.string "." ])
      | callname, (psi, T.Var n) ->
          let (T.PDec (Some n, _, _, _)) = I.ctxLookup psi n in
          Fmt.string n
      | callname, _ -> Fmt.string "missing case"
      end

    and formatNew arg__11 arg__12 =
      begin match (arg__11, arg__12) with
      | ( callname,
          (psi, T.New (T.Lam (T.UDec (I.BDec (l, (c, s)) as d), p)), fmts) )
        ->
          let g = T.coerceCtx psi in
          let d' = Names.decName g d in
          formatNew callname
            ( I.Decl (psi, T.UDec d'),
              p,
              Fmt.break_ :: Fmt.hVbox [ P.formatDec g d' ] :: fmts )
      | callname, (psi, p, fmts) ->
          Fmt.vbox0 0 1
            [
              Fmt.string "new";
              Fmt.vbox0 0 1 fmts;
              Fmt.break_;
              Fmt.string "in";
              Fmt.break_;
              Fmt.spaces 2;
              formatPrg3 callname (psi, p);
              Fmt.break_;
              Fmt.string "end";
            ]
      end

    and formatLet arg__13 arg__14 =
      begin match (arg__13, arg__14) with
      | ( callname,
          ( psi,
            T.Let
              (d, p1, T.Case (T.Cases ((psi1, s1, (T.Let _ as p2)) :: []))),
            fmts ) ) ->
          let psi1' = psiName (psi1, s1, psi, 1) in
          let f1 = Fmt.hVbox [ formatPrg3 callname (psi, p1) ] in
          let s = argsToSpine (s1, 1, T.Nil) in
          let fspine = fmtSpine callname (psi1, s) in
          let fpattern = Fmt.hVbox [ Fmt.hbox fspine ] in
          let fbody = Fmt.hVbox [ f1 ] in
          let fmt =
            Fmt.hVbox
              [
                Fmt.hVbox
                  [
                    Fmt.string "val";
                    Fmt.space;
                    fpattern;
                    Fmt.space;
                    Fmt.string "=";
                  ];
                Fmt.break_;
                fbody;
              ]
          in
          formatLet callname (psi1', p2, fmts @ [ Fmt.break_; fmt ])
      | ( callname,
          (psi, T.Let (d, p1, T.Case (T.Cases ((psi1, s1, p2) :: []))), fmts)
        ) ->
          let psi1' = psiName (psi1, s1, psi, 1) in
          let f1 = Fmt.hVbox [ formatPrg3 callname (psi, p1) ] in
          let s = argsToSpine (s1, 1, T.Nil) in
          let fspine = fmtSpine callname (psi1, s) in
          let fpattern = Fmt.hVbox [ Fmt.hbox fspine ] in
          let fbody = Fmt.hVbox [ f1 ] in
          let fmt =
            Fmt.hVbox
              [
                Fmt.hVbox
                  [
                    Fmt.string "val";
                    Fmt.space;
                    fpattern;
                    Fmt.space;
                    Fmt.string "=";
                  ];
                Fmt.break_;
                fbody;
              ]
          in
          Fmt.vbox0 0 1
            [
              Fmt.string "let";
              Fmt.vbox0 2 1 (fmts @ [ Fmt.break_; fmt ]);
              Fmt.break_;
              Fmt.string "in";
              Fmt.break_;
              Fmt.spaces 2;
              formatPrg3 callname (psi1', p2);
              Fmt.break_;
              Fmt.string "end";
            ]
      | callname, (psi, T.Let (d, p1, T.Case (T.Cases l)), []) ->
          let rec fmtCaseRest = function
            | [] -> []
            | (psi1, s1, p2) :: l ->
                let psi1' = psiName (psi1, s1, psi, 1) in
                let s = argsToSpine (s1, 1, T.Nil) in
                let fspine = fmtSpine callname (psi1, s) in
                let fpattern = Fmt.hVbox [ Fmt.hbox fspine ] in
                [
                  Fmt.hVbox
                    [
                      Fmt.space;
                      Fmt.string "|";
                      Fmt.space;
                      fpattern;
                      Fmt.space;
                      Fmt.string "-->";
                    ];
                  Fmt.spaces 2;
                  Fmt.vbox0 0 1 [ formatPrg3 callname (psi1', p2) ];
                  Fmt.break_;
                ]
                @ fmtCaseRest l
          in
          let fmtCase ((psi1, s1, p2) :: l) =
            let psi1' = psiName (psi1, s1, psi, 1) in
            let s = argsToSpine (s1, 1, T.Nil) in
            let fspine = fmtSpine callname (psi1, s) in
            let fpattern = Fmt.hVbox [ Fmt.hbox fspine ] in
            Fmt.vbox0 0 1
              ([
                 Fmt.hVbox
                   [
                     Fmt.string "of";
                     Fmt.space;
                     fpattern;
                     Fmt.space;
                     Fmt.string "-->";
                   ];
                 Fmt.spaces 2;
                 Fmt.vbox0 0 1 [ formatPrg3 callname (psi1', p2) ];
                 Fmt.break_;
               ]
              @ fmtCaseRest l)
          in
          let f1 = Fmt.hVbox [ formatPrg3 callname (psi, p1) ] in
          let fbody = Fmt.hVbox [ f1 ] in
          let fmt = fmtCase l in
          Fmt.vbox0 0 1
            [
              Fmt.string "case (";
              fbody;
              Fmt.space;
              Fmt.string ")";
              Fmt.break_;
              fmt;
            ]
      | callname, (psi, (T.Let (d, p1, T.Case (T.Cases l)) as r), fmts) ->
          Fmt.vbox0 0 1
            [
              Fmt.string "let";
              Fmt.vbox0 0 1 (fmts @ [ Fmt.break_ ]);
              Fmt.break_;
              Fmt.string "in";
              Fmt.break_;
              Fmt.spaces 2;
              formatLet callname (psi, r, []);
              Fmt.break_;
              Fmt.string "end";
            ]
      | ( callname,
          ( psi,
            (T.Let ((T.PDec (Some name, f, _, _) as d), p1, p2) as r),
            fmts ) ) ->
          Fmt.vbox0 0 1
            [
              Fmt.string "let";
              Fmt.break_;
              Fmt.vbox0 0 1
                [
                  Fmt.string name;
                  Fmt.space;
                  Fmt.string "=";
                  formatPrg3 callname (psi, p1);
                ];
              Fmt.break_;
              Fmt.string "in";
              Fmt.break_;
              Fmt.spaces 2;
              formatPrg3 callname (I.Decl (psi, d), p2);
              Fmt.break_;
              Fmt.string "end";
            ]
      | ( callname,
          ( psi,
            (T.LetPairExp
               ( (I.Dec (Some n1, _) as d1),
                 (T.PDec (Some n2, f, _, _) as d2),
                 p1,
                 p2 ) as r),
            fmts ) ) ->
          Fmt.vbox0 0 1
            [
              Fmt.string "let";
              Fmt.break_;
              Fmt.spaces 2;
              Fmt.vbox0 0 1
                [
                  Fmt.string "(";
                  Fmt.string n1;
                  Fmt.string ",";
                  Fmt.space;
                  Fmt.string n2;
                  Fmt.string ")";
                  Fmt.space;
                  Fmt.string "=";
                  Fmt.space;
                  formatPrg3 callname (psi, p1);
                ];
              Fmt.break_;
              Fmt.string "in";
              Fmt.break_;
              Fmt.spaces 2;
              formatPrg3 callname (I.Decl (I.Decl (psi, T.UDec d1), d2), p2);
              Fmt.break_;
              Fmt.string "end";
            ]
      | callname, (psi, (T.LetUnit (p1, p2) as r), fmts) ->
          Fmt.vbox0 0 1
            [
              Fmt.string "let";
              Fmt.break_;
              Fmt.spaces 2;
              Fmt.vbox0 0 1
                [
                  Fmt.string "()";
                  Fmt.space;
                  Fmt.string "=";
                  Fmt.space;
                  formatPrg3 callname (psi, p1);
                ];
              Fmt.break_;
              Fmt.string "in";
              Fmt.break_;
              Fmt.spaces 2;
              formatPrg3 callname (psi, p2);
              Fmt.break_;
              Fmt.string "end";
            ]
      end

    and formatHead callname (name, (max, index), psi', s, psi) =
      let s_ = argsToSpine (s, I.ctxLength psi - max, T.Nil) in
      let fspine = fmtSpine callname (psi', s_) in
      Fmt.hbox
        [ Fmt.space; Fmt.hVbox (Fmt.string name :: Fmt.break_ :: fspine) ]

    let rec formatPrg2 (name, a, psi, b, callname) = match a, b with
      | (max, index), [] -> []
      | (max, index), (psi', s, p) :: [] ->
          let psi'' = psiName (psi', s, psi, 0) in
          let fhead =
            begin if index = I.ctxLength psi then "fun" else "and"
            end
          in
          [
            Fmt.hVbox0 1 5 1
              [
                Fmt.string fhead;
                formatHead callname (name, (max, index), psi'', s, psi);
                Fmt.space;
                Fmt.string "=";
                Fmt.break_;
                formatPrg3 callname (psi'', p);
              ];
            Fmt.break_;
          ]
      | (max, index), (psi', s, p) :: o ->
          let psi'' = psiName (psi', s, psi, 0) in
          formatPrg2 (name, (max, index), psi, o, callname)
          @ [
              Fmt.hVbox0 1 5 1
                [
                  Fmt.string "  |";
                  formatHead callname (name, (max, index), psi'', s, psi);
                  Fmt.space;
                  Fmt.string "=";
                  Fmt.break_;
                  formatPrg3 callname (psi'', p);
                ];
              Fmt.break_;
            ]

    let rec formatPrg11 (name, a, psi, b, callname) = match a, b with
      | (max, index), T.Lam (d, p) ->
          formatPrg11
            ( name,
              (max, index + 1),
              I.Decl (psi, decName (T.coerceCtx psi) d),
              p,
              callname )
      | (max, index), T.Case (T.Cases os) ->
          formatPrg2 (name, (max, index), psi, os, callname)

    let rec formatPrg1 (a, b, psi, p, callname) = match a, b, p with
      | name :: names, (max, index), T.PairPrg (p1, p2) ->
          formatPrg11 (name, (max, index), psi, p1, callname)
          @ formatPrg1 (names, (max, index - 1), psi, p2, callname)
      | name :: [], (max, index), p ->
          formatPrg11 (name, (max, index), psi, p, callname)

    let rec lookup (name :: names, proj :: projs) lemma =
      begin if lemma = proj then name else lookup (names, projs) lemma
      end

    let formatPrg0
        ((names, projs), T.Rec ((T.PDec (Some _, f, _, _) as d), p)) =
      let max = 1 in
      Fmt.vbox0 0 1
        (formatPrg1
           ( names,
             (max, max),
             I.Decl (I.Null, d),
             p,
             function lemma -> lookup (names, projs) lemma ))

    let formatFun a1 a2 b =
      let args = ((a1, a2), b) in
      Names.varReset I.Null;
      formatPrg0 args

    let funToString a1 a2 b = Fmt.makestring_fmt (formatFun a1 a2 b)

    let prgToString a b =
      let args = (a, b) in
      Fmt.makestring_fmt (formatPrg3 (function _ -> "?") args)

    let rec nameCtx = function
      | I.Null -> I.Null
      | I.Decl (psi, T.UDec d) ->
          I.Decl (nameCtx psi, T.UDec (Names.decName (T.coerceCtx psi) d))
      | I.Decl (psi, T.PDec (None, f, tc1, tc2)) ->
          let psi' = nameCtx psi in
          let (I.NDec x) = Names.decName (T.coerceCtx psi') (I.NDec None) in
          I.Decl (psi', T.PDec (x, f, tc1, tc2))
      | I.Decl (psi, (T.PDec (Some n, f, _, _) as d)) ->
          I.Decl (nameCtx psi, d)

    let flag = function None -> "" | Some _ -> "*"

    let rec formatCtx = function
      | I.Null -> []
      | I.Decl (I.Null, T.UDec d) ->
          begin if !Global.chatter >= 4 then
            [ Fmt.hVbox [ Fmt.break_; P.formatDec I.Null d ] ]
          else [ P.formatDec I.Null d ]
          end
      | I.Decl (I.Null, T.PDec (Some s, f, tc1, tc2)) ->
          begin if !Global.chatter >= 4 then
            [
              Fmt.hVbox
                [
                  Fmt.break_;
                  Fmt.string s;
                  Fmt.space;
                  Fmt.string ("::" ^ flag tc1);
                  Fmt.space;
                  formatFor I.Null f;
                ];
            ]
          else
            [
              Fmt.string s;
              Fmt.space;
              Fmt.string ("::" ^ flag tc1);
              Fmt.space;
              formatFor I.Null f;
            ]
          end
      | I.Decl (psi, T.UDec d) ->
          let g = T.coerceCtx psi in
          begin if !Global.chatter >= 4 then
            formatCtx psi
            @ [ Fmt.string ","; Fmt.break_; Fmt.break_ ]
            @ [ Fmt.hVbox [ Fmt.break_; P.formatDec g d ] ]
          else
            formatCtx psi
            @ [ Fmt.string ","; Fmt.break_ ]
            @ [ Fmt.break_; P.formatDec g d ]
          end
      | I.Decl (psi, T.PDec (Some s, f, tc1, tc2)) ->
          begin if !Global.chatter >= 4 then
            formatCtx psi
            @ [ Fmt.string ","; Fmt.break_; Fmt.break_ ]
            @ [
                Fmt.hVbox
                  [
                    Fmt.break_;
                    Fmt.string s;
                    Fmt.space;
                    Fmt.string ("::" ^ flag tc1);
                    Fmt.space;
                    formatFor psi f;
                  ];
              ]
          else
            formatCtx psi
            @ [ Fmt.string ","; Fmt.break_ ]
            @ [
                Fmt.break_;
                Fmt.string s;
                Fmt.space;
                Fmt.string ("::" ^ flag tc1);
                Fmt.space;
                formatFor psi f;
              ]
          end

    let ctxToString psi = Fmt.makestring_fmt (Fmt.hVbox (formatCtx psi))
  end

  (* Invariant:

       The proof term must satisfy the following conditions:
       * proof term must have the structure
           Rec.     Lam ... Lam Case
                And Lam ... Lam Case
                ...
                And Lam ... Lam Case
         and the body of every case must be of the form
           (Let Decs in Case ...
           or
           Inx ... Inx Unit) *
         where Decs are always of the form
           New ... New App .. App Split .. Split Empty
     *)
  (* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *)
  (* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *)
  (* formatPrg (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
  (*      fun nameLookup index = List.nth (names, index) *)
  (* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable Names.
        *)
  (* needs to be integrated with Names *)
  (*       numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        
        fun numberOfSplits Ds =
            let
              fun numberOfSplits' (T.Empty, n) = n
                | numberOfSplits' (T.New (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.App (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Lemma (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Split (_, Ds), n) = numberOfSplits' (Ds, n+1)
                | numberOfSplits' (T.Left (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Right (_, Ds), n) = numberOfSplits' (Ds, n)
            in
              numberOfSplits' (Ds, 0)
            end
*)
  (* psiName (Psi1, s, Psi2, l) = Psi1'

           Invariant:
           If   |- Psi1 ctx
           and  |- Psi1' ctx
           and  |- Psi2 ctx
           and  Psi2 = Psi2', Psi2''
           and  Psi1 |- s : Psi2
           and  |Psi2''| = l
           then Psi1' = Psi1 modulo variable naming
           and  for all x in Psi2 s.t. s(x) = x in Psi1'
        *)
  (* copyNames  (ignore (s, l),  Psi2) *)
  (*

         merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        
        fun merge (G1, I.Null) = G1
          | merge (G1, I.Decl (G2, D)) =
              I.Decl (merge (G1, G2), D)

         formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        
        fun formatCtx (Psi, G) =
          let
            val G0 = T.makectx Psi

            fun formatCtx' (I.Null) = nil
              | formatCtx' (I.Decl (I.Null, I.Dec (SOME name, V))) =
                  [Fmt.string name, Fmt.string "":"",
                   P.formatExp (G0, V)]
              | formatCtx' (I.Decl (G, I.Dec (SOME name, V))) =
                  (formatCtx' G) @
                  [Fmt.string "","", Fmt.break_,
                   Fmt.string name, Fmt.string "":"",
                   P.formatExp (merge (G0, G), V)]
          in
            Fmt.hbox (Fmt.string ""|"" :: (formatCtx' G @ [Fmt.string ""|""]))
          end

         formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        
        fun formatTuple (Psi, P) =
          let
            fun formatTuple' (T.Unit) = nil
              | formatTuple' (T.Inx (M, T.Unit)) =
              [P.formatExp (T.makectx Psi, M)]
              | formatTuple' (T.Inx (M, P')) =
              (P.formatExp (T.makectx Psi, M) ::
               Fmt.string "","" :: Fmt.break_ :: formatTuple' P')
          in
            case P
              of (T.Inx (_, T.Unit)) => Fmt.hbox (formatTuple' P)
              | _ => Fmt.hVbox0 1 1 1
                (Fmt.string ""("" :: (formatTuple' P @ [Fmt.string "")""]))
          end

         formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        
        fun formatSplitArgs (Psi, L) =
          let
            fun formatSplitArgs' (nil) = nil
              | formatSplitArgs' (M :: nil) =
                  [P.formatExp (T.makectx Psi, M)]
              | formatSplitArgs' (M :: L) =
                  (P.formatExp (T.makectx Psi, M) ::
                   Fmt.string "","" :: Fmt.break_ :: formatSplitArgs' L)
          in
            if List.length L = 1 then Fmt.hbox (formatSplitArgs' L)
            else Fmt.hVbox0 1 1 1
              (Fmt.string ""("" :: (formatSplitArgs' L @ [Fmt.string "")""]))
          end


         formatDecs1 (Psi, Ds, s, L) = L'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for i<=n
                L = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then L' extends L
           s.t. L = (M1 .. Mn)
                for all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        
        fun formatDecs1 (Psi, T.Split (xx, Ds), I.Dot (Ft, s1), L) =
              formatDecs1 (Psi, Ds, s1, frontToExp (Ft) :: L)
          | formatDecs1 (Psi, T.Empty, s1, L) = L
          | formatDecs1 (Psi, Ds, I.Shift n, L) =
              formatDecs1 (Psi, Ds, I.Dot (I.Idx (n+1), I.Shift (n+1)), L)


         formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        
        fun formatDecs0 (Psi, T.App ((xx, M), Ds)) =
            let
              val (Ds', S) =
                formatDecs0 (Psi, Ds)
            in
              (Ds', I.App (M, S))
            end
          | formatDecs0 (Psi, Ds) = (Ds, I.Nil)


         formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        
        fun formatDecs (index, Psi, Ds as T.App ((xx, _), P), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val name = nameLookup index
            in
              Fmt.hbox [formatSplitArgs (Psi1, L'), Fmt.space,
                        Fmt.string ""="", Fmt.break_,
                        Fmt.hVbox (Fmt.string name :: Fmt.break_ ::
                                   P.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.New (B as T.CtxBlock (_, G), Ds),
                        (Psi1, s1)) =
            let
              val B' = ctxBlockName (T.makectx Psi, B)
              val fmt =
                formatDecs (index, I.Decl (Psi, T.Block B'), Ds, (Psi1, s1))
            in
              Fmt.vbox [formatCtx (Psi, G), Fmt.break_, fmt]
            end
          | formatDecs (index, Psi, T.Lemma (lemma, Ds), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val (T.LemmaDec (names, _, _)) = T.lemmaLookup lemma
            in
              Fmt.hbox [formatSplitArgs (Psi1, L'), Fmt.space,
                        Fmt.string ""="", Fmt.break_,
                        Fmt.hVbox (Fmt.string (List.nth (names, index)) :: Fmt.break_ ::
                                   P.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.Left (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index, Psi, Ds, (Psi1, s1))
            in
              fmt
            end
          | formatDecs (index, Psi, T.Right (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index+1, Psi, Ds, (Psi1, s1))
            in
              fmt
            end


*)
  (* fmtSpine callname (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  (* P.formatExp (T.coerceCtx Psi, U) *)
  (*
         frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        
        and frontToExp (T.Idx k) = I.Root (I.BVar k, I.Nil)
          | frontToExp (T.Exp (U)) = U
          | frontToExp (T.Prg (T.PairExp (U, _))) = U     this is a patch -cs
                                                            works only with one exists quantifier
                                                            we cannot use LF spines, we need to
                                                            use tomega spines.

                                                            Next step program printer for tomega spines
                                                            Then change this code. 
*)
  (* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *)
  (* Idx will always be expanded into Expressions and never into programs
                 is this a problem? -- cs *)
  (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
  (* no mutual recursion, recursive call *)
  (* lemma application *)
  (* mutual recursion, k is the projection function *)
  (* val T.ValDec (name, _, _) = T.lemmaLookup l *)
  (* formatCases ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
  (* formatPrg3 callname  (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *)
  (* formatTuple (Psi, P) *)
  (* formatTuple (Psi, P) *)
  (* need to fix the first  argument to formatcases Tue Apr 27 10:38:57 2004 --cs *)
  (* formatLet callname (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
  (* was I.ctxLength Psi - max  --cs *)
  (*            val Fspine =   P.formatSpine callname (T.coerceCtx Psi1, S) *)
  (* was I.ctxLength Psi - max  --cs *)
  (*            val Fspine =   P.formatSpine callname (T.coerceCtx Psi1, S) *)
  (*            val fmt =  formatDecs (0, Psi, Ds, (Psi1', s1)) 
                Fmt.hbox [Fmt.string "" ..."" , Fmt.space, Fmt.string ""="",  Fmt.break_, F1] *)
  (* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *)
  (* need space since there is one before Fbody *)
  (* formatHead callname (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
  (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *)
  (*            val Fspine =   P.formatSpine callname (T.coerceCtx Psi', S) *)
  (* formatPrg2 ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
  (* formatPrg1 ((max, index), Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
  (* formatPrg0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)
  (*      fun formatPrg0 (T.Rec (T.PDec (SOME _, F),
                             T.Case (T.Cases [(Psi, t, P)]))) =
          let
            val max = I.ctxLength Psi    number of ih. 
          in
            Fmt.vbox0 0 1 (formatPrg1 ((max, max), Psi, P))
          end
*)
  (* number of ih. *)
  (*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.vbox0 0 1 [formatFor (I.Null, F) names, Fmt.break_,
                     formatPrg (I.Null, P) names]
*)
  (*   fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args) *)
  (*    fun prgToString Args names = ""not yet implemented "" *)
  (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
  let formatFor = formatFor
  let forToString = forToString
  let formatFun = formatFun
  let formatPrg a b = formatPrg3 (function _ -> "?") (a, b)

  (*    val formatLemmaDec = formatLemmaDec *)
  let evarName = evarName
  let evarReset = evarReset
  let nameEVar = nameEVar
  let prgToString = prgToString
  let funToString = funToString
  let nameCtx = nameCtx
  let formatCtx psi = Fmt.hVbox (formatCtx psi)
  let ctxToString = ctxToString
  (*    val lemmaDecToString = lemmaDecToString *)
end
(*! sharing Print.IntSyn = IntSyn' !*)
(* signature FUNPRINT *)

(* # 1 "src/tomega/Tomegaprint.sml.ml" *)
