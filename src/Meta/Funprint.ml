open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_
open! Print.Print_

(* # 1 "src/meta/Funprint.sig.ml" *)
open Funsyn

(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
include FUNPRINT
(* signature PRINT *)

(* # 1 "src/meta/Funprint.fun.ml" *)
open! Print
open! Basis

(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)
module FunPrint (FunPrint__0 : sig
  (*! structure FunSyn' : FUNSYN !*)
  module Formatter : FORMATTER
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Print : PRINT
end) : FUNPRINT.FUNPRINT = struct
  (*! structure FunSyn = FunSyn' !*)
  module Formatter = Formatter

  open! struct
    module F = FunSyn
    module I = IntSyn
    module Fmt = Formatter
    module P = Print

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

    let rec formatFor' (g, a) = match a with
      | (F.All (ld, f), s) ->
          begin match ld with
          | F.Prim d ->
              let d' = Names.decName g d in
              [
                Fmt.string "{{";
                P.formatDec g (I.decSub d' s);
                Fmt.string "}}";
                Fmt.break_;
              ]
              @ formatFor' (I.Decl (g, d'), (f, I.dot1 s))
          | F.Block (F.CtxBlock (l, g')) ->
              let g'', s'', fmts = formatCtxBlock (g, (g', s)) in
              [ Fmt.string "{"; Fmt.hbox fmts; Fmt.string "}"; Fmt.break_ ]
              @ formatFor' (g'', (f, s''))
          end
      | (F.Ex (d, f), s) ->
          let d' = Names.decName g d in
          [
            Fmt.string "[[";
            P.formatDec g (I.decSub d' s);
            Fmt.string "]]";
            Fmt.break_;
          ]
          @ formatFor' (I.Decl (g, d'), (f, I.dot1 s))
      | (True, s) -> [ Fmt.string "True" ]

    let formatFor psi f names =
      let nameLookup index = List.nth (names, index) in
      let rec formatFor1 (index, g, a) = match a with
        | (F.And (f1, f2), s) ->
            formatFor1 (index, g, (f1, s))
            @ [ Fmt.break_ ]
            @ formatFor1 (index + 1, g, (f2, s))
        | (f, s) ->
            [
              Fmt.string (nameLookup index);
              Fmt.space;
              Fmt.string "::";
              Fmt.space;
              Fmt.hVbox (formatFor' (g, (f, s)));
            ]
      in
      let formatFor0 args = Fmt.vbox0 0 1 (formatFor1 args) in
      Names.varReset I.Null;
      formatFor0 (0, F.makectx psi, (f, I.id))

    let formatForBare g f = Fmt.hVbox (formatFor' (g, (f, I.id)))

    let formatPro psi p names =
      let args = (psi, p) in
      let nameLookup index = List.nth (names, index) in
      let blockName (g1, g2) =
        let rec blockName' (g1, a) = match a with
          | I.Null -> (g1, I.Null)
          | I.Decl (g2, d) ->
              let g1', g2' = blockName' (g1, g2) in
              let d' = Names.decName g1 d in
              (I.Decl (g1', d'), I.Decl (g2', d'))
        in
        let g1', g2' = blockName' (g1, g2) in
        g2'
      in
      let ctxBlockName (g1, F.CtxBlock (name, g2)) =
        F.CtxBlock (name, blockName (g1, g2))
      in
      let decName a1 b1 = match a1, b1 with
        | g, F.Prim d -> F.Prim (Names.decName g d)
        | g, F.Block cb -> F.Block (ctxBlockName (g, cb))
      in
      let numberOfSplits ds =
        let rec numberOfSplits' (empty, n) = match empty with
          | empty -> n
          | F.New (_, ds) -> numberOfSplits' (ds, n)
          | F.App (_, ds) -> numberOfSplits' (ds, n)
          | F.Lemma (_, ds) -> numberOfSplits' (ds, n)
          | F.Split (_, ds) -> numberOfSplits' (ds, n + 1)
          | F.Left (_, ds) -> numberOfSplits' (ds, n)
          | F.Right (_, ds) -> numberOfSplits' (ds, n)
        in
        numberOfSplits' (ds, 0)
      in
      let psiName (psi1, s, psi2, l) =
        let nameDec (a, name) = match a with
          | (I.Dec (Some _, _) as d) -> d
          | I.Dec (None, v) -> I.Dec (Some name, v)
        in
        let rec namePsi (a, n, name) = match a, n with
          | I.Decl (psi, F.Prim d), 1 ->
              I.Decl (psi, F.Prim (nameDec (d, name)))
          | I.Decl (psi, (F.Prim d as ld)), n ->
              I.Decl (namePsi (psi, n - 1, name), ld)
          | I.Decl (psi, F.Block (F.CtxBlock (label, g))), n ->
              let psi', g' =
                nameG
                  (psi, g, n, name, function n' -> namePsi (psi, n', name))
              in
              I.Decl (psi', F.Block (F.CtxBlock (label, g')))
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
          | I.Dot (_, s), k -> ignore (s, k - 1)
          | I.Shift n, k ->
              ignore (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), k - 1)
        in
        let rec copyNames arg__1 arg__2 =
          begin match (arg__1, arg__2) with
          | (I.Shift n, (I.Decl _ as g)), psi1 ->
              copyNames (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), g) psi1
          | (I.Dot (I.Exp _, s), I.Decl (g, _)), psi1 -> copyNames (s, g) psi1
          | (I.Dot (I.Idx k, s), I.Decl (g, I.Dec (None, _))), psi1 ->
              copyNames (s, g) psi1
          | (I.Dot (I.Idx k, s), I.Decl (g, I.Dec (Some name, _))), psi1 ->
              let psi1' = namePsi (psi1, k, name) in
              copyNames (s, g) psi1'
          | (I.Shift _, I.Null), psi1 -> psi1
          end
        in
        let rec psiName' = function
          | I.Null -> I.Null
          | I.Decl (psi, d) ->
              let psi' = psiName' psi in
              I.Decl (psi', decName (F.makectx psi') d)
        in
        psiName' (copyNames (ignore (s, l), F.makectx psi2) psi1)
      in
      let rec merge (g1, a) = match a with
        | I.Null -> g1
        | I.Decl (g2, d) -> I.Decl (merge (g1, g2), d)
      in
      let formatCtx psi g =
        let g0 = F.makectx psi in
        let rec formatCtx' = function
          | I.Null -> []
          | I.Decl (I.Null, I.Dec (Some name, v)) ->
              [ Fmt.string name; Fmt.string ":"; Print.formatExp g0 v ]
          | I.Decl (g, I.Dec (Some name, v)) ->
              formatCtx' g
              @ [
                  Fmt.string ",";
                  Fmt.break_;
                  Fmt.string name;
                  Fmt.string ":";
                  Print.formatExp (merge (g0, g)) v;
                ]
        in
        Fmt.hbox ((Fmt.string "|" :: formatCtx' g) @ [ Fmt.string "|" ])
      in
      let formatTuple (psi, p) =
        let rec formatTuple' = function
          | F.Unit -> []
          | F.Inx (m, F.Unit) -> [ Print.formatExp (F.makectx psi) m ]
          | F.Inx (m, p') ->
              Print.formatExp (F.makectx psi) m
              :: Fmt.string "," :: Fmt.break_ :: formatTuple' p'
        in
        begin match p with
        | F.Inx (_, F.Unit) -> Fmt.hbox (formatTuple' p)
        | _ ->
            Fmt.hVbox0 1 1 1
              ((Fmt.string "(" :: formatTuple' p) @ [ Fmt.string ")" ])
        end
      in
      let formatSplitArgs (psi, l) =
        let rec formatSplitArgs' = function
          | [] -> []
          | m :: [] -> [ Print.formatExp (F.makectx psi) m ]
          | m :: l ->
              Print.formatExp (F.makectx psi) m
              :: Fmt.string "," :: Fmt.break_ :: formatSplitArgs' l
        in
        begin if List.length l = 1 then Fmt.hbox (formatSplitArgs' l)
        else
          Fmt.hVbox0 1 1 1
            ((Fmt.string "(" :: formatSplitArgs' l) @ [ Fmt.string ")" ])
        end
      in
      let frontToExp = function
        | I.Idx k -> I.Root (I.BVar k, I.Nil)
        | I.Exp u -> u
      in
      let rec formatDecs1 (psi, empty, a, l) = match empty, a with
        | F.Split (xx, ds), I.Dot (ft, s1) ->
            formatDecs1 (psi, ds, s1, frontToExp ft :: l)
        | empty, s1 -> l
        | ds, I.Shift n ->
            formatDecs1 (psi, ds, I.Dot (I.Idx (n + 1), I.Shift (n + 1)), l)
      in
      let rec formatDecs0 (psi, a) = match a with
        | F.App ((xx, m), ds) ->
            let ds', s = formatDecs0 (psi, ds) in
            (ds', I.App (m, s))
        | ds -> (ds, I.Nil)
      in
      let rec formatDecs (index, psi, a, b) = match a, b with
        | (F.App ((xx, _), p) as ds), (psi1, s1) ->
            let ds', s = formatDecs0 (psi, ds) in
            let l' = formatDecs1 (psi, ds', s1, []) in
            let name = nameLookup index in
            Fmt.hbox
              [
                formatSplitArgs (psi1, l');
                Fmt.space;
                Fmt.string "=";
                Fmt.break_;
                Fmt.hVbox
                  (Fmt.string name :: Fmt.break_
                  :: Print.formatSpine (F.makectx psi) s);
              ]
        | F.New ((F.CtxBlock (_, g) as b), ds), (psi1, s1) ->
            let b' = ctxBlockName (F.makectx psi, b) in
            let fmt =
              formatDecs (index, I.Decl (psi, F.Block b'), ds, (psi1, s1))
            in
            Fmt.vbox [ formatCtx psi g; Fmt.break_; fmt ]
        | F.Lemma (lemma, ds), (psi1, s1) ->
            let ds', s = formatDecs0 (psi, ds) in
            let l' = formatDecs1 (psi, ds', s1, []) in
            let (F.LemmaDec (names, _, _)) = F.lemmaLookup lemma in
            Fmt.hbox
              [
                formatSplitArgs (psi1, l');
                Fmt.space;
                Fmt.string "=";
                Fmt.break_;
                Fmt.hVbox
                  (Fmt.string (List.nth (names, index))
                  :: Fmt.break_
                  :: Print.formatSpine (F.makectx psi) s);
              ]
        | F.Left (_, ds), (psi1, s1) ->
            let fmt = formatDecs (index, psi, ds, (psi1, s1)) in
            fmt
        | F.Right (_, ds), (psi1, s1) ->
            let fmt = formatDecs (index + 1, psi, ds, (psi1, s1)) in
            fmt
      in
      let rec formatLet (psi, a, fmts) = match a with
        | F.Let (ds, F.Case (F.Opts ((psi1, s1, (F.Let _ as p1)) :: []))) ->
            let psi1' = psiName (psi1, s1, psi, numberOfSplits ds) in
            let fmt = formatDecs (0, psi, ds, (psi1', s1)) in
            formatLet (psi1', p1, fmts @ [ fmt; Fmt.break_ ])
        | F.Let (ds, F.Case (F.Opts ((psi1, s1, p1) :: []))) ->
            let psi1' = psiName (psi1, s1, psi, numberOfSplits ds) in
            let fmt = formatDecs (0, psi, ds, (psi1', s1)) in
            Fmt.vbox0 0 1
              [
                Fmt.string "let";
                Fmt.break_;
                Fmt.spaces 2;
                Fmt.vbox0 0 1 (fmts @ [ fmt ]);
                Fmt.break_;
                Fmt.string "in";
                Fmt.break_;
                Fmt.spaces 2;
                formatPro3 (psi1', p1);
                Fmt.break_;
                Fmt.string "end";
              ]
      and formatPro3 (psi, a) = match a with
        | (Unit as p) -> formatTuple (psi, p)
        | (F.Inx _ as p) -> formatTuple (psi, p)
        | (F.Let _ as p) -> formatLet (psi, p, [])
      in
      let rec argsToSpine (a, b, s_) = match a, b with
        | s, I.Null -> s_
        | I.Shift n, psi ->
            argsToSpine (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), psi, s_)
        | I.Dot (ft, s), I.Decl (psi, d) ->
            argsToSpine (s, psi, I.App (frontToExp ft, s_))
      in
      let formatHead (index, psi', s, psi) =
        Fmt.hbox
          [
            Fmt.space;
            Fmt.hVbox
              (Fmt.string (nameLookup index)
              :: Fmt.break_
              :: Print.formatSpine (F.makectx psi') (argsToSpine (s, psi, I.Nil))
              );
          ]
      in
      let rec formatPro2 (index, psi, a) = match a with
        | [] -> []
        | (psi', s, p) :: [] ->
            let psi'' = psiName (psi', s, psi, 0) in
            let fhead =
              begin if index = 0 then "fun" else "and"
              end
            in
            [
              Fmt.hVbox0 1 5 1
                [
                  Fmt.string fhead;
                  formatHead (index, psi'', s, psi);
                  Fmt.space;
                  Fmt.string "=";
                  Fmt.break_;
                  formatPro3 (psi'', p);
                ];
              Fmt.break_;
            ]
        | (psi', s, p) :: o ->
            let psi'' = psiName (psi', s, psi, 0) in
            formatPro2 (index, psi, o)
            @ [
                Fmt.hVbox0 1 5 1
                  [
                    Fmt.string "  |";
                    formatHead (index, psi'', s, psi);
                    Fmt.space;
                    Fmt.string "=";
                    Fmt.break_;
                    formatPro3 (psi'', p);
                  ];
                Fmt.break_;
              ]
      in
      let rec formatPro1 (index, psi, a) = match a with
        | F.Lam (d, p) ->
            formatPro1 (index, I.Decl (psi, decName (F.makectx psi) d), p)
        | F.Case (F.Opts os) -> formatPro2 (index, psi, os)
        | F.Pair (p1, p2) ->
            formatPro1 (index, psi, p1) @ formatPro1 (index + 1, psi, p2)
      in
      let formatPro0 (psi, F.Rec (dd, p)) =
        Fmt.vbox0 0 1 (formatPro1 (0, psi, p))
      in
      Names.varReset I.Null;
      formatPro0 args

    let formatLemmaDec (F.LemmaDec (names, p, f)) =
      Fmt.vbox0 0 1
        [
          formatFor I.Null f names; Fmt.break_; formatPro I.Null p names;
        ]
    let forToString psi f names = Fmt.makestring_fmt (formatFor psi f names)
    let proToString psi p names = Fmt.makestring_fmt (formatPro psi p names)
    let proToString psi p names = Fmt.makestring_fmt (formatPro psi p names)
    let lemmaDecToString args = Fmt.makestring_fmt (formatLemmaDec args)
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
  (* formatFor (Psi, F) names = fmt'
       formatForBare (Psi, F) = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi |- F = F1 ^ .. ^ Fn formula
       and  names is a list of n names,
       then fmt' is the pretty printed format
    *)
  (* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *)
  (* formatPro (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *)
  (* blockName (G1, G2) = G2'

           Invariant:
           If   G1 |- G2 ctx
           then G2' = G2 modulo new non-conficting variable Names.
        *)
  (* ctxBlockName (G1, CB) = CB'

           Invariant:
           If   G1 |- CB ctxblock
           then CB' = CB modulo new non-conficting variable Names.
        *)
  (* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable Names.
        *)
  (* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
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
  (* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *)
  (* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *)
  (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
  (* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *)
  (* frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *)
  (* formatDecs1 (Psi, Ds, s, L) = L'

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
        *)
  (* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *)
  (* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *)
  (* formatLet (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *)
  (* formatPro3 (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
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
  (* formatHead (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *)
  (* formatPro2 (index, Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *)
  (* formatPro1 (index, Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *)
  (* formatPro0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *)
  let formatFor = formatFor
  let formatForBare = formatForBare
  let formatPro = formatPro
  let formatLemmaDec = formatLemmaDec
  let forToString = forToString
  let proToString = proToString
  let lemmaDecToString = lemmaDecToString
end
(*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
(* signature FUNPRINT *)

(* # 1 "src/meta/Funprint.sml.ml" *)
