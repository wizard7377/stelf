open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_

(* # 1 "src/print/Print_.sig.ml" *)

(* Printing *)
(* Author: Frank Pfenning *)

include PRINT
(** Modified: Jeff Polakow *)

(* signature PRINT *)

(* # 1 "src/print/Print_.fun.ml" *)
open! Symbol
open! Basis

module MakePrint
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER)
    (Symbol : SYMBOL) : PRINT = struct
  (*
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow, Roberto Virga *)
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Formatter_param : FORMATTER
  module Symbol : SYMBOL
*)
  (*! structure IntSyn = IntSyn' !*)
  module Formatter = struct
    include Formatter_param
  end

  module Whnf = Whnf
  module Abstract = Abstract
  module Constraints = Constraints
  module Names = Names
  module Symbol = Symbol
  module Tomega = Tomega

  (* Externally visible parameters *)
  let implicit = ref false

  (* whether to print implicit arguments *)
  let printInfix = ref false

  (* if implicit is ref true, whether to print infix ops when possible *)
  let printDepth = ref (None : int option)

  (* limit on term depth to print *)
  let printLength = ref (None : int option)

  (* limit on number of arguments to print *)
  let noShadow = ref false

  (* if false, omit constructor paths when printing terms *)
  let showConstPath = ref true

  (* if true, don't print shadowed constants as ""%const%"" *)
  open! struct
    module I = IntSyn
    module FX = Names.Fixity
    module F = Formatter
    module T = Tomega

    let full_stop = F.string "%."
    let lvars : I.block option ref list ref = ref []

    let lookuplvar l =
      ignore begin if List.exists (function r -> r = l) !lvars then ()
        else lvars := !lvars @ [ l ]
        end;
      let rec find (r :: l_) n =
        begin if r = l then n else find l_ (n + 1)
        end
      in
      Int.toString (find !lvars 0)

    let str_ = F.string
    let str0 (s, n) = F.string0 n s
    let sym s = str0 (Symbol.sym s)
    let nameOf = function Some id -> id | None -> "_"
    let fmtEVar (g, x) = str0 (Symbol.evar (Names.evarName g x))
    let fmtAVar (g, x) = str0 (Symbol.evar (Names.evarName g x ^ "_"))

    let rec isNil = function
      | I.Nil -> true
      | I.App _ -> false
      | I.SClo (s, _) -> isNil s

    let subToSpine (depth, s) =
      let rec sTS (a, s_) = match a with
        | I.Shift k ->
            begin if k < depth then
              sTS (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
            else s_
            end
        | I.Dot (I.Idx k, s) -> sTS (s, I.App (I.Root (I.BVar k, I.Nil), s_))
        | I.Dot (I.Exp u, s) -> sTS (s, I.App (u, s_))
      in
      sTS (s, I.Nil)

    type argStatus = TooFew | Exact of I.spine | TooMany of I.spine * I.spine

    let sclo' (a, s) = match a with
      | TooFew -> TooFew
      | Exact s_ -> Exact (I.SClo (s_, s))
      | TooMany (s_, s') -> TooMany (I.SClo (s_, s), I.SClo (s', s))

    let sclo'' (a, s) = match a with
      | TooFew -> TooFew
      | Exact s -> Exact s
      | TooMany (s_, s') -> TooMany (s_, I.SClo (s', s))

    let rec dropImp = function
      | 0, s, 0 -> Exact s
      | 0, s_, n ->
          let rec checkArgNumber = function
            | I.Nil, 0 -> Exact s_
            | I.Nil, k -> TooFew
            | (I.App _ as s'), 0 -> TooMany (s_, s')
            | I.App (u, s'), k -> checkArgNumber (s', k - 1)
            | I.SClo (s', s), k -> sclo'' (checkArgNumber (s', k), s)
          in
          checkArgNumber (s_, n)
      | i, I.App (u, s), n -> dropImp (i - 1, s, n)
      | i, I.SClo (s_, s), n -> sclo' (dropImp (i, s_, n), s)
      | i, I.Nil, n -> TooFew

    let exceeded = function
      | _, None -> false
      | (n : int), Some (m : int) -> n >= m

    type ctxt = Ctxt of FX.fixity * F.format list * int

    type opargs =
      | OpArgs of FX.fixity * F.format list * I.spine
      | EtaLong of I.exp

    let noCtxt =
      Ctxt (FX.Prefix (FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec)))), [], 0)

    let binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec))
    let arrowPrec = FX.dec FX.minPrec
    let juxPrec = FX.inc FX.maxPrec

    let arrow v1 v2 =
      OpArgs
        ( FX.Infix (arrowPrec, FX.Right),
          [ F.break; sym "%->"; F.space ],
          I.App (v1, I.App (v2, I.Nil)) )

    let appCtxt = Ctxt (FX.Nonfix, [], 0)

    let fixityCon = function
      | I.Const cid -> Names.getFixity cid
      | I.Skonst cid -> FX.Nonfix
      | I.Def cid -> Names.getFixity cid
      | I.NSDef cid -> Names.getFixity cid
      | _ -> FX.Nonfix

    let impCon = function
      | I.Const cid -> I.constImp cid
      | I.Skonst cid -> I.constImp cid
      | I.Def cid -> I.constImp cid
      | I.NSDef cid -> I.constImp cid
      | _ -> 0

    let argNumber = function
      | FX.Nonfix -> 0
      | FX.Infix _ -> 2
      | FX.Prefix _ -> 1
      | FX.Postfix _ -> 1

    let fmtConstPath (f, Names.Qid (ids, id)) =
      if !showConstPath then
        F.hVbox
          (foldr
             (function id, fmt -> str0 (Symbol.str id) :: full_stop :: fmt)
             [ str0 (f id) ]
             ids)
      else str0 (f id)

    let rec parmDec = function
      | d :: l, 1 -> d
      | d :: l, j -> parmDec (l, j - 1)

    let parmName (cid, i) =
      let gsome, gblock = I.constBlock cid in
      begin match parmDec (gblock, i) with
      | I.Dec (Some pname, _) -> pname
      | I.Dec (None, _) -> Int.toString i
      end

    let projName (g, a) = match a with
      | I.Proj (I.Bidx k, i) ->
          let (I.BDec (Some bname, (cid, t))) = I.ctxLookup g k in
          (bname ^ "_") ^ parmName (cid, i)
      | I.Proj (I.LVar (r, _, (cid, t)), i) -> "_" ^ parmName (cid, i)
      | I.Proj (I.Inst iota, i) -> "*"

    let constQid cid =
      begin if !noShadow then Names.conDecQid (I.sgnLookup cid)
      else Names.constQid cid
      end

    let cidToFmt cid = F.string (Names.qidToString (Names.constQid cid))

    let rec formatCids = function
      | [] -> []
      | cid :: [] -> [ cidToFmt cid ]
      | cid :: cids ->
          cidToFmt cid :: F.break :: F.string "|" :: F.space :: formatCids cids

    let formatWorlds (T.Worlds cids) =
      F.hbox [ F.string "("; F.hVbox (formatCids cids); F.string ")" ]

    let worldsToString w = F.makestring_fmt (formatWorlds w)

    let fmtCon (g, a) = match a with
      | I.BVar n -> str0 (Symbol.bvar (Names.bvarName g n))
      | I.Const cid -> fmtConstPath (Symbol.const, constQid cid)
      | I.Skonst cid -> fmtConstPath (Symbol.skonst, constQid cid)
      | I.Def cid -> fmtConstPath (Symbol.def, constQid cid)
      | I.NSDef cid -> fmtConstPath (Symbol.def, constQid cid)
      | I.FVar (name, _, _) -> str0 (Symbol.fvar name)
      | (I.Proj (I.Bidx k, i) as h) ->
          str0 (Symbol.const (projName (g, h)))
      | (I.Proj (I.LVar (({ contents = None } as r), sk, (cid, t)), i) as h) ->
          let n = lookuplvar r in
          fmtConstPath
            ( (function
              | l0 ->
                  Symbol.const (((("#[" ^ l0) ^ n) ^ "]") ^ projName (g, h))),
              constQid cid )
      | I.FgnConst (cs, conDec) ->
          let name = I.conDecName conDec in
          begin match (Names.constLookup (Names.Qid ([], name)), !noShadow) with
          | Some _, false -> str0 (Symbol.const (("%" ^ name) ^ "%"))
          | _ -> str0 (Symbol.const name)
          end

    let evarArgs (g, d, x, s) =
      OpArgs (FX.Nonfix, [ fmtEVar (g, x) ], subToSpine (I.ctxLength g, s))

    let evarArgs' (g, d, x, s) =
      OpArgs (FX.Nonfix, [ fmtAVar (g, x) ], subToSpine (I.ctxLength g, s))

    let rec fst (a, s) = match a with
      | I.App (u1, _) -> (u1, s)
      | I.SClo (s_, s') -> fst (s_, I.comp s' s)

    let rec snd (a, s) = match a with
      | I.App (u1, s_) -> fst (s_, s)
      | I.SClo (s_, s') -> snd (s_, I.comp s' s)

    let elide l =
      begin match !printLength with None -> false | Some l' -> l > l'
      end

    let ldots = sym "..."

    let addots l =
      begin match !printLength with None -> false | Some l' -> l = l'
      end

    let parens ((fixity', fixity), fmt) =
      begin if FX.leq (FX.prec fixity) (FX.prec fixity') then
        F.hbox [ sym "("; fmt; sym ")" ]
      else fmt
      end

    let eqFix = function
      | FX.Infix (p, FX.Left), FX.Infix (p', FX.Left) -> p = p'
      | FX.Infix (p, FX.Right), FX.Infix (p', FX.Right) -> p = p'
      | FX.Prefix p, FX.Prefix p' -> p = p'
      | FX.Postfix p, FX.Postfix p' -> p = p'
      | _ -> false

    let addAccum (fmt, a, accum) = match a, accum with
      | _, [] -> fmt
      | FX.Infix (_, FX.Left), accum -> F.hVbox ([ fmt ] @ accum)
      | FX.Infix (_, FX.Right), accum -> F.hVbox (accum @ [ fmt ])
      | FX.Prefix _, accum -> F.hVbox (accum @ [ fmt ])
      | FX.Postfix _, accum -> F.hVbox ([ fmt ] @ accum)

    let aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)
    let fmtUni = function I.Type -> sym "type" | I.Kind -> sym "kind"

    let rec fmtExpW (g, d, ctx, a) = match a with
      | (I.Uni l, s) -> aa (ctx, fmtUni l)
      | (I.Pi (((I.Dec (name_opt, _) as d_), p), v2), s)
        when !Global.printArrowSugar
             && match (name_opt, p) with None, I.No -> true | _ -> false ->
          let hops, gf, (uf, sf) =
            arrowSugarHops (g, (I.Pi ((d_, p), v2), s))
          in
          let domFmts =
            List.map
              (fun (gi, (vi, si)) ->
                fmtExp
                  ( gi,
                    d + 1,
                    Ctxt (FX.Infix (arrowPrec, FX.Right), [], 0),
                    (vi, si) ))
              hops
          in
          let codFmt =
            fmtExp
              (gf, d + 1, Ctxt (FX.Infix (arrowPrec, FX.Right), [], 0), (uf, sf))
          in
          let whole =
            F.hbox
              [
                sym "%pi";
                F.space;
                F.hVbox (joinArrowChain (domFmts @ [ codFmt ]));
              ]
          in
          let (Ctxt (fixity', accum, _l)) = ctx in
          addAccum
            (parens ((fixity', FX.Prefix binderPrec), whole), fixity', accum)
      | (I.Pi (((I.Dec (_, v1) as d_), p), v2), s) ->
          begin match p with
          | I.Maybe ->
              let d' = Names.decLUName g d_ in
              fmtLevel
                ( I.Decl (g, d'),
                  d,
                  ctx,
                  (braces (g, d, ((d', v2), s)), I.dot1 s) )
          | _ ->
              let d' = Names.decLUName g d_ in
              fmtLevel
                ( I.Decl (g, d'),
                  d,
                  ctx,
                  (braces (g, d, ((d', v2), s)), I.dot1 s) )
          end
      | (I.Pi (((I.BDec _ as d_), p), v2), s) ->
          let d' = Names.decLUName g d_ in
          fmtLevel
            ( I.Decl (g, d'),
              d,
              ctx,
              (braces (g, d, ((d', v2), s)), I.dot1 s) )
      | (I.Pi (((I.ADec _ as d_), p), v2), s) ->
          let braces =
            OpArgs
              ( FX.Prefix binderPrec,
                [ sym "["; sym "_"; sym "]"; F.break ],
                IntSyn.App (v2, IntSyn.Nil) )
          in
          fmtLevel (I.Decl (g, d_), d, ctx, (braces, I.dot1 s))
      | ((I.Root (h_r, sp_r) as u), s) ->
          fmtOpArgs (g, d, ctx, opargs (g, d, (h_r, sp_r)), s)
      | (I.Lam (d_, u), s) ->
          let d' = Names.decLUName g d_ in
          fmtLevel
            ( I.Decl (g, d'),
              d,
              ctx,
              (brackets (g, d, ((d', u), s)), I.dot1 s) )
      | ((I.EVar _ as x), s) ->
          begin if !implicit then
            aa (ctx, F.hVbox (fmtEVar (g, x) :: fmtSub (g, d, s)))
          else fmtOpArgs (g, d, ctx, evarArgs (g, d, x, s), I.id)
          end
      | ((I.AVar _ as x), s) ->
          begin if !implicit then
            aa (ctx, F.hVbox (fmtAVar (g, x) :: fmtSub (g, d, s)))
          else fmtOpArgs (g, d, ctx, evarArgs' (g, d, x, s), I.id)
          end
      | ((I.FgnExp (cs_fe, fe_fe) as u), s) ->
          fmtExp
            (g, d, ctx, (I.FgnExpStd.ToInternal.apply cs_fe fe_fe (), s))

    and opargsImplicit (g, d, (c, s)) =
      OpArgs (FX.Nonfix, [ fmtCon (g, c) ], s)

    and opargsImplicitInfix (g, d, ((c, s) as r)) =
      let fixity = fixityCon c in
      begin match fixity with
      | FX.Infix _ -> opargsExplicit (g, d, r)
      | _ -> OpArgs (FX.Nonfix, [ fmtCon (g, c) ], s)
      end

    and opargsExplicit (g, d, ((c, s) as r)) =
      let opFmt = fmtCon (g, c) in
      let fixity = fixityCon c in
      let rec oe = function
        | Exact s' ->
            begin match fixity with
            | FX.Nonfix -> OpArgs (FX.Nonfix, [ opFmt ], s')
            | FX.Prefix _ -> OpArgs (fixity, [ opFmt; F.break ], s')
            | FX.Postfix _ -> OpArgs (fixity, [ F.break; opFmt ], s')
            | FX.Infix _ -> OpArgs (fixity, [ F.break; opFmt; F.space ], s')
            end
        | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root (c, s)))
        | TooMany (s', s'') ->
            let opFmt' = fmtOpArgs (g, d, noCtxt, oe (Exact s'), I.id) in
            OpArgs (FX.Nonfix, [ F.hbox [ sym "("; opFmt'; sym ")" ] ], s'')
      in
      oe (dropImp (impCon c, s, argNumber fixity))

    and opargs (g, d, r) =
      begin if !implicit then
        begin if !printInfix then opargsImplicitInfix (g, d, r)
        else opargsImplicit (g, d, r)
        end
      else opargsExplicit (g, d, r)
      end

    and fmtOpArgs (g, d, ctx, a, s) = match a with
      | (OpArgs (_, opFmts, s') as oa) ->
          begin if isNil s' then aa (ctx, List.hd opFmts)
          else fmtLevel (g, d, ctx, (oa, s))
          end
      | EtaLong u' -> fmtExpW (g, d, ctx, (u', s))

    and fmtSub (g, d, s) = str_ "[" :: fmtSub' (g, d, 0, s)

    and fmtSub' (g, d, l, s) =
      begin if elide l then [ ldots ] else fmtSub'' (g, d, l, s)
      end

    and fmtSub'' (g, d, l, a) = match a with
      | I.Shift k -> [ str_ ("^" ^ Int.toString k); str_ "]" ]
      | I.Dot (I.Idx k, s) ->
          str_ (Names.bvarName g k)
          :: str_ "." :: F.break
          :: fmtSub' (g, d, l + 1, s)
      | I.Dot (I.Exp u, s) ->
          fmtExp (g, d + 1, noCtxt, (u, I.id))
          :: str_ "." :: F.break
          :: fmtSub' (g, d, l + 1, s)

    and fmtExp (g, d, ctx, (u, s)) =
      begin if exceeded (d, !printDepth) then sym "%%"
      else fmtExpW (g, d, ctx, Whnf.whnf (u, s))
      end

    and fmtSpine (g, d, l, a) = match a with
      | (I.Nil, _) -> []
      | (I.SClo (s_, s'), s) ->
          fmtSpine (g, d, l, (s_, I.comp s' s))
      | (I.App (u, s_), s) ->
          begin if elide l then []
          else
            begin if addots l then [ ldots ]
            else
              fmtExp (g, d + 1, appCtxt, (u, s))
              :: fmtSpine' (g, d, l, (s_, s))
            end
          end

    and fmtSpine' (g, d, l, a) = match a with
      | (I.Nil, _) -> []
      | (I.SClo (s_, s'), s) ->
          fmtSpine' (g, d, l, (s_, I.comp s' s))
      | (s_, s) -> F.break :: fmtSpine (g, d, l + 1, (s_, s))

    and fmtLevel (g, d, a, b) = match a, b with
      | Ctxt (fixity', accum, l), (OpArgs ((FX.Nonfix as fixity), fmts, s_), s) ->
          let atm = fmtSpine (g, d, 0, (s_, s)) in
          addAccum
            ( parens ((fixity', fixity), F.hVbox (fmts @ [ F.break ] @ atm)),
              fixity',
              accum )
      | Ctxt (fixity', accum, l), (OpArgs ((FX.Infix (p, FX.Left) as fixity), fmts, s_), s) ->
          let accMore = eqFix (fixity, fixity') in
          let rhs =
            begin if accMore && elide l then []
            else
              begin if accMore && addots l then fmts @ [ ldots ]
              else
                fmts
                @ [
                    fmtExp
                      ( g,
                        d + 1,
                        Ctxt (FX.Infix (p, FX.None), [], 0),
                        snd (s_, s) );
                  ]
              end
            end
          in
          begin if accMore then
            fmtExp (g, d, Ctxt (fixity, rhs @ accum, l + 1), fst (s_, s))
          else
            let both = fmtExp (g, d, Ctxt (fixity, rhs, 0), fst (s_, s)) in
            addAccum (parens ((fixity', fixity), both), fixity', accum)
          end
      | Ctxt (fixity', accum, l), (OpArgs ((FX.Infix (p, FX.Right) as fixity), fmts, s_), s) ->
          let accMore = eqFix (fixity, fixity') in
          let lhs =
            begin if accMore && elide l then []
            else
              begin if accMore && addots l then [ ldots ] @ fmts
              else
                [
                  fmtExp
                    (g, d + 1, Ctxt (FX.Infix (p, FX.None), [], 0), fst (s_, s));
                ]
                @ fmts
              end
            end
          in
          begin if accMore then
            fmtExp (g, d, Ctxt (fixity, accum @ lhs, l + 1), snd (s_, s))
          else
            let both = fmtExp (g, d, Ctxt (fixity, lhs, 0), snd (s_, s)) in
            addAccum (parens ((fixity', fixity), both), fixity', accum)
          end
      | Ctxt (fixity', accum, l), (OpArgs ((FX.Infix (_, FX.None) as fixity), fmts, s_), s) ->
          let lhs = fmtExp (g, d + 1, Ctxt (fixity, [], 0), fst (s_, s)) in
          let rhs = fmtExp (g, d + 1, Ctxt (fixity, [], 0), snd (s_, s)) in
          addAccum
            ( parens ((fixity', fixity), F.hVbox ([ lhs ] @ fmts @ [ rhs ])),
              fixity',
              accum )
      | Ctxt (fixity', accum, l), (OpArgs ((FX.Prefix _ as fixity), fmts, s_), s) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            begin if accMore && elide l then []
            else
              begin if accMore && addots l then [ ldots; F.break ] else fmts
              end
            end
          in
          begin if accMore then
            fmtExp (g, d, Ctxt (fixity, accum @ pfx, l + 1), fst (s_, s))
          else
            let whole = fmtExp (g, d, Ctxt (fixity, pfx, 0), fst (s_, s)) in
            addAccum (parens ((fixity', fixity), whole), fixity', accum)
          end
      | Ctxt (fixity', accum, l), (OpArgs ((FX.Postfix _ as fixity), fmts, s_), s) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            begin if accMore && elide l then []
            else
              begin if accMore && addots l then [ F.break; ldots ] else fmts
              end
            end
          in
          begin if accMore then
            fmtExp (g, d, Ctxt (fixity, pfx @ accum, l + 1), fst (s_, s))
          else
            let whole = fmtExp (g, d, Ctxt (fixity, pfx, 0), fst (s_, s)) in
            addAccum (parens ((fixity', fixity), whole), fixity', accum)
          end

    and braces (g, d, ((d_, v), s)) =
      OpArgs
        ( FX.Prefix binderPrec,
          [ sym "{"; fmtDec (g, d, (d_, s)); sym "}"; F.break ],
          IntSyn.App (v, IntSyn.Nil) )

    and brackets (g, d, ((d_, u), s)) =
      OpArgs
        ( FX.Prefix binderPrec,
          [ sym "["; fmtDec (g, d, (d_, s)); sym "]"; F.break ],
          IntSyn.App (u, IntSyn.Nil) )

    (* Collect a maximal run of anonymous, provably non-dependent Pi's
       starting at [(u_, s)] into a flat list of domains (each paired with
       the naming context and substitution it must be printed under) plus
       the final codomain, for `%pi A %-> B %-> ...` arrow-sugar printing. *)
    and arrowSugarHops (g, (u, s)) =
      begin match Whnf.whnf (u, s) with
      | I.Pi (((I.Dec (None, v1) as d), I.No), v2), s' ->
          let hops, gf, final =
            arrowSugarHops (I.Decl (g, d), (v2, I.dot1 s'))
          in
          ((g, (v1, s')) :: hops, gf, final)
      | other -> ([], g, other)
      end

    and joinArrowChain = function
      | [] -> []
      | [ f ] -> [ f ]
      | f :: rest -> f :: F.break :: sym "%->" :: F.space :: joinArrowChain rest

    and fmtDec (g, d, a) = match a with
      | (I.Dec (x, v), s) ->
          F.hVbox
            [
              str0 (Symbol.bvar (nameOf x));
              F.space;
              fmtExp (g, d + 1, noCtxt, (v, s));
            ]
      | (I.BDec (x, (cid, t)), s) ->
          let gsome, gblock = I.constBlock cid in
          F.hVbox
            ([ str0 (Symbol.const (nameOf x)); F.space ]
            @ fmtDecList' (g, (gblock, I.comp t s)))
      | (I.ADec (x, _), s) ->
          F.hVbox [ str0 (Symbol.bvar (nameOf x)); sym "_" ]
      | (I.NDec (Some name), s) -> F.hVbox [ sym name ]

    and fmtDecList' (g0, a) = match a with
      | ([], s) -> []
      | (d :: [], s) -> [ sym "{"; fmtDec (g0, 0, (d, s)); sym "}" ]
      | (d :: l, s) ->
          sym "{"
          :: fmtDec (g0, 0, (d, s))
          :: sym "}" :: F.break
          :: fmtDecList' (I.Decl (g0, d), (l, I.dot1 s))

    let rec skipI (i, g, a) = match i, a with
      | 0, v -> (g, v)
      | i, I.Pi ((d, _), v) ->
          skipI (i - 1, I.Decl (g, Names.decEName g d), v)

    let rec skipI2 (i, g, a, b) = match i, a, b with
      | 0, v, u -> (g, v, u)
      | i, I.Pi ((d, _), v), I.Lam (d', u) ->
          skipI2 (i - 1, I.Decl (g, Names.decEName g d'), v, u)

    let rec ctxToDecList (a, l) = match a with
      | I.Null -> l
      | I.Decl (g, d) -> ctxToDecList (g, d :: l)

    let rec fmtDecList (g0, a) = match a with
      | [] -> []
      | d :: [] -> [ sym "{"; fmtDec (g0, 0, (d, I.id)); sym "}" ]
      | d :: l ->
          sym "{"
          :: fmtDec (g0, 0, (d, I.id))
          :: sym "}" :: F.break
          :: fmtDecList (I.Decl (g0, d), l)

    let fmtCtx (g0, g) = fmtDecList (g0, ctxToDecList (g, []))

    let rec fmtKindBinders (g, d, v) =
      begin match v with
      | I.Uni _ -> []
      | I.Pi ((d_, _), v2) ->
          let d' = Names.decLUName g d_ in
          let rest = fmtKindBinders (I.Decl (g, d'), d + 1, v2) in
          sym "{"
          :: fmtDec (g, d, (d', I.id))
          :: sym "}"
          :: (match rest with [] -> [] | _ -> F.break :: rest)
      | _ -> [ fmtExp (g, d, noCtxt, (v, I.id)) ]
      end

    let fmtBlock (gsome, lblock) = match gsome with
      | I.Null ->
          [ sym "block"; F.break ] @ fmtDecList (I.Null, lblock)
      | gsome ->
          [
            F.hVbox ([ sym "some"; F.space ] @ fmtCtx (I.Null, gsome));
            F.break;
            F.hVbox ([ sym "block"; F.space ] @ fmtDecList (gsome, lblock));
          ]
    (* Fix *)

    let fmtConDec (hide, a) = match a with
      | (I.ConDec (_, _, imp, _, v, l) as condec) ->
          let qid = Names.conDecQid condec in
          ignore (Names.varReset IntSyn.Null);
          let g, v =
            begin if hide then skipI (imp, I.Null, v) else (I.Null, v)
            end
          in
          begin match l with
          | I.Kind ->
              let binders = fmtKindBinders (g, 0, v) in
              F.hVbox
                ([ sym "%sort"; F.space; fmtConstPath (Symbol.const, qid) ]
                @ (if binders = [] then [] else [ F.space ])
                @ binders)
          | I.Type ->
              let vfmt = fmtExp (g, 0, noCtxt, (v, I.id)) in
              F.hVbox
                [
                  sym "%term";
                  F.space;
                  fmtConstPath (Symbol.const, qid);
                  F.space;
                  F.break;
                  vfmt;
                ]
          end
      | (I.SkoDec (_, _, imp, v, l) as condec) ->
          let qid = Names.conDecQid condec in
          ignore (Names.varReset IntSyn.Null);
          let g, v =
            begin if hide then skipI (imp, I.Null, v) else (I.Null, v)
            end
          in
          let vfmt = fmtExp (g, 0, noCtxt, (v, I.id)) in
          F.hVbox
            [
              sym "%skolem";
              F.break;
              fmtConstPath (Symbol.skonst, qid);
              F.space;
              F.break;
              vfmt;
            ]
      | (I.BlockDec (_, _, gsome, lblock) as condec) ->
          let qid = Names.conDecQid condec in
          ignore (Names.varReset IntSyn.Null);
          F.hVbox
            ([
               sym "%block";
               F.break;
               fmtConstPath (Symbol.label, qid);
               F.space;
               F.break;
             ]
            @ fmtBlock (gsome, lblock)
            @ [ full_stop ])
      | (I.BlockDef (_, _, w) as condec) ->
          let qid = Names.conDecQid condec in
          ignore (Names.varReset IntSyn.Null);
          F.hVbox
            ([
               sym "%block";
               F.break;
               fmtConstPath (Symbol.label, qid);
               F.space;
               F.break;
             ]
            @ [ formatWorlds (T.Worlds w); full_stop ])
      | (I.ConDef (_, _, imp, u, v, l, _) as condec) ->
          let qid = Names.conDecQid condec in
          ignore (Names.varReset IntSyn.Null);
          let g, v, u =
            begin if hide then skipI2 (imp, I.Null, v, u) else (I.Null, v, u)
            end
          in
          let vfmt = fmtExp (g, 0, noCtxt, (v, I.id)) in
          let ufmt = fmtExp (g, 0, noCtxt, (u, I.id)) in
          F.hVbox
            [
              sym "%def";
              F.space;
              fmtConstPath (Symbol.def, qid);
              F.space;
              F.break;
              vfmt;
              F.break;
              F.space;
              ufmt;
            ]
      | (I.AbbrevDef (_, _, imp, u, v, l) as condec) ->
          let qid = Names.conDecQid condec in
          ignore (Names.varReset IntSyn.Null);
          let g, v, u =
            begin if hide then skipI2 (imp, I.Null, v, u) else (I.Null, v, u)
            end
          in
          let vfmt = fmtExp (g, 0, noCtxt, (v, I.id)) in
          let ufmt = fmtExp (g, 0, noCtxt, (u, I.id)) in
          F.hVbox
            [
              sym "%inline";
              fmtConstPath (Symbol.def, qid);
              F.space;
              F.break;
              vfmt;
              F.break;
              F.space;
              ufmt;
            ]

    let fmtCnstr = function
      | solved -> [ str_ "Solved Constraint" ]
      | I.Eqn (g, u1, u2) ->
          let g' = Names.ctxLUName g in
          [
            F.hVbox
              [
                fmtExp (g', 0, noCtxt, (u1, I.id));
                F.break;
                sym "=";
                F.space;
                fmtExp (g', 0, noCtxt, (u2, I.id));
              ];
          ]
      | I.FgnCnstr (cs, csfc_inner) ->
          let rec fmtExpL = function
            | [] -> [ str_ "Empty Constraint" ]
            | (g, u) :: [] ->
                [ fmtExp (Names.ctxLUName g, 0, noCtxt, (u, I.id)) ]
            | (g, u) :: expL ->
                [
                  fmtExp (Names.ctxLUName g, 0, noCtxt, (u, I.id));
                  str_ ";";
                  F.break;
                ]
                @ fmtExpL expL
          in
          fmtExpL (I.FgnCnstrStd.ToInternal.apply cs csfc_inner ())

    let rec fmtCnstrL = function
      | [] -> [ str_ "Empty Constraint" ]
      | { contents = cnstr } :: [] -> fmtCnstr cnstr @ [ str_ "." ]
      | { contents = cnstr } :: cnstrL ->
          fmtCnstr cnstr @ [ str_ ";"; F.break ] @ fmtCnstrL cnstrL

    let rec abstractLam (a, u) = match a with
      | I.Null -> u
      | I.Decl (g, d) -> abstractLam (g, I.Lam (d, u))

    let fmtNamedEVar (a, name) = match a with
      | (I.EVar (_, g, _, _) as u) ->
          let u' = abstractLam (g, u) in
          F.hVbox
            [
              str0 (Symbol.evar name);
              F.space;
              sym "=";
              F.break;
              fmtExp (I.Null, 0, noCtxt, (u', I.id));
            ]
      | u ->
          F.hVbox
            [
              str0 (Symbol.evar name);
              F.space;
              sym "=";
              F.break;
              fmtExp (I.Null, 0, noCtxt, (u, I.id));
            ]

    let rec fmtEVarInst = function
      | [] -> [ str_ "Empty Substitution" ]
      | (u, name) :: [] -> [ fmtNamedEVar (u, name) ]
      | (u, name) :: xs ->
          fmtNamedEVar (u, name) :: str_ ";" :: F.break :: fmtEVarInst xs

    let rec collectEVars (a, xs) = match a with
      | [] -> xs
      | (u, _) :: xnames ->
          collectEVars (xnames, Abstract.collectEVars I.Null (u, I.id) xs)

    let eqCnstr r1 r2 = r1 == r2

    let rec mergeConstraints (a, cnstrs2) = match a with
      | [] -> cnstrs2
      | cnstr :: cnstrs1 ->
          begin if List.exists (eqCnstr cnstr) cnstrs2 then
            mergeConstraints (cnstrs1, cnstrs2)
          else cnstr :: mergeConstraints (cnstrs1, cnstrs2)
          end

    let rec collectConstraints = function
      | [] -> []
      | I.EVar ({ contents = None }, _, _, cnstrs) :: xs ->
          mergeConstraints (Constraints.simplify !cnstrs, collectConstraints xs)
      | _ :: xs -> collectConstraints xs
  end

  (* Shorthands *)
  (* Disambiguation of block logic variable names *)
  (* speed improvment possible Tue Mar  1 13:27:04 2011 --cs *)
  (* fmtEVar (G, X) = ""X"", the name of the EVar X *)
  (* Effect: Names.evarName will assign a name if X does not yet have one *)
  (* should probably be a new Symbol constructor for AVars -kw *)
  (* isNil S = true iff S == Nil *)
  (* subToSpine (depth, s) = S
     Invariants:
     If  G |- s : G', Gd  with  |Gd| = depth
     then G |- S : {{Gd}} C > C  for any C

     This is used to print
      G |- Xl[s] : A[s]  for  G', Gd |- Xl : A
     as
      G |- Xr @ S : A[s]  for  G' |- Xr : {{Gd}} A
     where Xr is the raised version of Xl.
     Xr is not actually created, just printed using the name of Xl.
  *)
  (* k >= depth *)
  (* Eta violation, but probably inconsequential -kw *)
  (* ArgStatus classifies the number of arguments to an operator *)
  (* dropImp (i, S, n) for n >= 1
     = TooFew            if |S| < i+n
     = Exact(S')         if n >= 1, |S| = i+n, S = _ @ S' and |S'| = n
                         if n = 0, |S| = _ @ S', |_| = i
     = TooMany(S', S'')  if n >=1, |S| > i+n, S = _ @ S' and |S'| > n,
                                              S' = S0 @ S'' and |S0| = n
  *)
  (* n >= 1 *)
  (* exceeded (n:int, b:bound) = true if n exceeds bound b *)
  (* Type ctxt is the ""left context"" of an expression to be printed.
     It works as an accumulator and is used to decide whether to insert of parentheses
     or elide nested subexpressions.

     Ctxt (fixity, formats, length)
     is the ""left context"" of an expression to be printed.  When printed
     it will be the string prefixed to the string representing the
     current expression.

     fixity is the operator and precedence in effect,
     formats is the list of formats which make up the left context
     length is the length of the left context (used for printLength elision)
  *)
  (* Type opargs represent the operator/arguments form of roots.

     OpArgs (fixity, formats, S)
     represents the printed form of a root expression H @ S:
      fixity is the fixity of H (possibly FX.Nonfix),
      formats is a list of formats for printing H (including surrounding breaks
         and whitespace),
      S is the spine of arguments.
      There may be additional argument in S which are ignored.

     EtaLong (U)
     represents an expression U' which had to be eta-expanded to U
     in order to supply enough arguments to a prefix, postfix, or infix operator
     so it can be printed.
  *)
  (* empty left context *)
  (* braces and brackets as a prefix operator *)
  (* colon is of FX.minPrec-2, but doesn't occur in printing *)
  (* arrow as infix operator *)
  (* juxtaposition as infix operator *)
  (* arrow (V1, V2) = oa
     where oa is the operator/argument representation of V1 -> V2
  *)
  (* Nonfix corresponds to application and therefore has precedence juxPrex (which is maximal) *)
  (* fixityCon (c) = fixity of c *)
  (* BVar, FVar *)
  (* impCon (c) = number of implicit arguments to c *)
  (* BVar, FVar *)
  (* argNumber (fixity) = number of required arguments to head with fixity *)
  (* FIX: this is certainly not correct -kw *)
  (* names should have been assigned by invar
         iant, NONE imppossible *)
  (* note: this obscures LVar identity! *)
  (* no longer Tue Mar  1 13:32:21 2011 -cs *)
  (* to be fixed --cs *)
  (* fmtCon (c) = ""c"" where the name is assigned according the the Name table
     maintained in the names module.
     FVar's are printed with a preceding ""`"" (backquote) character
  *)
  (* LVar fixed Sun Dec  1 11:36:55 2002 -cs *)
  (* will need to be changed if qualified constraint constant
             names are introduced... anyway, why should the user be
             allowed to shadow constraint constants? -kw *)
  (* the user has re-defined this name *)
  (* evarArgs (G, d, X, s)
     formats X[s] by printing X @ S, where S is the substitution s in spine form.
     This is an implicit form of raising.
  *)
  (* fst (S, s) = U1, the first argument in S[s] *)
  (* snd (S, s) = U2, the second argument in S[s] *)
  (* elide (l) = true  iff  l exceeds the optional printLength bound *)
  (* addots (l) = true  iff  l is equal to the optional printLength bound *)
  (* parens ((fixity', fixity), fmt) = fmt'
     where fmt' contains additional parentheses when the precedence of
     fixity' is greater or equal to that of fixity, otherwise it is unchanged.
  *)
  (* eqFix (fixity, fixity') = true iff fixity and fixity' have the same precedence
     Invariant: only called when precedence comparison is necessary to resolve
                the question if parentheses should be added
  *)
  (* Infix(_,None) should never be asked *)
  (* Nonfix should never be asked *)
  (* addAccum (fmt, fixity, accum) = fmt'
     Extend the current ""left context"" with operator fixity
     and format list accum by fmt.

     This is not very efficient, since the accumulator is copied
     for right associative or prefix operators.
  *)
  (* FX.Infix(None,_), FX.Nonfix should never arise *)
  (* aa (ctx, fmt) = fmt'
     Extend the current ""left context"" by fmt.
  *)
  (* fmtUni (L) = ""L"" *)
  (* impossible, included for robustness *)
  (* fmtExpW (G, d, ctx, (U, s)) = fmt

     format the expression U[s] at printing depth d and add it to the left context
     ctx.

     Invariants:
       G is a ""printing context"" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  (* if Pi is dependent but anonymous, invent name here *)
  (* could sometimes be EName *)
  (* I.decSub (D', s) *)
  (* I.decSub (D', s) *)
  (* I.decSub (D, s) *)
  (* -bp *)
  (*      val D' = Names.decLUName (G, D) *)
  (* s = id *)
  (* I.Redex not possible *)
  (* I.decSub (D', s) *)
  (* assume dereferenced during whnf *)
  (* assume dereferenced during whnf *)
  (* I.EClo not possible for Whnf *)
  (* for internal printing *)
  (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix, prefix, and postfix declarations
     are ignored.
  *)
  (* for flit printing -jcreed 6/2005 *)
  (* opargsImplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, showing all implicit
     arguments.  In this form, infix declarations are obeyed. It is an
     error to call this function if an infix declaration has been made for
     a term which has more than two arguments. (This could have happened if the term
     had two explicit arguments and further implicit arguments)

     In other words, it is an error if an infix declaration had any
     implicit arguments.
  *)
  (* Can't have implicit arguments by invariant *)
  (* for external printing *)
  (* opargsExplicit (G, (C, S)) = oa
     converts C @ S into operator/arguments form, eliding implicit
     arguments and taking operator fixity declarations into account.
     G |- C @ S (no substitution involved)
  *)
  (* extra arguments to infix operator *)
  (* S' - all non-implicit arguments *)
  (* S'' - extra arguments *)
  (* parens because juxtaposition has highest precedence *)
  (*
                 could be redundant for prefix or postfix operators, but
                 include anyway to avoid misreading output
              *)
  (* opargs (G, d, (C, S)) = oa
     converts C @ S to operator/arguments form, depending on the
     value of !implicit
  *)
  (* fmtOpArgs (G, d, ctx, oa, s) = fmt
     format the operator/arguments form oa at printing depth d and add it
     to the left context ctx.

     G is a printing context approximating G', and G' |- oa[s] is valid.
  *)
  (* opFmts = [fmtCon(G,C)] *)
  (* fmtSub (G, d, s) = fmt
     format substitution s at printing depth d and printing context G.

     This is used only when !implicit = true, that is, when the internal
     representation is printed.  Note that a substitution is not reparsable
  *)
  (* fmtExp (G, d, ctx, (U, s)) = fmt
     format or elide U[s] at printing depth d and add to the left context ctx.

     G is a printing context approximation G' and G' |- U[s] is valid.
  *)
  (* fmtSpine (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *)
  (* necessary? *)
  (* fmtSpine' (G, d, l, (S, s)) = fmts
     like fmtSpine, but will add leading ""Break"" and increment printing length
  *)
  (* fmtLevel (G, d, ctx, (oa, s)) = fmt

     format operator/arguments form oa[s] at printing depth d and add the result
     to the left context ctx.

     This is the main function flattening out infix/prefix/postfix operator
     sequences.  It compares the fixity of the operator of the current left
     context with the operator at the head of the current operator/arguments
     form and decides how to extend the accumulator and whether to insert
     parentheses.
  *)
  (* atm must not be empty, otherwise bug below *)
  (* F.hVbox doesn't work if last item of HVbox is F.break *)
  (* possible improvement along the following lines: *)
  (*
           if (#2 (F.Width (F.hbox (fmts)))) < 4
           then F.hbox [F.hbox(fmts), F.hVbox0 1 1 1 atm]
           else ...
        *)
  (* braces (G, d, ((D, V), s)) = oa
     convert declaration D[s] as a prefix pi-abstraction into operator/arguments
     form with prefix ""{D}"" and argument V at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- V : L  [NOTE: s does not apply to V!]
  *)
  (* brackets (G, d, ((D, U), s)) = oa
     convert declaration D[s] as a prefix lambda-abstraction into operator/arguments
     form with prefix ""[D]"" and argument U at printing depth d in printing
     context G approximating G'.

     Invariants:
      G' |- D[s] decl
      G' |- U : V  [NOTE: s does not apply to U!]
  *)
  (* fmtDec (G, d, (D, s)) = fmt
     format declaration D[s] at printing depth d in printing context G approximating G'.

     Invariants:
      G' |- D[s] decl
  *)
  (* alternative with more whitespace *)
  (* F.hVbox [F.string0 (Symbol.bvar (nameOf (x))), F.space, sym "":"", F.break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
  (* alternative with more whitespace *)
  (* F.hVbox [F.string0 (Symbol.bvar (nameOf (x))), F.space, sym "":"", F.break,
                  fmtExp (G, d+1, noCtxt, (V,s))]
      *)
  (* Assume unique names are already assigned in G0 and G! *)
  (* fmtConDec (hide, condec) = fmt
     formats a constant declaration (which must be closed and in normal form)

     This function prints the quantifiers and abstractions only if hide = false.
  *)
  (* reset variable names in between to align names of type V and definition U *)
  (* val _ = Names.varReset () *)
  (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.vbox0 0 1 [F.hVbox [F.string0 (Symbol.def (name)), F.space, sym "":"", F.break,
                         Vfmt, F.break,
                         sym ""="", F.space,
                         Ufmt, sym "".""],
                F.break,
                F.hVbox [sym ""%strict "", F.string0 (Symbol.def (name)), sym "".""]]
*)
  (* reset variable names in between to align names of type V and definition U *)
  (* val _ = Names.varReset () *)
  (* removed, when abbreviations where introduced. -- cs Mon Jun  7 16:03:30 EDT 1999
        F.vbox0 0 1 [F.hVbox [F.string0 (Symbol.def (name)), F.space, sym "":"", F.break,
                         Vfmt, F.break,
                         sym ""="", F.space,
                         Ufmt, sym "".""],
                F.break,
                F.hVbox [sym ""%nonstrict "", F.string0 (Symbol.def (name)), sym "".""]]
*)
  (* fmtNamedEVar, fmtEVarInst and evarInstToString are used to print
     instantiations of EVars occurring in queries.  To that end, a list of
     EVars paired with their is passed, thereby representing a substitution
     for logic variables.

     We always raise AVars to the empty context.
  *)
  (* used for proof term variables in queries *)
  (* collectEVars and collectConstraints are used to print constraints
     associated with EVars in a instantiation of variables occurring in queries.
  *)
  (* In the functions below, G must be a ""printing context"", that is,
     (a) unique names must be assigned to each declaration which may
         actually applied in the scope (typically, using Names.decName)
     (b) types need not be well-formed, since they are not used
  *)
  let formatDec g d = fmtDec (g, 0, (d, I.id))
  let formatDecList g d = F.hVbox (fmtDecList (g, d))
  let formatDecList' g (d, s) = F.hVbox (fmtDecList' (g, (d, s)))
  let formatExp g u = fmtExp (g, 0, noCtxt, (u, I.id))
  let formatSpine g s = fmtSpine (g, 0, 0, (s, I.id))
  let formatConDec condec = fmtConDec (false, condec)
  let formatConDecI condec = fmtConDec (true, condec)
  let formatCnstr cnstr = F.vbox0 0 1 (fmtCnstr cnstr)
  let formatCnstrs cnstrL = F.vbox0 0 1 (fmtCnstrL cnstrL)
  let formatCtx g0 g = F.hVbox (fmtCtx (g0, g))

  (* assumes G0 and G are named *)
  let decToString g d = F.makestring_fmt (formatDec g d)
  let expToString g u = F.makestring_fmt (formatExp g u)
  let conDecToString condec = F.makestring_fmt (formatConDec condec)
  let cnstrToString cnstr = F.makestring_fmt (formatCnstr cnstr)
  let cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
  let ctxToString g0 g = F.makestring_fmt (formatCtx g0 g)

  let evarInstToString xnames =
    F.makestring_fmt (F.hbox [ F.vbox0 0 1 (fmtEVarInst xnames); str_ "." ])

  let evarCnstrsToStringOpt xnames =
    let ys = collectEVars (xnames, []) in
    let cnstrL = collectConstraints ys in
    begin match cnstrL with [] -> None | _ -> Some (cnstrsToString cnstrL)
    end
  (* collect EVars in instantiations *)

  let printSgn () =
    IntSyn.sgnApp (function cid ->
        begin
          print (F.makestring_fmt (formatConDecI (IntSyn.sgnLookup cid)));
          print "\n"
        end)

  let formatWorlds = formatWorlds
  let worldsToString = worldsToString
end

(* local ... *)
(* functor Print *)

(* # 1 "src/print/Print_.sml.ml" *)
module SymbolAscii = Symbol.MakeSymbolAscii (struct end)
module SymbolTeX = Symbol.MakeSymbolTeX (struct end)

(*
structure WorldPrint = WorldPrint 
  (structure Global = Global
   ! structure IntSyn = IntSyn !
   ! structure Tomega' = Tomega !
   structure WorldSyn' = WorldSyn
   structure Names = Names
   structure Formatter_param = Formatter
   structure Print = Print);
*)
(* Term output now goes through [Resugar] and [Pretty]; see [PrintCst].
   [MakePrint] stays because [PrintTeX] and [ClausePrintTeX] below still use
   it, and because reverting is this one line. *)
module PrintForML =
  MakePrint (Whnf) (Abstract) (Constraints) (Names) (Formatter) (SymbolAscii)

module Print = PrintCst.Print
module ClausePrintFunctor = ClausePrint
include Print

module ClausePrint =
  ClausePrintFunctor.MakeClausePrint (Whnf) (Names) (Formatter) (Print)
    (SymbolAscii)

module PrintTeX =
  MakePrint (Whnf) (Abstract) (Constraints) (Names) (Formatter) (SymbolTeX)

module ClausePrintTeX =
  ClausePrintFunctor.MakeClausePrint (Whnf) (Names) (Formatter) (PrintTeX)
    (SymbolTeX)
