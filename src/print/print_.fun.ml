open! Symbol
open! Basis

module MakePrint (Print__0 : sig
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
end) : PRINT = struct
  (*! structure IntSyn = IntSyn' !*)
  module Formatter = struct
    include Print__0.Formatter_param
  end

  module Whnf = Print__0.Whnf
  module Abstract = Print__0.Abstract
  module Constraints = Print__0.Constraints
  module Names = Print__0.Names
  module Symbol = Print__0.Symbol
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

  (* if true, don't print shadowed constants as ""%const%"" *)
  open! struct
    module I = IntSyn
    module FX = Names.Fixity
    module F = Formatter
    module T = Tomega

    let lvars : I.block_ option ref list ref = ref []

    let rec lookuplvar l =
      let _ =
        begin if List.exists (function r -> r = l) !lvars then ()
        else lvars := !lvars @ [ l ]
        end
      in
      let rec find (r :: l_) n =
        begin if r = l then n else find l_ (n + 1)
        end
      in
      Int.toString (find !lvars 0)

    let str_ = F.string
    let rec str0_ (s, n) = F.string0 n s
    let rec sym s = str0_ (Symbol.sym s)
    let rec nameOf = function Some id -> id | None -> "_"
    let rec fmtEVar (g_, x_) = str0_ (Symbol.evar (Names.evarName (g_, x_)))

    let rec fmtAVar (g_, x_) =
      str0_ (Symbol.evar (Names.evarName (g_, x_) ^ "_"))

    let rec isNil = function
      | nil_ -> true
      | I.App _ -> false
      | I.SClo (s_, _) -> isNil s_

    let rec subToSpine (depth, s) =
      let rec sTS = function
        | I.Shift k, s_ -> begin
            if k < depth then sTS (I.Dot (I.Idx (k + 1), I.Shift (k + 1)), s_)
            else s_
          end
        | I.Dot (I.Idx k, s), s_ -> sTS (s, I.App (I.Root (I.BVar k, I.Nil), s_))
        | I.Dot (I.Exp u_, s), s_ -> sTS (s, I.App (u_, s_))
      in
      sTS (s, I.Nil)

    type argStatus_ =
      | TooFew
      | Exact of I.spine_
      | TooMany of I.spine_ * I.spine_

    let rec sclo' = function
      | TooFew, s -> TooFew
      | Exact s_, s -> Exact (I.SClo (s_, s))
      | TooMany (s_, s'_), s -> TooMany (I.SClo (s_, s), I.SClo (s'_, s))

    let rec sclo'' = function
      | TooFew, s -> TooFew
      | Exact s_, s -> Exact s_
      | TooMany (s_, s'_), s -> TooMany (s_, I.SClo (s'_, s))

    let rec dropImp = function
      | 0, s_, 0 -> Exact s_
      | 0, s_, n ->
          let rec checkArgNumber = function
            | I.Nil, 0 -> Exact s_
            | I.Nil, k -> TooFew
            | (I.App _ as s'_), 0 -> TooMany (s_, s'_)
            | I.App (u_, s'_), k -> checkArgNumber (s'_, k - 1)
            | I.SClo (s'_, s), k -> sclo'' (checkArgNumber (s'_, k), s)
          in
          checkArgNumber (s_, n)
      | i, I.App (u_, s_), n -> dropImp (i - 1, s_, n)
      | i, I.SClo (s_, s), n -> sclo' (dropImp (i, s_, n), s)
      | i, nil_, n -> TooFew

    let rec exceeded = function
      | _, None -> false
      | (n : int), Some (m : int) -> n >= m

    type ctxt = Ctxt of FX.fixity * F.format list * int

    type opargs =
      | OpArgs of FX.fixity * F.format list * I.spine_
      | EtaLong of I.exp_

    let noCtxt =
      Ctxt (FX.Prefix (FX.dec (FX.dec (FX.dec (FX.dec FX.minPrec)))), [], 0)

    let binderPrec = FX.dec (FX.dec (FX.dec FX.minPrec))
    let arrowPrec = FX.dec FX.minPrec
    let juxPrec = FX.inc FX.maxPrec

    let rec arrow (v1_, v2_) =
      OpArgs
        ( FX.Infix (arrowPrec, FX.Right),
          [ F.break; sym "->"; F.space ],
          I.App (v1_, I.App (v2_, I.Nil)) )

    let appCtxt = Ctxt (FX.Nonfix, [], 0)

    let rec fixityCon = function
      | I.Const cid -> Names.getFixity cid
      | I.Skonst cid -> FX.Nonfix
      | I.Def cid -> Names.getFixity cid
      | I.NSDef cid -> Names.getFixity cid
      | _ -> FX.Nonfix

    let rec impCon = function
      | I.Const cid -> I.constImp cid
      | I.Skonst cid -> I.constImp cid
      | I.Def cid -> I.constImp cid
      | I.NSDef cid -> I.constImp cid
      | _ -> 0

    let rec argNumber = function
      | nonfix_ -> 0
      | FX.Infix _ -> 2
      | FX.Prefix _ -> 1
      | FX.Postfix _ -> 1

    let rec fmtConstPath (f, Names.Qid (ids, id)) =
      F.hVbox
        (foldr
           (function id, fmt -> str0_ (Symbol.str id) :: sym "." :: fmt)
           [ str0_ (f id) ]
           ids)

    let rec parmDec = function
      | d_ :: l_, 1 -> d_
      | d_ :: l_, j -> parmDec (l_, j - 1)

    let rec parmName (cid, i) =
      let gsome_, gblock_ = I.constBlock cid in
      begin match parmDec (gblock_, i) with
      | I.Dec (Some pname, _) -> pname
      | I.Dec (None, _) -> Int.toString i
      end

    let rec projName = function
      | g_, I.Proj (I.Bidx k, i) ->
          let (I.BDec (Some bname, (cid, t))) = I.ctxLookup (g_, k) in
          (bname ^ "_") ^ parmName (cid, i)
      | g_, I.Proj (I.LVar (r, _, (cid, t)), i) -> "_" ^ parmName (cid, i)
      | g_, I.Proj (I.Inst iota, i) -> "*"

    let rec constQid cid =
      begin if !noShadow then Names.conDecQid (I.sgnLookup cid)
      else Names.constQid cid
      end

    let rec cidToFmt cid = F.string (Names.qidToString (Names.constQid cid))

    let rec formatCids = function
      | [] -> []
      | cid :: [] -> [ cidToFmt cid ]
      | cid :: cids ->
          cidToFmt cid :: F.break :: F.string "|" :: F.space :: formatCids cids

    let rec formatWorlds (T.Worlds cids) =
      F.hbox [ F.string "("; F.hVbox (formatCids cids); F.string ")" ]

    let rec worldsToString w_ = F.makestring_fmt (formatWorlds w_)

    let rec fmtCon = function
      | g_, I.BVar n -> str0_ (Symbol.bvar (Names.bvarName (g_, n)))
      | g_, I.Const cid -> fmtConstPath (Symbol.const, constQid cid)
      | g_, I.Skonst cid -> fmtConstPath (Symbol.skonst, constQid cid)
      | g_, I.Def cid -> fmtConstPath (Symbol.def, constQid cid)
      | g_, I.NSDef cid -> fmtConstPath (Symbol.def, constQid cid)
      | g_, I.FVar (name, _, _) -> str0_ (Symbol.fvar name)
      | g_, (I.Proj (I.Bidx k, i) as h_) ->
          str0_ (Symbol.const (projName (g_, h_)))
      | ( g_,
          (I.Proj (I.LVar (({ contents = None } as r), sk, (cid, t)), i) as h_)
        ) ->
          let n = lookuplvar r in
          fmtConstPath
            ( (function
              | l0 ->
                  Symbol.const (((("#[" ^ l0) ^ n) ^ "]") ^ projName (g_, h_))),
              constQid cid )
      | g_, I.FgnConst (cs, conDec) ->
          let name = I.conDecName conDec in
          begin match (Names.constLookup (Names.Qid ([], name)), !noShadow) with
          | Some _, false -> str0_ (Symbol.const (("%" ^ name) ^ "%"))
          | _ -> str0_ (Symbol.const name)
          end

    let rec evarArgs (g_, d, x_, s) =
      OpArgs (FX.Nonfix, [ fmtEVar (g_, x_) ], subToSpine (I.ctxLength g_, s))

    let rec evarArgs' (g_, d, x_, s) =
      OpArgs (FX.Nonfix, [ fmtAVar (g_, x_) ], subToSpine (I.ctxLength g_, s))

    let rec fst = function
      | I.App (u1_, _), s -> (u1_, s)
      | I.SClo (s_, s'), s -> fst (s_, I.comp (s', s))

    let rec snd = function
      | I.App (u1_, s_), s -> fst (s_, s)
      | I.SClo (s_, s'), s -> snd (s_, I.comp (s', s))

    let rec elide l =
      begin match !printLength with None -> false | Some l' -> l > l'
      end

    let ldots = sym "..."

    let rec addots l =
      begin match !printLength with None -> false | Some l' -> l = l'
      end

    let rec parens ((fixity', fixity), fmt) =
      begin if FX.leq (FX.prec fixity, FX.prec fixity') then
        F.hbox [ sym "("; fmt; sym ")" ]
      else fmt
      end

    let rec eqFix = function
      | FX.Infix (p, FX.Left), FX.Infix (p', FX.Left) -> p = p'
      | FX.Infix (p, FX.Right), FX.Infix (p', FX.Right) -> p = p'
      | FX.Prefix p, FX.Prefix p' -> p = p'
      | FX.Postfix p, FX.Postfix p' -> p = p'
      | _ -> false

    let rec addAccum = function
      | fmt, _, [] -> fmt
      | fmt, FX.Infix (_, left_), accum -> F.hVbox ([ fmt ] @ accum)
      | fmt, FX.Infix (_, right_), accum -> F.hVbox (accum @ [ fmt ])
      | fmt, FX.Prefix _, accum -> F.hVbox (accum @ [ fmt ])
      | fmt, FX.Postfix _, accum -> F.hVbox ([ fmt ] @ accum)

    let rec aa (Ctxt (fixity, accum, l), fmt) = addAccum (fmt, fixity, accum)
    let rec fmtUni = function I.Type -> sym "type" | I.Kind -> sym "kind"

    let rec fmtExpW = function
      | g_, d, ctx, (I.Uni l_, s) -> aa (ctx, fmtUni l_)
      | g_, d, ctx, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s) -> begin
          match p_ with
          | I.Maybe ->
              let d'_ = Names.decLUName (g_, d_) in
              fmtLevel
                ( I.Decl (g_, d'_),
                  d,
                  ctx,
                  (braces (g_, d, ((d'_, v2_), s)), I.dot1 s) )
          | meta_ ->
              let d'_ = Names.decLUName (g_, d_) in
              fmtLevel
                ( I.Decl (g_, d'_),
                  d,
                  ctx,
                  (braces (g_, d, ((d'_, v2_), s)), I.dot1 s) )
          | I.No ->
              fmtLevel
                ( I.Decl (g_, d_),
                  d,
                  ctx,
                  (arrow (I.EClo (v1_, I.shift), v2_), I.dot1 s) )
        end
      | g_, d, ctx, (I.Pi (((I.BDec _ as d_), p_), v2_), s) ->
          let d'_ = Names.decLUName (g_, d_) in
          fmtLevel
            ( I.Decl (g_, d'_),
              d,
              ctx,
              (braces (g_, d, ((d'_, v2_), s)), I.dot1 s) )
      | g_, d, ctx, (I.Pi (((I.ADec _ as d_), p_), v2_), s) ->
          let braces =
            OpArgs
              ( FX.Prefix binderPrec,
                [ sym "["; sym "_"; sym "]"; F.break ],
                IntSyn.App (v2_, IntSyn.Nil) )
          in
          fmtLevel (I.Decl (g_, d_), d, ctx, (braces, I.dot1 s))
      | g_, d, ctx, ((I.Root (h_r_, sp_r_) as u_), s) ->
          fmtOpArgs (g_, d, ctx, opargs (g_, d, (h_r_, sp_r_)), s)
      | g_, d, ctx, (I.Lam (d_, u_), s) ->
          let d'_ = Names.decLUName (g_, d_) in
          fmtLevel
            ( I.Decl (g_, d'_),
              d,
              ctx,
              (brackets (g_, d, ((d'_, u_), s)), I.dot1 s) )
      | g_, d, ctx, ((I.EVar _ as x_), s) -> begin
          if !implicit then
            aa (ctx, F.hVbox (fmtEVar (g_, x_) :: fmtSub (g_, d, s)))
          else fmtOpArgs (g_, d, ctx, evarArgs (g_, d, x_, s), I.id)
        end
      | g_, d, ctx, ((I.AVar _ as x_), s) -> begin
          if !implicit then
            aa (ctx, F.hVbox (fmtAVar (g_, x_) :: fmtSub (g_, d, s)))
          else fmtOpArgs (g_, d, ctx, evarArgs' (g_, d, x_, s), I.id)
        end
      | g_, d, ctx, ((I.FgnExp (cs_fe, fe_fe) as u_), s) ->
          fmtExp
            (g_, d, ctx, (I.FgnExpStd.ToInternal.apply (cs_fe, fe_fe) (), s))

    and opargsImplicit (g_, d, (c_, s_)) =
      OpArgs (FX.Nonfix, [ fmtCon (g_, c_) ], s_)

    and opargsImplicitInfix (g_, d, ((c_, s_) as r_)) =
      let fixity = fixityCon c_ in
      begin match fixity with
      | FX.Infix _ -> opargsExplicit (g_, d, r_)
      | _ -> OpArgs (FX.Nonfix, [ fmtCon (g_, c_) ], s_)
      end

    and opargsExplicit (g_, d, ((c_, s_) as r_)) =
      let opFmt = fmtCon (g_, c_) in
      let fixity = fixityCon c_ in
      let rec oe = function
        | Exact s'_ -> begin
            match fixity with
            | nonfix_ -> OpArgs (FX.Nonfix, [ opFmt ], s'_)
            | FX.Prefix _ -> OpArgs (fixity, [ opFmt; F.break ], s'_)
            | FX.Postfix _ -> OpArgs (fixity, [ F.break; opFmt ], s'_)
            | FX.Infix _ -> OpArgs (fixity, [ F.break; opFmt; F.space ], s'_)
          end
        | TooFew -> EtaLong (Whnf.etaExpandRoot (I.Root (c_, s_)))
        | TooMany (s'_, s''_) ->
            let opFmt' = fmtOpArgs (g_, d, noCtxt, oe (Exact s'_), I.id) in
            OpArgs (FX.Nonfix, [ F.hbox [ sym "("; opFmt'; sym ")" ] ], s''_)
      in
      oe (dropImp (impCon c_, s_, argNumber fixity))

    and opargs (g_, d, r_) =
      begin if !implicit then begin
        if !printInfix then opargsImplicitInfix (g_, d, r_)
        else opargsImplicit (g_, d, r_)
      end
      else opargsExplicit (g_, d, r_)
      end

    and fmtOpArgs = function
      | g_, d, ctx, (OpArgs (_, opFmts, s'_) as oa), s -> begin
          if isNil s'_ then aa (ctx, List.hd opFmts)
          else fmtLevel (g_, d, ctx, (oa, s))
        end
      | g_, d, ctx, EtaLong u'_, s -> fmtExpW (g_, d, ctx, (u'_, s))

    and fmtSub (g_, d, s) = str_ "[" :: fmtSub' (g_, d, 0, s)

    and fmtSub' (g_, d, l, s) =
      begin if elide l then [ ldots ] else fmtSub'' (g_, d, l, s)
      end

    and fmtSub'' = function
      | g_, d, l, I.Shift k -> [ str_ ("^" ^ Int.toString k); str_ "]" ]
      | g_, d, l, I.Dot (I.Idx k, s) ->
          str_ (Names.bvarName (g_, k))
          :: str_ "." :: F.break
          :: fmtSub' (g_, d, l + 1, s)
      | g_, d, l, I.Dot (I.Exp u_, s) ->
          fmtExp (g_, d + 1, noCtxt, (u_, I.id))
          :: str_ "." :: F.break
          :: fmtSub' (g_, d, l + 1, s)

    and fmtExp (g_, d, ctx, (u_, s)) =
      begin if exceeded (d, !printDepth) then sym "%%"
      else fmtExpW (g_, d, ctx, Whnf.whnf (u_, s))
      end

    and fmtSpine = function
      | g_, d, l, (I.Nil, _) -> []
      | g_, d, l, (I.SClo (s_, s'), s) ->
          fmtSpine (g_, d, l, (s_, I.comp (s', s)))
      | g_, d, l, (I.App (u_, s_), s) -> begin
          if elide l then []
          else begin
            if addots l then [ ldots ]
            else
              fmtExp (g_, d + 1, appCtxt, (u_, s))
              :: fmtSpine' (g_, d, l, (s_, s))
          end
        end

    and fmtSpine' = function
      | g_, d, l, (I.Nil, _) -> []
      | g_, d, l, (I.SClo (s_, s'), s) ->
          fmtSpine' (g_, d, l, (s_, I.comp (s', s)))
      | g_, d, l, (s_, s) -> F.break :: fmtSpine (g_, d, l + 1, (s_, s))

    and fmtLevel = function
      | ( g_,
          d,
          Ctxt (fixity', accum, l),
          (OpArgs ((nonfix_ as fixity), fmts, s_), s) ) ->
          let atm = fmtSpine (g_, d, 0, (s_, s)) in
          addAccum
            ( parens ((fixity', fixity), F.hVbox (fmts @ [ F.break ] @ atm)),
              fixity',
              accum )
      | ( g_,
          d,
          Ctxt (fixity', accum, l),
          (OpArgs ((FX.Infix (p, left_) as fixity), fmts, s_), s) ) ->
          let accMore = eqFix (fixity, fixity') in
          let rhs =
            begin if accMore && elide l then []
            else begin
              if accMore && addots l then fmts @ [ ldots ]
              else
                fmts
                @ [
                    fmtExp
                      ( g_,
                        d + 1,
                        Ctxt (FX.Infix (p, FX.None), [], 0),
                        snd (s_, s) );
                  ]
            end
            end
          in
          begin if accMore then
            fmtExp (g_, d, Ctxt (fixity, rhs @ accum, l + 1), fst (s_, s))
          else
            let both = fmtExp (g_, d, Ctxt (fixity, rhs, 0), fst (s_, s)) in
            addAccum (parens ((fixity', fixity), both), fixity', accum)
          end
      | ( g_,
          d,
          Ctxt (fixity', accum, l),
          (OpArgs ((FX.Infix (p, right_) as fixity), fmts, s_), s) ) ->
          let accMore = eqFix (fixity, fixity') in
          let lhs =
            begin if accMore && elide l then []
            else begin
              if accMore && addots l then [ ldots ] @ fmts
              else
                [
                  fmtExp
                    (g_, d + 1, Ctxt (FX.Infix (p, FX.None), [], 0), fst (s_, s));
                ]
                @ fmts
            end
            end
          in
          begin if accMore then
            fmtExp (g_, d, Ctxt (fixity, accum @ lhs, l + 1), snd (s_, s))
          else
            let both = fmtExp (g_, d, Ctxt (fixity, lhs, 0), snd (s_, s)) in
            addAccum (parens ((fixity', fixity), both), fixity', accum)
          end
      | ( g_,
          d,
          Ctxt (fixity', accum, l),
          (OpArgs ((FX.Infix (_, none_) as fixity), fmts, s_), s) ) ->
          let lhs = fmtExp (g_, d + 1, Ctxt (fixity, [], 0), fst (s_, s)) in
          let rhs = fmtExp (g_, d + 1, Ctxt (fixity, [], 0), snd (s_, s)) in
          addAccum
            ( parens ((fixity', fixity), F.hVbox ([ lhs ] @ fmts @ [ rhs ])),
              fixity',
              accum )
      | ( g_,
          d,
          Ctxt (fixity', accum, l),
          (OpArgs ((FX.Prefix _ as fixity), fmts, s_), s) ) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            begin if accMore && elide l then []
            else begin
              if accMore && addots l then [ ldots; F.break ] else fmts
            end
            end
          in
          begin if accMore then
            fmtExp (g_, d, Ctxt (fixity, accum @ pfx, l + 1), fst (s_, s))
          else
            let whole = fmtExp (g_, d, Ctxt (fixity, pfx, 0), fst (s_, s)) in
            addAccum (parens ((fixity', fixity), whole), fixity', accum)
          end
      | ( g_,
          d,
          Ctxt (fixity', accum, l),
          (OpArgs ((FX.Postfix _ as fixity), fmts, s_), s) ) ->
          let accMore = eqFix (fixity', fixity) in
          let pfx =
            begin if accMore && elide l then []
            else begin
              if accMore && addots l then [ F.break; ldots ] else fmts
            end
            end
          in
          begin if accMore then
            fmtExp (g_, d, Ctxt (fixity, pfx @ accum, l + 1), fst (s_, s))
          else
            let whole = fmtExp (g_, d, Ctxt (fixity, pfx, 0), fst (s_, s)) in
            addAccum (parens ((fixity', fixity), whole), fixity', accum)
          end

    and braces (g_, d, ((d_, v_), s)) =
      OpArgs
        ( FX.Prefix binderPrec,
          [ sym "{"; fmtDec (g_, d, (d_, s)); sym "}"; F.break ],
          IntSyn.App (v_, IntSyn.Nil) )

    and brackets (g_, d, ((d_, u_), s)) =
      OpArgs
        ( FX.Prefix binderPrec,
          [ sym "["; fmtDec (g_, d, (d_, s)); sym "]"; F.break ],
          IntSyn.App (u_, IntSyn.Nil) )

    and fmtDec = function
      | g_, d, (I.Dec (x, v_), s) ->
          F.hVbox
            [
              str0_ (Symbol.bvar (nameOf x));
              sym ":";
              fmtExp (g_, d + 1, noCtxt, (v_, s));
            ]
      | g_, d, (I.BDec (x, (cid, t)), s) ->
          let gsome_, gblock_ = I.constBlock cid in
          F.hVbox
            ([ str0_ (Symbol.const (nameOf x)); sym ":" ]
            @ fmtDecList' (g_, (gblock_, I.comp (t, s))))
      | g_, d, (I.ADec (x, _), s) ->
          F.hVbox [ str0_ (Symbol.bvar (nameOf x)); sym ":_" ]
      | g_, d, (I.NDec (Some name), s) -> F.hVbox [ sym name ]

    and fmtDecList' = function
      | g0_, ([], s) -> []
      | g0_, (d_ :: [], s) -> [ sym "{"; fmtDec (g0_, 0, (d_, s)); sym "}" ]
      | g0_, (d_ :: l_, s) ->
          sym "{"
          :: fmtDec (g0_, 0, (d_, s))
          :: sym "}" :: F.break
          :: fmtDecList' (I.Decl (g0_, d_), (l_, I.dot1 s))

    let rec skipI = function
      | 0, g_, v_ -> (g_, v_)
      | i, g_, I.Pi ((d_, _), v_) ->
          skipI (i - 1, I.Decl (g_, Names.decEName (g_, d_)), v_)

    let rec skipI2 = function
      | 0, g_, v_, u_ -> (g_, v_, u_)
      | i, g_, I.Pi ((d_, _), v_), I.Lam (d'_, u_) ->
          skipI2 (i - 1, I.Decl (g_, Names.decEName (g_, d'_)), v_, u_)

    let rec ctxToDecList = function
      | null_, l_ -> l_
      | I.Decl (g_, d_), l_ -> ctxToDecList (g_, d_ :: l_)

    let rec fmtDecList = function
      | g0_, [] -> []
      | g0_, d_ :: [] -> [ sym "{"; fmtDec (g0_, 0, (d_, I.id)); sym "}" ]
      | g0_, d_ :: l_ ->
          sym "{"
          :: fmtDec (g0_, 0, (d_, I.id))
          :: sym "}" :: F.break
          :: fmtDecList (I.Decl (g0_, d_), l_)

    let rec fmtCtx (g0_, g_) = fmtDecList (g0_, ctxToDecList (g_, []))

    let rec fmtBlock = function
      | null_, lblock_ -> [ sym "block"; F.break ] @ fmtDecList (I.Null, lblock_)
      | gsome_, lblock_ ->
          [
            F.hVbox ([ sym "some"; F.space ] @ fmtCtx (I.Null, gsome_));
            F.break;
            F.hVbox ([ sym "block"; F.space ] @ fmtDecList (gsome_, lblock_));
          ]

    let rec fmtConDec = function
      | hide, (I.ConDec (_, _, imp, _, v_, l_) as condec) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let g_, v_ =
            begin if hide then skipI (imp, I.Null, v_) else (I.Null, v_)
            end
          in
          let vfmt_ = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
          F.hVbox
            [
              fmtConstPath (Symbol.const, qid);
              F.space;
              sym ":";
              F.break;
              vfmt_;
              sym ".";
            ]
      | hide, (I.SkoDec (_, _, imp, v_, l_) as condec) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let g_, v_ =
            begin if hide then skipI (imp, I.Null, v_) else (I.Null, v_)
            end
          in
          let vfmt_ = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
          F.hVbox
            [
              sym "%skolem";
              F.break;
              fmtConstPath (Symbol.skonst, qid);
              F.space;
              sym ":";
              F.break;
              vfmt_;
              sym ".";
            ]
      | hide, (I.BlockDec (_, _, gsome_, lblock_) as condec) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.hVbox
            ([
               sym "%block";
               F.break;
               fmtConstPath (Symbol.label, qid);
               F.space;
               sym ":";
               F.break;
             ]
            @ fmtBlock (gsome_, lblock_)
            @ [ sym "." ])
      | hide, (I.BlockDef (_, _, w_) as condec) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          F.hVbox
            ([
               sym "%block";
               F.break;
               fmtConstPath (Symbol.label, qid);
               F.space;
               sym "=";
               F.break;
             ]
            @ [ formatWorlds (T.Worlds w_); sym "." ])
      | hide, (I.ConDef (_, _, imp, u_, v_, l_, _) as condec) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let g_, v_, u_ =
            begin if hide then skipI2 (imp, I.Null, v_, u_) else (I.Null, v_, u_)
            end
          in
          let vfmt_ = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
          let ufmt_ = fmtExp (g_, 0, noCtxt, (u_, I.id)) in
          F.hVbox
            [
              fmtConstPath (Symbol.def, qid);
              F.space;
              sym ":";
              F.break;
              vfmt_;
              F.break;
              sym "=";
              F.space;
              ufmt_;
              sym ".";
            ]
      | hide, (I.AbbrevDef (_, _, imp, u_, v_, l_) as condec) ->
          let qid = Names.conDecQid condec in
          let _ = Names.varReset IntSyn.Null in
          let g_, v_, u_ =
            begin if hide then skipI2 (imp, I.Null, v_, u_) else (I.Null, v_, u_)
            end
          in
          let vfmt_ = fmtExp (g_, 0, noCtxt, (v_, I.id)) in
          let ufmt_ = fmtExp (g_, 0, noCtxt, (u_, I.id)) in
          F.hVbox
            [
              fmtConstPath (Symbol.def, qid);
              F.space;
              sym ":";
              F.break;
              vfmt_;
              F.break;
              sym "=";
              F.space;
              ufmt_;
              sym ".";
            ]

    let rec fmtCnstr = function
      | solved_ -> [ str_ "Solved Constraint" ]
      | I.Eqn (g_, u1_, u2_) ->
          let g'_ = Names.ctxLUName g_ in
          [
            F.hVbox
              [
                fmtExp (g'_, 0, noCtxt, (u1_, I.id));
                F.break;
                sym "=";
                F.space;
                fmtExp (g'_, 0, noCtxt, (u2_, I.id));
              ];
          ]
      | I.FgnCnstr (cs, csfc_inner) ->
          let rec fmtExpL = function
            | [] -> [ str_ "Empty Constraint" ]
            | (g_, u_) :: [] ->
                [ fmtExp (Names.ctxLUName g_, 0, noCtxt, (u_, I.id)) ]
            | (g_, u_) :: expL ->
                [
                  fmtExp (Names.ctxLUName g_, 0, noCtxt, (u_, I.id));
                  str_ ";";
                  F.break;
                ]
                @ fmtExpL expL
          in
          fmtExpL (I.FgnCnstrStd.ToInternal.apply (cs, csfc_inner) ())

    let rec fmtCnstrL = function
      | [] -> [ str_ "Empty Constraint" ]
      | { contents = cnstr_ } :: [] -> fmtCnstr cnstr_ @ [ str_ "." ]
      | { contents = cnstr_ } :: cnstrL ->
          fmtCnstr cnstr_ @ [ str_ ";"; F.break ] @ fmtCnstrL cnstrL

    let rec abstractLam = function
      | null_, u_ -> u_
      | I.Decl (g_, d_), u_ -> abstractLam (g_, I.Lam (d_, u_))

    let rec fmtNamedEVar = function
      | (I.EVar (_, g_, _, _) as u_), name ->
          let u'_ = abstractLam (g_, u_) in
          F.hVbox
            [
              str0_ (Symbol.evar name);
              F.space;
              sym "=";
              F.break;
              fmtExp (I.Null, 0, noCtxt, (u'_, I.id));
            ]
      | u_, name ->
          F.hVbox
            [
              str0_ (Symbol.evar name);
              F.space;
              sym "=";
              F.break;
              fmtExp (I.Null, 0, noCtxt, (u_, I.id));
            ]

    let rec fmtEVarInst = function
      | [] -> [ str_ "Empty Substitution" ]
      | (u_, name) :: [] -> [ fmtNamedEVar (u_, name) ]
      | (u_, name) :: xs_ ->
          fmtNamedEVar (u_, name) :: str_ ";" :: F.break :: fmtEVarInst xs_

    let rec collectEVars = function
      | [], xs_ -> xs_
      | (u_, _) :: xnames_, xs_ ->
          collectEVars (xnames_, Abstract.collectEVars (I.Null, (u_, I.id), xs_))

    let rec eqCnstr r1 r2 = r1 = r2

    let rec mergeConstraints = function
      | [], cnstrs2 -> cnstrs2
      | cnstr :: cnstrs1, cnstrs2 -> begin
          if List.exists (eqCnstr cnstr) cnstrs2 then
            mergeConstraints (cnstrs1, cnstrs2)
          else cnstr :: mergeConstraints (cnstrs1, cnstrs2)
        end

    let rec collectConstraints = function
      | [] -> []
      | I.EVar ({ contents = None }, _, _, cnstrs) :: xs_ ->
          mergeConstraints (Constraints.simplify !cnstrs, collectConstraints xs_)
      | _ :: xs_ -> collectConstraints xs_
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
  let rec formatDec (g_, d_) = fmtDec (g_, 0, (d_, I.id))
  let rec formatDecList (g_, d_) = F.hVbox (fmtDecList (g_, d_))
  let rec formatDecList' (g_, (d_, s)) = F.hVbox (fmtDecList' (g_, (d_, s)))
  let rec formatExp (g_, u_) = fmtExp (g_, 0, noCtxt, (u_, I.id))
  let rec formatSpine (g_, s_) = fmtSpine (g_, 0, 0, (s_, I.id))
  let rec formatConDec condec_ = fmtConDec (false, condec_)
  let rec formatConDecI condec_ = fmtConDec (true, condec_)
  let rec formatCnstr cnstr_ = F.vbox0 0 1 (fmtCnstr cnstr_)
  let rec formatCnstrs cnstrL = F.vbox0 0 1 (fmtCnstrL cnstrL)
  let rec formatCtx (g0_, g_) = F.hVbox (fmtCtx (g0_, g_))

  (* assumes G0 and G are named *)
  let rec decToString (g_, d_) = F.makestring_fmt (formatDec (g_, d_))
  let rec expToString (g_, u_) = F.makestring_fmt (formatExp (g_, u_))
  let rec conDecToString condec_ = F.makestring_fmt (formatConDec condec_)
  let rec cnstrToString cnstr_ = F.makestring_fmt (formatCnstr cnstr_)
  let rec cnstrsToString cnstrL = F.makestring_fmt (formatCnstrs cnstrL)
  let rec ctxToString (g0_, g_) = F.makestring_fmt (formatCtx (g0_, g_))

  let rec evarInstToString xnames_ =
    F.makestring_fmt (F.hbox [ F.vbox0 0 1 (fmtEVarInst xnames_); str_ "." ])

  let rec evarCnstrsToStringOpt xnames_ =
    let ys_ = collectEVars (xnames_, []) in
    let cnstrL = collectConstraints ys_ in
    begin match cnstrL with [] -> None | _ -> Some (cnstrsToString cnstrL)
    end
  (* collect EVars in instantiations *)

  let rec printSgn () =
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
