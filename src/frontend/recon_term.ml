(* # 1 "src/frontend/recon_term.sig.ml" *)
open! Basis

(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)
(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)
include Recon_term_intf
(* id | _  (type omitted) *)
(* signature EXTSYN *)
(* signature RECON_TERM
   provides the interface to type reconstruction seen by Stelf 
*)
(* signature RECON_TERM *)

(* # 1 "src/frontend/recon_term.fun.ml" *)
open! Basis

(* Type Reconstruction with Tracing *)
(* Author: Kevin Watkins *)
(* Based on a previous implementation by Frank Pfenning *)
(* with modifications by Jeff Polakow and Roberto Virga *)
(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)
module ReconTerm (ReconTerm__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! structure Paths' : PATHS !*)
  module Approx : APPROX

  (*! sharing Approx.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn' !*)
  module StringTree : TABLE with type key = string
  module Msg : MSG
end) : RECON_TERM = struct
  module Names = ReconTerm__0.Names
  module Approx = ReconTerm__0.Approx
  module Whnf = ReconTerm__0.Whnf
  module Unify = ReconTerm__0.Unify
  module Abstract = ReconTerm__0.Abstract
  module Print = ReconTerm__0.Print
  module StringTree = ReconTerm__0.StringTree
  module Msg = ReconTerm__0.Msg
  module F = Print.Formatter
  module Apx = Approx

  (* Error handling *)
  let delayedList : (unit -> unit) list ref = ref []
  let rec clearDelayed () = delayedList := []
  let rec addDelayed f = delayedList := f :: !delayedList

  let rec runDelayed () =
    let rec run' = function
      | [] -> ()
      | h :: t -> begin
          run' t;
          h ()
        end
    in
    run' !delayedList

  exception Error of string

  let errorCount = ref 0
  let errorFileName = ref "no file"
  let errorThreshold = ref (Some 20)
  let exceeds = function i, None -> false | i, Some j -> i > j

  let rec resetErrors fileName =
    begin
      errorCount := 0;
      errorFileName := fileName
    end

  let rec die r =
    raise
      (Error
         (Paths.wrap
            ( r,
              (((" " ^ Int.toString !errorCount) ^ " error")
              ^ begin if !errorCount > 1 then "s" else ""
              end)
              ^ " found" )))

  let rec checkErrors r =
    begin if !errorCount > 0 then die r else ()
    end

  (* Since this structure uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the ""[Loading file ..."" message and the closing ""]"",
     instead of after the closing ""]"".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same line
     as ""[Loading file ..."", terribly confusing the Emacs error parsing code.
   *)
  let rec chatterOneNewline () =
    begin if !Global.chatter = 1 && !errorCount = 1 then Msg.message "\n"
    else ()
    end

  let rec fatalError (r, msg) =
    begin
      errorCount := !errorCount + 1;
      begin
        chatterOneNewline ();
        begin
          Msg.message (((!errorFileName ^ ":") ^ Paths.wrap (r, msg)) ^ "\n");
          die r
        end
      end
    end

  let rec error (r, msg) =
    begin
      errorCount := !errorCount + 1;
      begin
        chatterOneNewline ();
        begin
          Msg.message (((!errorFileName ^ ":") ^ Paths.wrap (r, msg)) ^ "\n");
          begin if exceeds (!errorCount, !errorThreshold) then die r else ()
          end
        end
      end
    end

  let rec formatExp (g_, u_) =
    try Print.formatExp (g_, u_)
    with unprintable_ -> F.string "%_unprintable_%"

  (* this is a hack, i know *)
  let queryMode = ref false

  open! struct
    open IntSyn
  end

  let decl_ = function g_, d_ -> IntSyn.Decl (g_, d_)
  let eClo_ = function v_, s -> IntSyn.EClo (v_, s)
  let root_ = function h_, s_ -> IntSyn.Root (h_, s_)
  let rec bVar_ n = IntSyn.BVar n
  let redex_ = function u_, s_ -> IntSyn.Redex (u_, s_)
  let fVar_ = function name, v_, s -> IntSyn.FVar (name, v_, s)
  let rec exp_ u_ = IntSyn.Exp u_
  let undefined_ = Apx.Undefined
  let rec uni_ l_ = Apx.Uni (Apx.uniToApx l_)
  let kind_ = Apx.kind
  let hyperkind_ = Apx.hyperkind
  let rec next_ l_ = Apx.Next l_

  let rec headConDec (h_ : IntSyn.head) =
    begin match h_ with
    | IntSyn.Const c -> IntSyn.sgnLookup c
    | IntSyn.Skonst c -> IntSyn.sgnLookup c
    | IntSyn.Def d -> IntSyn.sgnLookup d
    | IntSyn.NSDef d -> IntSyn.sgnLookup d
    | IntSyn.FgnConst (_, cd) -> cd
    end

  (* others impossible by invariant *)
  (* lowerType (G, (V, s)) = (G', a)
     if   G0 |- V : type and G |- s : G0
     and  G |- V[s] = {{G1}} a : type
     then G' = G, G1 *)
  let rec lowerTypeW = function
    | g_, (IntSyn.Pi ((d_, _), v_), s) ->
        let d'_ = IntSyn.decSub (d_, s) in
        lowerType (decl_ (g_, d'_), (v_, IntSyn.dot1 s))
    | g_, vs_ -> (g_, eClo_ vs_)

  and lowerType (g_, vs_) = lowerTypeW (g_, Whnf.whnfExpandDef vs_)

  (* raiseType (G, V) = {{G}} V *)
  let rec raiseType = function
    | IntSyn.Null, v_ -> v_
    | IntSyn.Decl (g_, d_), v_ ->
        raiseType (g_, IntSyn.Pi ((d_, IntSyn.Maybe), v_))

  (* open IntSyn *)
  let evarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarTable : IntSyn.exp StringTree.table = StringTree.new_ 0

  let varReset () =
    StringTree.clear evarApxTable;
    StringTree.clear fvarApxTable;
    StringTree.clear fvarTable

  let fvarApxTable_ref_check () = fvarApxTable

  let rec getEVarTypeApx name =
    begin match StringTree.lookup evarApxTable name with
    | Some v_ -> v_
    | None -> begin
        match Names.getEVarOpt name with
        | Some (IntSyn.EVar (_, _, v_, _)) ->
            let v'_, _ (* Type *) = Apx.classToApx v_ in
            begin
              StringTree.insert evarApxTable (name, v'_);
              v'_
            end
        | None ->
            let v_ = Apx.newCVar () in
            begin
              StringTree.insert evarApxTable (name, v_);
              v_
            end
      end
    end

  let rec getFVarTypeApx name =
    begin match StringTree.lookup fvarApxTable name with
    | Some v_ ->
        Logs.debug (fun m -> m "getFVarTypeApx: found existing for %s" name);
        v_
    | None ->
        let v_ = Apx.newCVar () in
        Logs.debug (fun m ->
            m "getFVarTypeApx: creating fresh CVar for %s" name);
        begin
          StringTree.insert fvarApxTable (name, v_);
          v_
        end
    end

  let rec getEVar (name, allowed) =
    begin match Names.getEVarOpt name with
    | Some (IntSyn.EVar (_, g_, v_, _) as x_) -> (x_, raiseType (g_, v_))
    | None ->
        let v_ = Option.valOf (StringTree.lookup evarApxTable name) in
        let v'_ = Apx.apxToClass (IntSyn.Null, v_, Apx.(Level 1), allowed) in
        let g''_, v''_ = lowerType (IntSyn.Null, (v'_, IntSyn.id)) in
        let x_ = IntSyn.newEVar (g''_, v''_) in
        begin
          Names.addEVar (x_, name);
          (x_, v'_)
        end
    end

  let rec getFVarType (name, allowed) =
    begin match StringTree.lookup fvarTable name with
    | Some v_ -> v_
    | None ->
        let v_ = Option.valOf (StringTree.lookup fvarApxTable name) in
        let v'_ = Apx.apxToClass (IntSyn.Null, v_, Apx.(Level 1), allowed) in
        begin
          StringTree.insert fvarTable (name, v'_);
          v'_
        end
    end

  (* External syntax of terms *)
  type term =
    | Internal_ of IntSyn.exp * IntSyn.exp * Paths.region
    | Constant_ of IntSyn.head * Paths.region
    | Bvar_ of int * Paths.region
    | Evar_ of string * Paths.region
    | Fvar_ of string * Paths.region
    | Typ_ of Paths.region
    | Arrow_ of term * term
    | Pi_ of dec * term
    | Lam_ of dec * term
    | App_ of term * term
    | Hastype_ of term * term
    | Mismatch_ of term * term * string * string
    | Omitted_ of Paths.region
    | Lcid_ of string list * string * Paths.region
    | Ucid_ of string list * string * Paths.region
    | Quid_ of string list * string * Paths.region
    | Scon_ of string * Paths.region
    | Omitapx_ of Apx.exp * Apx.exp * Apx.uni * Paths.region
    | Omitexact_ of IntSyn.exp * IntSyn.exp * Paths.region
  [@@deriving show]

  and dec = Dec_ of string option * term * Paths.region

  let rec lcid (ids, name, r) = Lcid_ (ids, name, r)
  let rec ucid (ids, name, r) = Ucid_ (ids, name, r)
  let rec quid (ids, name, r) = Quid_ (ids, name, r)
  let rec scon (value, r) = Scon_ (value, r)
  let rec evar (name, r) = Evar_ (name, r)
  let rec fvar (name, r) = Fvar_ (name, r)
  let rec typ r = Typ_ r
  let rec arrow (tm1, tm2) = Arrow_ (tm1, tm2)
  let rec pi (d, tm) = Pi_ (d, tm)
  let rec lam (d, tm) = Lam_ (d, tm)
  let rec app (tm1, tm2) = App_ (tm1, tm2)
  let rec hastype (tm1, tm2) = Hastype_ (tm1, tm2)
  let rec omitted r = Omitted_ r
  let rec dec (nameOpt, tm, r) = Dec_ (nameOpt, tm, r)

  (* (U, V, r) *)
  (* G |- U : V nf where V : L or V == kind *)
  (* not used currently *)
  (* must be Const/Skonst/Def/NSDef/FgnConst *)
  (* (original, replacement, location, problem) *)
  (* Phase 1 only *)
  (* Phase 2 only *)
  (* (U, V, L, r) where U ~:~ V ~:~ L *)
  (* U undefined unless L >= kind *)
  (* Phase 3 only *)
  let rec backarrow (tm1, tm2) = Arrow_ (tm2, tm1)

  (* for now *)
  let rec dec0 (nameOpt, r) = Dec_ (nameOpt, Omitted_ r, r)

  type job =
    | Jnothing_
    | Jand_ of job * job
    | Jwithctx_ of dec IntSyn.ctx * job
    | Jterm_ of term
    | Jclass_ of term
    | Jof_ of term * term
    | Jof'_ of term * IntSyn.exp

  let jnothing = Jnothing_
  let rec jand (j1, j2) = Jand_ (j1, j2)
  let rec jwithctx (g, j) = Jwithctx_ (g, j)
  let rec jterm tm = Jterm_ tm
  let rec jclass tm = Jclass_ tm
  let rec jof (tm1, tm2) = Jof_ (tm1, tm2)
  let rec jof' (tm, v_) = Jof'_ (tm, v_)

  let rec termRegion = function
    | Internal_ (u_, v_, r) -> r
    | Constant_ (h_, r) -> r
    | Bvar_ (k, r) -> r
    | Evar_ (name, r) -> r
    | Fvar_ (name, r) -> r
    | Typ_ r -> r
    | Arrow_ (tm1, tm2) -> Paths.join (termRegion tm1, termRegion tm2)
    | Pi_ (tm1, tm2) -> Paths.join (decRegion tm1, termRegion tm2)
    | Lam_ (tm1, tm2) -> Paths.join (decRegion tm1, termRegion tm2)
    | App_ (tm1, tm2) -> Paths.join (termRegion tm1, termRegion tm2)
    | Hastype_ (tm1, tm2) -> Paths.join (termRegion tm1, termRegion tm2)
    | Mismatch_ (tm1, tm2, _, _) -> termRegion tm2
    | Omitted_ r -> r
    | Lcid_ (_, _, r) -> r
    | Ucid_ (_, _, r) -> r
    | Quid_ (_, _, r) -> r
    | Scon_ (_, r) -> r
    | Omitapx_ (u_, v_, l_, r) -> r
    | Omitexact_ (u_, v_, r) -> r

  and decRegion (Dec_ (name, tm, r)) = r

  let rec ctxRegion = function
    | IntSyn.Null -> None
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, decRegion tm)

  and ctxRegion' = function
    | IntSyn.Null, r -> Some r
    | IntSyn.Decl (g, tm), r -> ctxRegion' (g, Paths.join (r, decRegion tm))

  type apx_dec = Dec of string option * Apx.exp | NDec of string option
  type apx_ctx = apx_dec IntSyn.ctx

  open Apx

  (* Phase 1:
       Try to determine an approximate type/kind and level for each subterm.
       In cases where there's a mismatch, it's generally better not to report
       it immediately, but rather to wait until after the exact phase, so that
       the error message can mention more precise type information.  So instead
       the bad subterm is wrapped in a `mismatch' constructor, which also
       supplies a replacement (always an `omitted' in the current implementation)
       so that the invariant that the entire term is approximately well-typed
       after phase 1 is satisfied even in the presence of the error.
     *)
  (* inferApx (G, tm, false) = (tm', U, V, L)
       pre: G is an approximate context
            tm is an approximate subject
       post: tm' is an approximate subject
             U is an approximate subject
             V is an approximate classifier
             L is an approximate universe
             G |- U ~:~ V ~:~ L
             termToExp tm' = U

       inferApx (G, tm, true) = (tm', U, V, L)
       pre: G is an approximate context
            tm is an approximate classifier
       post: tm' is an approximate classifier
             U is an approximate classifier
             V is an approximate classifier
             L is an approximate universe
             G |- U ~:~ V ~:~ L
             termToExp tm' = U
     *)
  let rec filterLevel (tm, l_, max, msg) =
    let notGround = Apx.makeGroundUni l_ in
    let (Apx.Level i) = Apx.whnfUni l_ in
    begin if i > max then fatalError (termRegion tm, "Level too high\n" ^ msg)
    else begin
      if notGround then
        error
          ( termRegion tm,
            ((("Ambiguous level\n"
             ^ "The level of this term could not be inferred\n")
             ^ "Defaulting to ")
            ^ begin match i with
            | 1 -> "object"
            | 2 -> "type family"
            | 3 -> "kind"
            end)
            ^ " level" )
      else ()
    end
    end

  let rec findOmitted (g_, qid, r) =
    begin
      error
        ( r,
          "Undeclared identifier "
          ^ Names.qidToString (valOf (Names.constUndef qid)) );
      Omitted_ r
    end

  let rec findBVar' = function
    | IntSyn.Null, name, k -> None
    | IntSyn.Decl (g_, Dec (None, _)), name, k -> findBVar' (g_, name, k + 1)
    | IntSyn.Decl (g_, NDec _), name, k -> findBVar' (g_, name, k + 1)
    | IntSyn.Decl (g_, Dec (Some name', _)), name, k -> begin
        if name = name' then Some k else findBVar' (g_, name, k + 1)
      end

  let rec findBVar fc (g_, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g_, qid, r)
    | Some name -> begin
        match findBVar' (g_, name, 1) with
        | None -> fc (g_, qid, r)
        | Some k -> Bvar_ (k, r)
      end
    end

  let rec findConst fc (g_, qid, r) =
    begin match Names.constLookup qid with
    | None -> fc (g_, qid, r)
    | Some cid -> begin
        match IntSyn.sgnLookup cid with
        | IntSyn.ConDec _ -> Constant_ (IntSyn.Const cid, r)
        | IntSyn.ConDef _ -> Constant_ (IntSyn.Def cid, r)
        | IntSyn.AbbrevDef _ -> Constant_ (IntSyn.NSDef cid, r)
        | _ -> begin
            error
              ( r,
                (("Invalid identifier\n" ^ "Identifier `")
                ^ Names.qidToString qid)
                ^ "' is not a constant, definition or abbreviation" );
            Omitted_ r
          end
      end
    end

  let rec findCSConst fc (g_, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g_, qid, r)
    | Some name -> begin
        match Cs_manager.parse name with
        | None -> fc (g_, qid, r)
        | Some (cs, conDec) -> Constant_ (IntSyn.FgnConst (cs, conDec), r)
      end
    end

  let rec findEFVar fc (g_, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g_, qid, r)
    | Some name -> begin
        if !queryMode then Evar_ (name, r) else Fvar_ (name, r)
      end
    end

  let rec findLCID x = findBVar (findConst (findCSConst findOmitted)) x

  let rec findUCID x =
    findBVar (findConst (findCSConst (findEFVar findOmitted))) x

  let rec findQUID x = findConst (findCSConst findOmitted) x

  let rec inferApx = function
    | g_, (Internal_ (u_, v_, r) as tm) ->
        let u'_, v'_, l'_ = Apx.exactToApx (u_, v_) in
        (tm, u'_, v'_, l'_)
    | g_, (Lcid_ (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g_, findLCID (g_, qid, r))
    | g_, (Ucid_ (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g_, findUCID (g_, qid, r))
    | g_, (Quid_ (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g_, findQUID (g_, qid, r))
    | g_, (Scon_ (name, r) as tm) -> begin
        match Cs_manager.parse name with
        | None -> begin
            error (r, "Strings unsupported in current signature");
            inferApx (g_, Omitted_ r)
          end
        | Some (cs, conDec) ->
            inferApx (g_, Constant_ (IntSyn.FgnConst (cs, conDec), r))
      end
    | g_, (Constant_ (h_, r) as tm) ->
        let cd = headConDec h_ in
        let u'_, v'_, l'_ =
          Apx.exactToApx (IntSyn.Root (h_, IntSyn.Nil), IntSyn.conDecType cd)
        in
        let rec dropImplicit = function
          | v_, 0 -> v_
          | Apx.Arrow (_, v_), i -> dropImplicit (v_, i - 1)
        in
        let v''_ = dropImplicit (v'_, IntSyn.conDecImp cd) in
        (tm, u'_, v''_, l'_)
    | g_, (Bvar_ (k, r) as tm) ->
        let (Dec (_, v_)) = IntSyn.ctxLookup (g_, k) in
        (tm, undefined_, v_, Apx.(Level 1))
    | g_, (Evar_ (name, r) as tm) ->
        (tm, undefined_, getEVarTypeApx name, Apx.(Level 1))
    | g_, (Fvar_ (name, r) as tm) ->
        (tm, undefined_, getFVarTypeApx name, Apx.(Level 1))
    | g_, (Typ_ r as tm) -> (tm, uni_ Type, Apx.Uni kind_, hyperkind_)
    | g_, Arrow_ (tm1, tm2) ->
        let l_ = Apx.newLVar () in
        let tm1', v1_ =
          checkApx
            (g_, tm1, uni_ Type, kind_, "Left-hand side of arrow must be a type")
        in
        let tm2', v2_ =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l_,
              next_ l_,
              "Right-hand side of arrow must be a type or a kind" )
        in
        (Arrow_ (tm1', tm2'), Arrow (v1_, v2_), Apx.Uni l_, next_ l_)
    | g_, Pi_ (tm1, tm2) ->
        let tm1', (Dec (_, v1_) as d_) = inferApxDec (g_, tm1) in
        let l_ = Apx.newLVar () in
        let tm2', v2_ =
          checkApx
            ( decl_ (g_, d_),
              tm2,
              Apx.Uni l_,
              next_ l_,
              "Body of pi must be a type or a kind" )
        in
        (Pi_ (tm1', tm2'), Arrow (v1_, v2_), Apx.Uni l_, next_ l_)
    | g_, (Lam_ (tm1, tm2) as tm) ->
        let tm1', (Dec (_, v1_) as d_) = inferApxDec (g_, tm1) in
        let tm2', u2_, v2_, l2_ = inferApx (decl_ (g_, d_), tm2) in
        (Lam_ (tm1', tm2'), u2_, Arrow (v1_, v2_), l2_)
    | g_, (App_ (tm1, tm2) as tm) ->
        Debug.(
          msg Group.approx Level.Debug
          @@ Fmt.concat
               Fmt.
                 [
                   const string "Infering application of";
                   using fst pp_term;
                   const string "to";
                   using snd pp_term;
                 ])
          (tm1, tm2);
        let l_ = Apx.newLVar () in
        let va_ = Apx.newCVar () in
        let vr_ = Apx.newCVar () in
        let tm1', u1_ =
          checkApx
            ( g_,
              tm1,
              Arrow (va_, vr_),
              l_,
              "Non-function was applied to an argument" )
        in
        let tm2', _ =
          checkApx
            ( g_,
              tm2,
              va_,
              Apx.(Level 1),
              "Argument type did not match function domain type" )
        in
        (App_ (tm1', tm2'), u1_, vr_, l_)
        (* probably a confusing message if the problem is the level: *)
    | g_, (Hastype_ (tm1, tm2) as tm) ->
        let l_ = Apx.newLVar () in
        let tm2', v2_ =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l_,
              next_ l_,
              "Right-hand side of ascription must be a type or a kind" )
        in
        let tm1', u1_ =
          checkApx (g_, tm1, v2_, l_, "Ascription did not hold")
        in
        let _ =
          addDelayed (function () ->
              filterLevel
                ( tm,
                  l_,
                  2,
                  "Ascription can only be applied to objects and type families"
                ))
        in
        (Hastype_ (tm1', tm2'), u1_, v2_, l_)
    | g_, Omitted_ r ->
        let l_ = Apx.newLVar () in
        let v_ = Apx.newCVar () in
        let u_ = Apx.newCVar () in
        (Omitapx_ (u_, v_, l_, r), u_, v_, l_)
  (* guaranteed not to be used if L is type *)

  and checkApx (g_, tm, v_, l_, location_msg) =
    let tm', u'_, v'_, l'_ = inferApx (g_, tm) in
    try
      begin
        Apx.matchUni (l_, l'_);
        begin
          Apx.match_ (v_, v'_);
          (tm', u'_)
        end
      end
    with Apx.Unify problem_msg ->
      begin
        let r = termRegion tm in
        let tm'', u''_ = checkApx (g_, Omitted_ r, v_, l_, location_msg) in
        let _ = addDelayed (fun () -> ignore (Apx.makeGroundUni l'_)) in
        (Mismatch_ (tm', tm'', location_msg, problem_msg), u''_)
      end
  (* just in case *)

  and inferApxDec (g_, Dec_ (name, tm, r)) =
    let tm', v1_ =
      checkApx
        (g_, tm, uni_ Type, kind_, "Classifier in declaration must be a type")
    in
    let d_ = Dec (name, v1_) in
    (Dec_ (name, tm', r), d_)

  let rec inferApxJob = function
    | g_, Jnothing_ -> Jnothing_
    | g_, Jand_ (j1, j2) -> Jand_ (inferApxJob (g_, j1), inferApxJob (g_, j2))
    | g_, Jwithctx_ (g, j) ->
        let rec ia = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g'_, g' = ia g in
              let _ = clearDelayed () in
              let tm', d_ = inferApxDec (g'_, tm) in
              let _ = runDelayed () in
              (decl_ (g'_, d_), decl_ (g', tm'))
        in
        let g'_, g' = ia g in
        Jwithctx_ (g', inferApxJob (g'_, j))
    | g_, Jterm_ tm ->
        let _ = clearDelayed () in
        let tm', u_, v_, l_ = inferApx (g_, tm) in
        let _ =
          filterLevel
            ( tm',
              l_,
              2,
              "The term in this position must be an object or a type family" )
        in
        let _ = runDelayed () in
        Jterm_ tm'
    | g_, Jclass_ tm ->
        let _ = clearDelayed () in
        let l_ = Apx.newLVar () in
        let tm', v_ =
          checkApx
            ( g_,
              tm,
              Apx.Uni l_,
              next_ l_,
              "The term in this position must be a type or a kind" )
        in
        let _ =
          filterLevel
            ( tm',
              next_ l_,
              3,
              "The term in this position must be a type or a kind" )
        in
        let _ = runDelayed () in
        Jclass_ tm'
    | g_, Jof_ (tm1, tm2) ->
        let _ = clearDelayed () in
        let l_ = Apx.newLVar () in
        let tm2', v2_ =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l_,
              next_ l_,
              "The term in this position must be a type or a kind" )
        in
        let tm1', u1_ =
          checkApx (g_, tm1, v2_, l_, "Ascription in declaration did not hold")
        in
        let _ =
          filterLevel
            ( tm1',
              l_,
              2,
              "The term in this position must be an object or a type family" )
        in
        let _ = runDelayed () in
        Jof_ (tm1', tm2')
    | g_, Jof'_ (tm1, v_) ->
        let _ = clearDelayed () in
        let l_ = Apx.newLVar () in
        let v2_, _ = Apx.classToApx v_ in
        let tm1', u1_ =
          checkApx (g_, tm1, v2_, l_, "Ascription in declaration did not hold")
        in
        let _ =
          filterLevel
            ( tm1',
              l_,
              2,
              "The term in this position must be an object or a type family" )
        in
        let _ = runDelayed () in
        Jof'_ (tm1', v_)

  let rec ctxToApx = function
    | IntSyn.Null -> IntSyn.Null
    | IntSyn.Decl (g_, IntSyn.NDec x) -> IntSyn.Decl (ctxToApx g_, NDec x)
    | IntSyn.Decl (g_, IntSyn.Dec (name, v_)) ->
        let v'_, _ = Apx.classToApx v_ in
        IntSyn.Decl (ctxToApx g_, Dec (name, v'_))

  let rec inferApxJob' (g_, t) = inferApxJob (ctxToApx g_, t)

  (* open Apx *)
  open! struct
    open IntSyn
  end

  (* Final reconstruction job syntax *)
  type job_ =
    | JNothing
    | JAnd of job_ * job_
    | JWithCtx of IntSyn.dec IntSyn.ctx * job_
    | JTerm of (IntSyn.exp * Paths.occExp) * IntSyn.exp * IntSyn.uni
    | JClass of (IntSyn.exp * Paths.occExp) * IntSyn.uni
    | JOf of
        (IntSyn.exp * Paths.occExp) * (IntSyn.exp * Paths.occExp) * IntSyn.uni

  (* This little datatype makes it easier to work with eta-expanded terms
     The idea is that Elim E represents a term U if
       E (s, S) = U[s] @ S *)
  type bidi =
    | Elim of (IntSyn.sub * IntSyn.spine -> IntSyn.exp)
    | Intro of IntSyn.exp

  let rec elimSub (e_, s) = function s', s_ -> e_ (IntSyn.comp (s, s'), s_)

  let rec elimApp (e_, u_) = function
    | s, s_ -> e_ (s, IntSyn.App (eClo_ (u_, s), s_))

  let rec bvarElim n = function
    | s, s_ -> begin
        match IntSyn.bvarSub (n, s) with
        | Idx n' -> root_ (bVar_ n', s_)
        | Exp u_ -> redex_ (u_, s_)
      end

  let rec fvarElim (name, v_, s) = function
    | s', s_ -> root_ (fVar_ (name, v_, IntSyn.comp (s, s')), s_)

  let rec redexElim u_ = function s, s_ -> redex_ (eClo_ (u_, s), s_)

  (* headElim (H) = E
     assumes H not Proj _ *)
  let rec headElim = function
    | IntSyn.BVar n -> bvarElim n
    | IntSyn.FVar (name, v_, s) -> fvarElim (name, v_, s)
    | IntSyn.NSDef d -> redexElim (IntSyn.constDef d)
    | h_ -> begin
        match IntSyn.conDecStatus (headConDec h_) with
        | Foreign (_, f) -> fun (_, s_) -> f s_
        | _ -> fun (_, s_) -> Root (h_, s_)
      end

  (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[G]] V) *)
  let rec evarElim (IntSyn.EVar _ as x_) = function
    | s, s_ -> eClo_ (x_, Whnf.spineToSub (s_, s))

  let rec etaExpandW = function
    | e_, (IntSyn.Pi (((IntSyn.Dec (_, va_) as d_), _), vr_), s) ->
        let u1_ =
          etaExpand (bvarElim 1, (va_, IntSyn.comp (s, IntSyn.shift)))
        in
        let d'_ = IntSyn.decSub (d_, s) in
        IntSyn.Lam
          ( d'_,
            etaExpand
              (elimApp (elimSub (e_, IntSyn.shift), u1_), (vr_, IntSyn.dot1 s))
          )
    | e_, _ -> e_ (IntSyn.id, IntSyn.Nil)

  and etaExpand (e_, vs_) = etaExpandW (e_, Whnf.whnfExpandDef vs_)

  (* preserves redices *)
  let toElim = function Elim e_ -> e_ | Intro u_ -> redexElim u_

  let rec toIntro = function
    | Elim e_, vs_ -> etaExpand (e_, vs_)
    | Intro u_, vs_ -> u_

  let rec addImplicit1W
      (g_, e_, (IntSyn.Pi ((IntSyn.Dec (_, va_), _), vr_), s), i (* >= 1 *)) =
    let x_ = Whnf.newLoweredEVar (g_, (va_, s)) in
    addImplicit (g_, elimApp (e_, x_), (vr_, Whnf.dotEta (exp_ x_, s)), i - 1)

  and addImplicit = function
    | g_, e_, vs_, 0 -> (e_, eClo_ vs_)
    | g_, e_, vs_, i -> addImplicit1W (g_, e_, Whnf.whnfExpandDef vs_, i)

  (* if no implicit arguments, do not expand Vs!!! *)
  (* Report mismatches after the entire process finishes -- yields better
     error messages *)
  let rec reportConstraints xnames_ =
    try
      begin match Print.evarCnstrsToStringOpt xnames_ with
      | None -> ()
      | Some constr -> print (("Constraints:\n" ^ constr) ^ "\n")
      end
    with unprintable_ -> print "%_constraints unprintable_%\n"

  let rec reportInst xnames_ =
    try Msg.message (Print.evarInstToString xnames_ ^ "\n")
    with unprintable_ -> Msg.message "%_unifier unprintable_%\n"

  let rec delayMismatch (g_, v1_, v2_, r2, location_msg, problem_msg) =
    addDelayed (function () ->
        let xs_ =
          Abstract.collectEVars
            ( g_,
              (v2_, IntSyn.id),
              Abstract.collectEVars (g_, (v1_, IntSyn.id), []) )
        in
        let xnames_ =
          List.map (function x_ -> (x_, Names.evarName (IntSyn.Null, x_))) xs_
        in
        let v1fmt_ = formatExp (g_, v1_) in
        let v2fmt_ = formatExp (g_, v2_) in
        let diff =
          F.vbox0 0 1
            [
              F.string "Expected:";
              F.space;
              v2fmt_;
              F.break_;
              F.string "Inferred:";
              F.space;
              v1fmt_;
            ]
        in
        let diff =
          begin match Print.evarCnstrsToStringOpt xnames_ with
          | None -> F.makestring_fmt diff
          | Some cnstrs -> (F.makestring_fmt diff ^ "\nConstraints:\n") ^ cnstrs
          end
        in
        error
          ( r2,
            (((("Type mismatch\n" ^ diff) ^ "\n") ^ problem_msg) ^ "\n")
            ^ location_msg ))

  let rec delayAmbiguous (g_, u_, r, msg) =
    addDelayed (function () ->
        let ufmt_ = formatExp (g_, u_) in
        let amb =
          F.hVbox [ F.string "Inferred:"; F.space; formatExp (g_, u_) ]
        in
        error
          ( r,
            (("Ambiguous reconstruction\n" ^ F.makestring_fmt amb) ^ "\n") ^ msg
          ))

  let rec unifyIdem x =
    let _ = Unify.reset () in
    let _ =
      try Unify.unify x
      with Unify.Unify _ as e ->
        begin
          Unify.unwind ();
          raise e
        end
    in
    let _ = Unify.reset () in
    ()
  (* this reset should be unnecessary -- for safety only *)

  let rec unifiableIdem x =
    let _ = Unify.reset () in
    let ok = Unify.unifiable x in
    let _ =
      begin if ok then Unify.reset () else Unify.unwind ()
      end
    in
    ok
  (* this reset should be unnecessary -- for safety only *)

  (* tracing code *)
  type traceMode = Progressive | Omniscient

  let trace = ref false
  let traceMode = ref Omniscient

  let rec report f =
    begin match !traceMode with
    | Progressive -> f ()
    | Omniscient -> addDelayed f
    end

  let rec reportMismatch (g_, vs1_, vs2_, problem_msg) =
    report (function () ->
        let xs_ =
          Abstract.collectEVars (g_, vs2_, Abstract.collectEVars (g_, vs1_, []))
        in
        let xnames_ =
          List.map (function x_ -> (x_, Names.evarName (IntSyn.Null, x_))) xs_
        in
        let eqnsFmt =
          F.hVbox
            [
              F.string "|?";
              F.space;
              formatExp (g_, eClo_ vs1_);
              F.break_;
              F.string "=";
              F.space;
              formatExp (g_, eClo_ vs2_);
            ]
        in
        let _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n") in
        let _ = reportConstraints xnames_ in
        let _ =
          Msg.message
            ((("Failed: " ^ problem_msg) ^ "\n")
            ^ "Continuing with subterm replaced by _\n")
        in
        ())

  let rec reportUnify' (g_, vs1_, vs2_) =
    let xs_ =
      Abstract.collectEVars (g_, vs2_, Abstract.collectEVars (g_, vs1_, []))
    in
    let xnames_ =
      List.map (function x_ -> (x_, Names.evarName (IntSyn.Null, x_))) xs_
    in
    let eqnsFmt =
      F.hVbox
        [
          F.string "|?";
          F.space;
          formatExp (g_, eClo_ vs1_);
          F.break_;
          F.string "=";
          F.space;
          formatExp (g_, eClo_ vs2_);
        ]
    in
    let _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n") in
    let _ =
      try unifyIdem (g_, vs1_, vs2_)
      with Unify.Unify msg as e ->
        begin
          Msg.message
            ((("Failed: " ^ msg) ^ "\n")
            ^ "Continuing with subterm replaced by _\n");
          raise e
        end
    in
    let _ = reportInst xnames_ in
    let _ = reportConstraints xnames_ in
    ()

  let rec reportUnify (g_, vs1_, vs2_) =
    begin match !traceMode with
    | Progressive -> reportUnify' (g_, vs1_, vs2_)
    | Omniscient -> (
        try unifyIdem (g_, vs1_, vs2_)
        with Unify.Unify msg as e ->
          begin
            reportMismatch (g_, vs1_, vs2_, msg);
            raise e
          end)
    end

  let rec reportInfer' = function
    | g_, Omitexact_ (_, _, r), u_, v_ ->
        let xs_ =
          Abstract.collectEVars
            ( g_,
              (u_, IntSyn.id),
              Abstract.collectEVars (g_, (v_, IntSyn.id), []) )
        in
        let xnames_ =
          List.map (function x_ -> (x_, Names.evarName (IntSyn.Null, x_))) xs_
        in
        let omit =
          F.hVbox
            [
              F.string "|-";
              F.space;
              F.string "_";
              F.space;
              F.string "==>";
              F.space;
              formatExp (g_, u_);
              F.break_;
              F.string ":";
              F.space;
              formatExp (g_, v_);
            ]
        in
        let _ = Msg.message (F.makestring_fmt omit ^ "\n") in
        let _ = reportConstraints xnames_ in
        ()
    | g_, Mismatch_ (tm1, tm2, _, _), u_, v_ -> reportInfer' (g_, tm2, u_, v_)
    | g_, Hastype_ _, u_, v_ -> ()
    | g_, tm, u_, v_ ->
        let xs_ =
          Abstract.collectEVars
            ( g_,
              (u_, IntSyn.id),
              Abstract.collectEVars (g_, (v_, IntSyn.id), []) )
        in
        let xnames_ =
          List.map (function x_ -> (x_, Names.evarName (IntSyn.Null, x_))) xs_
        in
        let judg =
          F.hVbox
            [
              F.string "|-";
              F.space;
              formatExp (g_, u_);
              F.break_;
              F.string ":";
              F.space;
              formatExp (g_, v_);
            ]
        in
        let _ = Msg.message (F.makestring_fmt judg ^ "\n") in
        let _ = reportConstraints xnames_ in
        ()

  let rec reportInfer x = report (function () -> reportInfer' x)

  (* inferExact (G, tm) = (tm', U, V)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = U-
       and  U : V
       and  U, V are most general such
       effect: as for unification *)
  let rec inferExactN = function
    | g_, (Internal_ (u_, v_, r) as tm) -> (tm, Intro u_, v_)
    | g_, (Constant_ (h_, r) as tm) ->
        let cd = headConDec h_ in
        let e_, v_ =
          addImplicit
            ( g_,
              headElim h_,
              (IntSyn.conDecType cd, IntSyn.id),
              IntSyn.conDecImp cd )
        in
        (tm, Elim e_, v_)
    | g_, (Bvar_ (k, r) as tm) ->
        let (Dec (_, v_)) = IntSyn.ctxDec (g_, k) in
        (tm, Elim (bvarElim k), v_)
    | g_, (Evar_ (name, r) as tm) ->
        Logs.debug (fun m -> m "inferring EVar %s" name);
        let x_, v_ =
          try getEVar (name, false)
          with Apx.Ambiguous ->
            let x_, v_ = getEVar (name, true) in
            begin
              delayAmbiguous (g_, v_, r, "Free variable has ambiguous type");
              (x_, v_)
            end
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g_) in
        (tm, Elim (elimSub (evarElim x_, s)), eClo_ (v_, s))
        (* externally EVars are raised elim forms *)
        (* necessary? -kw *)
    | g_, (Fvar_ (name, r) as tm) ->
        Logs.debug (fun m -> m "inferring FVar %s" name);
        let v_ =
          try getFVarType (name, false)
          with Apx.Ambiguous ->
            let v_ = getFVarType (name, true) in
            begin
              Logs.debug (fun m -> m "ambiguous type for FVar %s" name);
              delayAmbiguous (g_, v_, r, "Free variable has ambiguous type");
              v_
            end
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g_) in
        (tm, Elim (fvarElim (name, v_, s)), EClo (v_, s))
        (* necessary? -kw *)
    | g_, (Typ_ r as tm) -> (tm, Intro (IntSyn.Uni Type), IntSyn.Uni Kind)
    | g_, Arrow_ (tm1, tm2) ->
        let tm1', b1_, _ (* Uni Type *) = inferExact (g_, tm1) in
        let d_ =
          IntSyn.Dec (None, toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)))
        in
        let tm2', b2_, l_ = inferExact (g_, tm2) in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        ( Arrow_ (tm1', tm2'),
          Intro (IntSyn.Pi ((d_, IntSyn.No), eClo_ (v2_, IntSyn.shift))),
          l_ )
    | g_, Pi_ (tm1, tm2) ->
        let tm1', d_ = inferExactDec (g_, tm1) in
        let tm2', b2_, l_ = inferExact (decl_ (g_, d_), tm2) in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        (Pi_ (tm1', tm2'), Intro (IntSyn.Pi ((d_, IntSyn.Maybe), v2_)), l_)
    | g_, Lam_ (tm1, tm2) ->
        let tm1', d_ = inferExactDec (g_, tm1) in
        let tm2', b2_, v2_ = inferExact (decl_ (g_, d_), tm2) in
        let u2_ = toIntro (b2_, (v2_, IntSyn.id)) in
        ( Lam_ (tm1', tm2'),
          Intro (IntSyn.Lam (d_, u2_)),
          IntSyn.Pi ((d_, IntSyn.Maybe), v2_) )
    | g_, App_ (tm1, tm2) ->
        let tm1', b1_, v1_ = inferExact (g_, tm1) in
        let e1_ = toElim b1_ in
        Debug.(
          msg Group.approx Level.Debug
          @@ Fmt.concat
               Fmt.
                 [
                   const string "Infering exact application of";
                   using fst pp_term;
                   const string "to";
                   using snd pp_term;
                 ])
          (tm1, tm2);
        let IntSyn.Pi ((IntSyn.Dec (_, va_), _), vr_), s =
          Whnf.whnfExpandDef (v1_, IntSyn.id)
        in
        let tm2', b2_ =
          checkExact
            ( g_,
              tm2,
              (va_, s),
              "Argument type did not match function domain type\n\
               (Index object(s) did not match)" )
        in
        let u2_ = toIntro (b2_, (va_, s)) in
        ( App_ (tm1', tm2'),
          Elim (elimApp (e1_, u2_)),
          eClo_ (vr_, Whnf.dotEta (exp_ u2_, s)) )
    | g_, Hastype_ (tm1, tm2) ->
        let tm2', b2_, l_ = inferExact (g_, tm2) in
        let v_ = toIntro (b2_, (l_, IntSyn.id)) in
        let tm1', b1_ =
          checkExact
            ( g_,
              tm1,
              (v_, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        (Hastype_ (tm1', tm2'), b1_, v_)
    | g_, Mismatch_ (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, v1_ = inferExact (g_, tm1) in
        let tm2', b_, v_ = inferExactN (g_, tm2) in
        let _ =
          begin if !trace then
            reportMismatch (g_, (v1_, IntSyn.id), (v_, IntSyn.id), problem_msg)
          else ()
          end
        in
        let _ =
          delayMismatch (g_, v1_, v_, termRegion tm2', location_msg, problem_msg)
        in
        (Mismatch_ (tm1', tm2', location_msg, problem_msg), b_, v_)
    | g_, Omitapx_ (u_, v_, l_, r) ->
        let v'_ =
          try Apx.apxToClass (g_, v_, l_, false)
          with Ambiguous ->
            let v'_ = Apx.apxToClass (g_, v_, l_, true) in
            begin
              delayAmbiguous
                ( g_,
                  v'_,
                  r,
                  "Omitted term has ambiguous "
                  ^ begin match Apx.whnfUni l_ with
                  | Apx.Level 1 -> "type"
                  | Apx.Level 2 -> "kind"
                  | Apx.Level 3 -> "hyperkind"
                  (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                  (* FIX: this violates an invariant in printing *)
                  end );
              v'_
            end
        in
        let u'_ =
          try Apx.apxToExact (g_, u_, (v'_, IntSyn.id), false)
          with Ambiguous ->
            let u'_ = Apx.apxToExact (g_, u_, (v'_, IntSyn.id), true) in
            begin
              delayAmbiguous
                ( g_,
                  u'_,
                  r,
                  ("Omitted "
                  ^ begin match Apx.whnfUni l_ with
                  | Apx.Level 2 -> "type"
                  | Apx.Level 3 -> "kind"
                  end)
                  ^ " is ambiguous" );
              u'_
            end
        in
        (Omitexact_ (u'_, v'_, r), Intro u'_, v'_)

  and inferExact (g_, tm) =
    begin if not !trace then inferExactN (g_, tm)
    else
      let tm', b'_, v'_ = inferExactN (g_, tm) in
      begin
        reportInfer (g_, tm', toIntro (b'_, (v'_, IntSyn.id)), v'_);
        (tm', b'_, v'_)
      end
    end

  and inferExactDec (g_, Dec_ (name, tm, r)) =
    let tm', b1_, _ (* Uni Type *) = inferExact (g_, tm) in
    let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
    let d_ = IntSyn.Dec (name, v1_) in
    (Dec_ (name, tm', r), d_)

  and checkExact1 = function
    | g_, Lam_ (Dec_ (name, tm1, r), tm2), vhs_ ->
        let Pi ((Dec (_, va_), _), vr_), s = Whnf.whnfExpandDef vhs_ in
        let (tm1', b1_, _ (* Uni Type *)), ok1 =
          unifyExact (g_, tm1, (va_, s))
        in
        let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
        let d_ = IntSyn.Dec (name, v1_) in
        let (tm2', b2_, v2_), ok2 =
          begin if ok1 then
            checkExact1 (decl_ (g_, d_), tm2, (vr_, IntSyn.dot1 s))
          else (inferExact (decl_ (g_, d_), tm2), false)
          end
        in
        let u2_ = toIntro (b2_, (v2_, IntSyn.id)) in
        ( ( Lam_ (Dec_ (name, tm1', r), tm2'),
            Intro (IntSyn.Lam (d_, u2_)),
            IntSyn.Pi ((d_, IntSyn.Maybe), v2_) ),
          ok2 )
    | g_, Hastype_ (tm1, tm2), vhs_ ->
        let (tm2', b2_, l_), ok2 = unifyExact (g_, tm2, vhs_) in
        let v_ = toIntro (b2_, (l_, IntSyn.id)) in
        let tm1', b1_ =
          checkExact
            ( g_,
              tm1,
              (v_, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        ((Hastype_ (tm1', tm2'), b1_, v_), ok2)
    | g_, Mismatch_ (tm1, tm2, location_msg, problem_msg), vhs_ ->
        let tm1', _, v1_ = inferExact (g_, tm1) in
        let (tm2', b_, v_), ok2 = checkExact1 (g_, tm2, vhs_) in
        let _ =
          delayMismatch (g_, v1_, v_, termRegion tm2', location_msg, problem_msg)
        in
        ((Mismatch_ (tm1', tm2', location_msg, problem_msg), b_, v_), ok2)
    | g_, Omitapx_ (u_, v_, l_, r (* = Vhs *)), vhs_ ->
        let v'_ = eClo_ vhs_ in
        let u'_ =
          try Apx.apxToExact (g_, u_, vhs_, false)
          with Ambiguous ->
            let u'_ = Apx.apxToExact (g_, u_, vhs_, true) in
            begin
              delayAmbiguous
                ( g_,
                  u'_,
                  r,
                  ("Omitted "
                  ^ begin match Apx.whnfUni l_ with
                  | Apx.Level 2 -> "type"
                  | Apx.Level 3 -> "kind"
                  end)
                  ^ " is ambiguous" );
              u'_
            end
        in
        ((Omitexact_ (u'_, v'_, r), Intro u'_, v'_), true)
    | g_, tm, vhs_ ->
        let tm', b'_, v'_ = inferExact (g_, tm) in
        ((tm', b'_, v'_), unifiableIdem (g_, vhs_, (v'_, IntSyn.id)))

  and checkExact (g_, tm, vs_, location_msg) =
    begin if not !trace then
      let (tm', b'_, v'_), ok = checkExact1 (g_, tm, vs_) in
      begin if ok then (tm', b'_)
      else
        try
          begin
            unifyIdem (g_, (v'_, IntSyn.id), vs_);
            raise Match
          end
          (* can't happen *)
        with Unify.Unify problem_msg ->
          let r = termRegion tm in
          let u'_ = toIntro (b'_, (v'_, IntSyn.id)) in
          let uapx_, vapx_, lapx_ = Apx.exactToApx (u'_, v'_) in
          let (tm'', b''_, _ (* Vs *)), _ (* true *) =
            checkExact1 (g_, Omitapx_ (uapx_, vapx_, lapx_, r), vs_)
          in
          let _ =
            delayMismatch (g_, v'_, eClo_ vs_, r, location_msg, problem_msg)
          in
          (Mismatch_ (tm', tm'', location_msg, problem_msg), b''_)
      end
    else
      let tm', b'_, v'_ = inferExact (g_, tm) in
      try
        begin
          reportUnify (g_, (v'_, IntSyn.id), vs_);
          (tm', b'_)
        end
      with Unify.Unify problem_msg ->
        let r = termRegion tm in
        let u'_ = toIntro (b'_, (v'_, IntSyn.id)) in
        let uapx_, vapx_, lapx_ = Apx.exactToApx (u'_, v'_) in
        let tm'', b''_ =
          checkExact (g_, Omitapx_ (uapx_, vapx_, lapx_, r), vs_, location_msg)
        in
        let _ =
          delayMismatch (g_, v'_, eClo_ vs_, r, location_msg, problem_msg)
        in
        (Mismatch_ (tm', tm'', location_msg, problem_msg), b''_)
    end

  and unifyExact = function
    | g_, Arrow_ (tm1, tm2), vhs_ ->
        let Pi ((Dec (_, va_), _), vr_), s = Whnf.whnfExpandDef vhs_ in
        let (tm1', b1_, _ (* Uni Type *)), ok1 =
          unifyExact (g_, tm1, (va_, s))
        in
        let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
        let d_ = IntSyn.Dec (None, v1_) in
        let tm2', b2_, l_ = inferExact (g_, tm2) in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        ( ( Arrow_ (tm1', tm2'),
            Intro (IntSyn.Pi ((d_, IntSyn.No), eClo_ (v2_, IntSyn.shift))),
            l_ ),
          ok1
          && unifiableIdem
               (decl_ (g_, d_), (vr_, IntSyn.dot1 s), (v2_, IntSyn.shift)) )
    | g_, Pi_ (Dec_ (name, tm1, r), tm2), vhs_ ->
        let Pi ((Dec (_, va_), _), vr_), s = Whnf.whnfExpandDef vhs_ in
        let (tm1', b1_, _ (* Uni Type *)), ok1 =
          unifyExact (g_, tm1, (va_, s))
        in
        let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
        let d_ = IntSyn.Dec (name, v1_) in
        let (tm2', b2_, l_), ok2 =
          begin if ok1 then
            unifyExact (decl_ (g_, d_), tm2, (vr_, IntSyn.dot1 s))
          else (inferExact (decl_ (g_, d_), tm2), false)
          end
        in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        ( ( Pi_ (Dec_ (name, tm1', r), tm2'),
            Intro (IntSyn.Pi ((d_, IntSyn.Maybe), v2_)),
            l_ ),
          ok2 )
    | g_, Hastype_ (tm1, tm2), vhs_ ->
        let ( tm2',
              _,
              _
              (* Uni L *)
              (* Uni (Next L) *) ) =
          inferExact (g_, tm2)
        in
        let (tm1', b_, l_), ok1 = unifyExact (g_, tm1, vhs_) in
        ((Hastype_ (tm1', tm2'), b_, l_), ok1)
        (* Vh : L by invariant *)
    | g_, Mismatch_ (tm1, tm2, location_msg, problem_msg), vhs_ ->
        let tm1', _, l1_ = inferExact (g_, tm1) in
        let (tm2', b_, l_), ok2 = unifyExact (g_, tm2, vhs_) in
        let _ =
          delayMismatch (g_, l1_, l_, termRegion tm2', location_msg, problem_msg)
        in
        ((Mismatch_ (tm1', tm2', location_msg, problem_msg), b_, l_), ok2)
    | ( g_,
        Omitapx_
          ( v_,
            l_,
            nL,
            r
            (* = Vhs *)
            (* Next L *) ),
        vhs_ ) ->
        let l'_ = Apx.apxToClass (g_, l_, nL, false) in
        let v'_ = eClo_ vhs_ in
        ((Omitexact_ (v'_, l'_, r), Intro v'_, l'_), true)
        (* cannot raise Ambiguous *)
    | g_, tm, vhs_ ->
        let tm', b'_, l'_ = inferExact (g_, tm) in
        let v'_ = toIntro (b'_, (l'_, IntSyn.id)) in
        ((tm', b'_, l'_), unifiableIdem (g_, vhs_, (v'_, IntSyn.id)))
  (* lam impossible *)

  let rec occElim = function
    | Constant_ (h_, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        ( Paths.root (r', Paths.leaf r, IntSyn.conDecImp (headConDec h_), i, os),
          r' )
        (* should probably treat a constant with Foreign
             attribute as a redex *)
    | Bvar_ (k, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | Fvar_ (name, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | App_ (tm1, tm2), os, rs, i ->
        let oc2, r2 = occIntro tm2 in
        occElim (tm1, Paths.app (oc2, os), r2 :: rs, i + 1)
    | Hastype_ (tm1, tm2), os, rs, i -> occElim (tm1, os, rs, i)
    | tm, os, rs, i ->
        let r' = List.foldr Paths.join (termRegion tm) rs in
        (Paths.leaf r', r')
  (* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)

  and occIntro = function
    | Arrow_ (tm1, tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join (r1, r2) in
        (Paths.bind (r', Some oc1, oc2), r')
    | Pi_ (Dec_ (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join (r, r2) in
        (Paths.bind (r', Some oc1, oc2), r')
        (* not quite consistent with older implementation for dec0 *)
    | Lam_ (Dec_ (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join (r, r2) in
        (Paths.bind (r', Some oc1, oc2), r')
        (* not quite consistent with older implementation for dec0 *)
    | Hastype_ (tm1, tm2) -> occIntro tm1
    | tm ->
        let oc, r = occElim (tm, Paths.nils, [], 0) in
        (oc, r)
  (* still doesn't work quite right for the location -> occurrence map? *)

  let rec inferExactJob = function
    | g_, Jnothing_ -> JNothing
    | g_, Jand_ (j1, j2) -> JAnd (inferExactJob (g_, j1), inferExactJob (g_, j2))
    | g_, Jwithctx_ (g, j) ->
        let rec ie = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g'_, gresult_ = ie g in
              let _, d_ = inferExactDec (g'_, tm) in
              (decl_ (g'_, d_), decl_ (gresult_, d_))
        in
        let g'_, gresult_ = ie g in
        JWithCtx (gresult_, inferExactJob (g'_, j))
    | g_, Jterm_ tm ->
        let tm', b_, v_ = inferExact (g_, tm) in
        let u_ = toIntro (b_, (v_, IntSyn.id)) in
        let oc, r = occIntro tm' in
        let rec iu = function
          | IntSyn.Uni Type -> IntSyn.Kind
          | IntSyn.Pi (_, v_) -> iu v_
          | IntSyn.Root _ -> IntSyn.Type
          | IntSyn.Redex (v_, _) -> iu v_
          | IntSyn.Lam (_, v_) -> iu v_
          | IntSyn.EClo (v_, _) -> iu v_
        in
        JTerm ((u_, oc), v_, iu v_)
        (* others impossible *)
    | g_, Jclass_ tm ->
        let tm', b_, l_ = inferExact (g_, tm) in
        let v_ = toIntro (b_, (l_, IntSyn.id)) in
        let oc, r = occIntro tm' in
        let IntSyn.Uni l_, _ = Whnf.whnf (l_, IntSyn.id) in
        JClass ((v_, oc), l_)
    | g_, Jof_ (tm1, tm2) ->
        let tm2', b2_, l2_ = inferExact (g_, tm2) in
        let v2_ = toIntro (b2_, (l2_, IntSyn.id)) in
        let tm1', b1_ =
          checkExact
            ( g_,
              tm1,
              (v2_, IntSyn.id),
              "Ascription in declaration did not hold\n"
              ^ "(Index object(s) did not match)" )
        in
        let u1_ = toIntro (b1_, (v2_, IntSyn.id)) in
        let oc2, r2 = occIntro tm2' in
        let oc1, r1 = occIntro tm1' in
        let IntSyn.Uni l2_, _ = Whnf.whnf (l2_, IntSyn.id) in
        JOf ((u1_, oc1), (v2_, oc2), l2_)
    | g_, Jof'_ (tm1, v2_) ->
        let tm1', b1_ =
          checkExact
            ( g_,
              tm1,
              (v2_, IntSyn.id),
              "Ascription in declaration did not hold\n"
              ^ "(Index object(s) did not match)" )
        in
        let u1_ = toIntro (b1_, (v2_, IntSyn.id)) in
        let oc1, r1 = occIntro tm1' in
        JOf ((u1_, oc1), (v2_, oc1), IntSyn.Type)
  (*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
  (*          val (oc2, r2) = occIntro tm2' *)
  (*          val (Uni L2, _) = Whnf.whnf (L2, id) *)

  let rec recon' j =
    let _ = Apx.varReset () in
    StringTree.clear evarApxTable;
    StringTree.clear fvarApxTable;
    StringTree.clear fvarTable;
    let j' = inferApxJob (IntSyn.Null, j) in
    let _ = clearDelayed () in
    let j'' = inferExactJob (IntSyn.Null, j') in
    let _ = runDelayed () in
    j''
  (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
  (* context must already have called resetErrors *)
  (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the ""best effort"" result returned, even if there were
             errors *)

  let rec recon j =
    begin
      queryMode := false;
      recon' j
    end

  let rec reconQuery j =
    begin
      queryMode := true;
      recon' j
    end

  (* Invariant, G must be named! *)
  let rec reconWithCtx' (g_, j) =
    let _ = Apx.varReset () in
    let _ = varReset () in
    let j' = inferApxJob' (g_, j) in
    let _ = clearDelayed () in
    let j'' = inferExactJob (g_, j') in
    let _ = runDelayed () in
    j''
  (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
  (* context must already have called resetErrors *)
  (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the ""best effort"" result returned, even if there were
             errors *)

  let rec reconWithCtx (g_, j) =
    begin
      queryMode := false;
      reconWithCtx' (g_, j)
    end

  let rec reconQueryWithCtx (g_, j) =
    begin
      queryMode := true;
      reconWithCtx' (g_, j)
    end

  let rec internalInst x = raise Match
  let rec externalInst x = raise Match
end
(* open IntSyn *)
(* functor ReconTerm *)

(* # 1 "src/frontend/recon_term.sml.ml" *)
