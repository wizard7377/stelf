open! Global.Global_
open! Table.Table_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths.Paths_
open! Print.Print_
open! Solvers.Solvers_
open! Msg.Msg_

(* # 1 "src/frontend/ReconTerm.sig.ml" *)

(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)
(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)
include RECONTERM

(* id | _  (type omitted) *)
(* signature EXTSYN *)
(* signature RECON_TERM
   provides the interface to type reconstruction seen by Stelf 
*)
(* signature RECON_TERM *)

(* # 1 "src/frontend/ReconTerm.fun.ml" *)
open! Basis

(* Type Reconstruction with Tracing *)
(* Author: Kevin Watkins *)
(* Based on a previous implementation by Frank Pfenning *)
(* with modifications by Jeff Polakow and Roberto Virga *)
(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn' !*)
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
  let clearDelayed () = delayedList := []
  let addDelayed f = delayedList := f :: !delayedList

  let runDelayed () =
    let rec run' = function
      | [] -> ()
      | h :: t -> begin
          run' t;
          h ()
        end
    in
    run' !delayedList

  exception Error = Error

  let errorCount = ref 0
  let errorFileName = ref "no file"
  let errorThreshold = ref (Some 20)
  let exceeds (i, a) = match a with None -> false | Some j -> i > j

  let resetErrors fileName =
    begin
      errorCount := 0;
      errorFileName := fileName
    end

  let die r =
    raise
      (Error
         (Paths.wrap
            r ((((" " ^ Int.toString !errorCount) ^ " error")
              ^ begin if !errorCount > 1 then "s" else ""
              end)
              ^ " found")))

  let checkErrors r =
    begin if !errorCount > 0 then die r else ()
    end

  (* Since this structure uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the ""[Loading file ..."" message and the closing ""]"",
     instead of after the closing ""]"".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same line
     as ""[Loading file ..."", terribly confusing the Emacs error parsing code.
   *)
  let chatterOneNewline () =
    begin if !Global.chatter = 1 && !errorCount = 1 then
      Display.debug (Display.string "\n")
    else ()
    end

  let fatalError (r, msg) =
    begin
      errorCount := !errorCount + 1;
      begin
        chatterOneNewline ();
        begin
          Display.debug
            (Display.string
               (((!errorFileName ^ ":") ^ Paths.wrap r msg) ^ "\n"));
          die r
        end
      end
    end

  let error r msg =
    begin
      errorCount := !errorCount + 1;
      begin
        chatterOneNewline ();
        begin
          Display.debug
            (Display.string
               (((!errorFileName ^ ":") ^ Paths.wrap r msg) ^ "\n"));
          begin if exceeds (!errorCount, !errorThreshold) then die r else ()
          end
        end
      end
    end

  let withConstPath show f =
    let old = !Print.showConstPath in
    Print.showConstPath := show;
    try
      let result = f () in
      Print.showConstPath := old;
      result
    with exn ->
      Print.showConstPath := old;
      raise exn

  let formatExp g u =
    withConstPath false (fun () ->
        try Print.formatExp g u
        with unprintable -> F.string "%_unprintable_%")

  (* this is a hack, i know *)
  let queryMode = ref false

  open! struct
    open IntSyn
  end

  let decl_ (g, d) = IntSyn.Decl (g, d)
  let eClo (v, s) = IntSyn.EClo (v, s)
  let root_ (h, s) = IntSyn.Root (h, s)
  let bVar n = IntSyn.BVar n
  let redex_ (u, s) = IntSyn.Redex (u, s)
  let fVar (name, v, s) = IntSyn.FVar (name, v, s)
  let exp_ u = IntSyn.Exp u
  let undefined_ = Apx.Undefined
  let uni_ l = Apx.Uni (Apx.uniToApx l)
  let kind_ = Apx.kind
  let hyperkind_ = Apx.hyperkind
  let next_ l = Apx.Next l

  let headConDec (h : IntSyn.head) =
    begin match h with
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
  let rec lowerTypeW (g, vs) = match vs with
    | (IntSyn.Pi ((d, _), v), s) ->
        let d' = IntSyn.decSub d s in
        lowerType (decl_ (g, d'), (v, IntSyn.dot1 s))
    | vs -> (g, eClo vs)

  and lowerType (g, vs) = lowerTypeW (g, Whnf.whnfExpandDef vs)

  (* raiseType (G, V) = {{G}} V *)
  let rec raiseType a1 b1 = match a1, b1 with
    | IntSyn.Null, v -> v
    | IntSyn.Decl (g, d), v ->
        raiseType g (IntSyn.Pi ((d, IntSyn.Maybe), v))

  (* open IntSyn *)
  let evarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarTable : IntSyn.exp StringTree.table = StringTree.new_ 0

  let varReset () =
    StringTree.clear evarApxTable;
    StringTree.clear fvarApxTable;
    StringTree.clear fvarTable

  let fvarApxTable_ref_check () = fvarApxTable

  let getEVarTypeApx name =
    begin match StringTree.lookup evarApxTable name with
    | Some v -> v
    | None ->
        begin match Names.getEVarOpt name with
        | Some (IntSyn.EVar (_, _, v, _)) ->
            let v', _ (* Type *) = Apx.classToApx v in
            StringTree.insert evarApxTable (name, v');
            v'
        | None ->
            let v = Apx.newCVar () in
            StringTree.insert evarApxTable (name, v);
            v
        end
    end

  let getFVarTypeApx name =
    begin match StringTree.lookup fvarApxTable name with
    | Some v ->
        Debug.(
          msg ~src:Group.approx ~level:Level.Debug
            (Fmt.shown_exact
               (fun name -> "getFVarTypeApx: found existing for " ^ name)
               name));
        v
    | None ->
        let v = Apx.newCVar () in
        Debug.(
          msg ~src:Group.approx ~level:Level.Debug
            (Fmt.shown_exact
               (fun name -> "getFVarTypeApx: creating fresh CVar for " ^ name)
               name));
        begin
          StringTree.insert fvarApxTable (name, v);
          v
        end
    end

  let getEVar (name, allowed) =
    begin match Names.getEVarOpt name with
    | Some (IntSyn.EVar (_, g, v, _) as x) -> (x, raiseType g v)
    | None ->
        let v = Option.valOf (StringTree.lookup evarApxTable name) in
        let v' = Apx.apxToClass (IntSyn.Null, v, Apx.(Level 1), allowed) in
        let g'', v'' = lowerType (IntSyn.Null, (v', IntSyn.id)) in
        let x = IntSyn.newEVar g'' v'' in
        Names.addEVar x name;
        (x, v')
    end

  let getFVarType (name, allowed) =
    begin match StringTree.lookup fvarTable name with
    | Some v -> v
    | None ->
        let v = Option.valOf (StringTree.lookup fvarApxTable name) in
        let v' = Apx.apxToClass (IntSyn.Null, v, Apx.(Level 1), allowed) in
        StringTree.insert fvarTable (name, v');
        v'
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
    | Omitapx of Apx.exp * Apx.exp * Apx.uni * Paths.region
    | Omitexact of IntSyn.exp * IntSyn.exp * Paths.region
  [@@deriving show { with_path = false }]

  and dec = Dec_ of string option * term * Paths.region

  let lcid ids name r = Lcid_ (ids, name, r)
  let ucid ids name r = Ucid_ (ids, name, r)
  let quid ids name r = Quid_ (ids, name, r)
  let scon value r = Scon_ (value, r)
  let evar name r = Evar_ (name, r)
  let fvar name r = Fvar_ (name, r)
  let typ r = Typ_ r
  let arrow tm1 tm2 = Arrow_ (tm1, tm2)
  let pi d tm = Pi_ (d, tm)
  let lam d tm = Lam_ (d, tm)
  let app tm1 tm2 = App_ (tm1, tm2)
  let hastype tm1 tm2 = Hastype_ (tm1, tm2)
  let omitted r = Omitted_ r
  let dec (nameOpt, tm, r) = Dec_ (nameOpt, tm, r)

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
  let backarrow tm1 tm2 = Arrow_ (tm2, tm1)

  (* for now *)
  let dec0 nameOpt r = Dec_ (nameOpt, Omitted_ r, r)

  type job =
    | Jnothing
    | Jand of job * job
    | Jwithctx of dec IntSyn.ctx * job
    | Jterm of term
    | Jclass of term
    | Jof of term * term
    | Jof' of term * IntSyn.exp

  let jnothing = Jnothing
  let jand j1 j2 = Jand (j1, j2)
  let jwithctx g j = Jwithctx (g, j)
  let jterm tm = Jterm tm
  let jclass tm = Jclass tm
  let jof tm1 tm2 = Jof (tm1, tm2)
  let jof' tm v = Jof' (tm, v)

  let rec termRegion = function
    | Internal_ (u, v, r) -> r
    | Constant_ (h, r) -> r
    | Bvar_ (k, r) -> r
    | Evar_ (name, r) -> r
    | Fvar_ (name, r) -> r
    | Typ_ r -> r
    | Arrow_ (tm1, tm2) -> Paths.join (termRegion tm1) (termRegion tm2)
    | Pi_ (tm1, tm2) -> Paths.join (decRegion tm1) (termRegion tm2)
    | Lam_ (tm1, tm2) -> Paths.join (decRegion tm1) (termRegion tm2)
    | App_ (tm1, tm2) -> Paths.join (termRegion tm1) (termRegion tm2)
    | Hastype_ (tm1, tm2) -> Paths.join (termRegion tm1) (termRegion tm2)
    | Mismatch_ (tm1, tm2, _, _) -> termRegion tm2
    | Omitted_ r -> r
    | Lcid_ (_, _, r) -> r
    | Ucid_ (_, _, r) -> r
    | Quid_ (_, _, r) -> r
    | Scon_ (_, r) -> r
    | Omitapx (u, v, l, r) -> r
    | Omitexact (u, v, r) -> r

  and decRegion (Dec_ (name, tm, r)) = r

  let rec ctxRegion = function
    | IntSyn.Null -> None
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, decRegion tm)

  and ctxRegion' (a, r) = match a with
    | IntSyn.Null -> Some r
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, Paths.join r (decRegion tm))

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
  let filterLevel (tm, l, max, msg) =
    let notGround = Apx.makeGroundUni l in
    let (Apx.Level i) = Apx.whnfUni l in
    begin if i > max then fatalError (termRegion tm, "Level too high\n" ^ msg)
    else
      begin if notGround then
        error
          (termRegion tm) (((("Ambiguous level\n"
             ^ "The level of this term could not be inferred\n")
             ^ "Defaulting to ")
            ^ begin match i with
            | 1 -> "object"
            | 2 -> "type family"
            | 3 -> "kind"
            end)
            ^ " level")
      else ()
      end
    end

  let findOmitted (g, qid, r) =
    begin
      error
        r ("Undeclared identifier "
          ^ Names.qidToString (valOf (Names.constUndef qid)));
      Omitted_ r
    end

  let rec findBVar' (a, name, k) = match a with
    | IntSyn.Null -> None
    | IntSyn.Decl (g, Dec (None, _)) -> findBVar' (g, name, k + 1)
    | IntSyn.Decl (g, NDec _) -> findBVar' (g, name, k + 1)
    | IntSyn.Decl (g, Dec (Some name', _)) ->
        begin if name = name' then Some k else findBVar' (g, name, k + 1)
        end

  let findBVar fc (g, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g, qid, r)
    | Some name ->
        begin match findBVar' (g, name, 1) with
        | None -> fc (g, qid, r)
        | Some k -> Bvar_ (k, r)
        end
    end

  let findConst fc (g, qid, r) =
    begin match Names.constLookup qid with
    | None -> fc (g, qid, r)
    | Some cid ->
        begin match IntSyn.sgnLookup cid with
        | IntSyn.ConDec _ -> Constant_ (IntSyn.Const cid, r)
        | IntSyn.ConDef _ -> Constant_ (IntSyn.Def cid, r)
        | IntSyn.AbbrevDef _ -> Constant_ (IntSyn.NSDef cid, r)
        | _ -> begin
            error
              r ((("Invalid identifier\n" ^ "Identifier `")
                ^ Names.qidToString qid)
                ^ "' is not a constant, definition or abbreviation");
            Omitted_ r
          end
        end
    end

  let findCSConst fc (g, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g, qid, r)
    | Some name ->
        begin match CsManager.parse name with
        | None -> fc (g, qid, r)
        | Some (cs, conDec) -> Constant_ (IntSyn.FgnConst (cs, conDec), r)
        end
    end

  let findEFVar fc (g, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g, qid, r)
    | Some name ->
        begin if !queryMode then Evar_ (name, r) else Fvar_ (name, r)
        end
    end

  let findLCID x = findBVar (findConst (findCSConst findOmitted)) x
  let findUCID x = findBVar (findConst (findCSConst (findEFVar findOmitted))) x
  let findQUID x = findConst (findCSConst findOmitted) x

  let rec inferApx (g, b) = match b with
    | (Internal_ (u, v, r) as tm) ->
        let u', v', l' = Apx.exactToApx u v in
        (tm, u', v', l')
    | (Lcid_ (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g, findLCID (g, qid, r))
    | (Ucid_ (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g, findUCID (g, qid, r))
    | (Quid_ (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g, findQUID (g, qid, r))
    | (Scon_ (name, r) as tm) ->
        begin match CsManager.parse name with
        | None -> begin
            error r ("Strings unsupported in current signature");
            inferApx (g, Omitted_ r)
          end
        | Some (cs, conDec) ->
            inferApx (g, Constant_ (IntSyn.FgnConst (cs, conDec), r))
        end
    | (Constant_ (h, r) as tm) ->
        let cd = headConDec h in
        let u', v', l' =
          Apx.exactToApx (IntSyn.Root (h, IntSyn.Nil)) (IntSyn.conDecType cd)
        in
        let rec dropImplicit = function
          | v, 0 -> v
          | Apx.Arrow (_, v), i -> dropImplicit (v, i - 1)
        in
        let v'' = dropImplicit (v', IntSyn.conDecImp cd) in
        (tm, u', v'', l')
    | (Bvar_ (k, r) as tm) ->
        let (Dec (_, v)) = IntSyn.ctxLookup g k in
        (tm, undefined_, v, Apx.(Level 1))
    | (Evar_ (name, r) as tm) ->
        (tm, undefined_, getEVarTypeApx name, Apx.(Level 1))
    | (Fvar_ (name, r) as tm) ->
        (tm, undefined_, getFVarTypeApx name, Apx.(Level 1))
    | (Typ_ r as tm) -> (tm, uni_ Type, Apx.Uni kind_, hyperkind_)
    | Arrow_ (tm1, tm2) ->
        let l = Apx.newLVar () in
        let tm1', v1 =
          checkApx
            (g, tm1, uni_ Type, kind_, "Left-hand side of arrow must be a type")
        in
        let tm2', v2 =
          checkApx
            ( g,
              tm2,
              Apx.Uni l,
              next_ l,
              "Right-hand side of arrow must be a type or a kind" )
        in
        (Arrow_ (tm1', tm2'), Arrow (v1, v2), Apx.Uni l, next_ l)
    | Pi_ (tm1, tm2) ->
        let tm1', (Dec (_, v1) as d) = inferApxDec (g, tm1) in
        let l = Apx.newLVar () in
        let tm2', v2 =
          checkApx
            ( decl_ (g, d),
              tm2,
              Apx.Uni l,
              next_ l,
              "Body of pi must be a type or a kind" )
        in
        (Pi_ (tm1', tm2'), Arrow (v1, v2), Apx.Uni l, next_ l)
    | (Lam_ (tm1, tm2) as tm) ->
        let tm1', (Dec (_, v1) as d) = inferApxDec (g, tm1) in
        let tm2', u2, v2, l2 = inferApx (decl_ (g, d), tm2) in
        (Lam_ (tm1', tm2'), u2, Arrow (v1, v2), l2)
    | (App_ (tm1, tm2) as tm) ->
        Debug.(
          msg' ~src:Group.approx ~level:Level.Debug
          @@ Fmt.concat
               Fmt.
                 [
                   const string "Infering application of";
                   using fst pp_term;
                   const string "to";
                   using snd pp_term;
                 ])
          (tm1, tm2);
        let l = Apx.newLVar () in
        let va = Apx.newCVar () in
        let vr = Apx.newCVar () in
        let tm1', u1 =
          checkApx
            ( g,
              tm1,
              Arrow (va, vr),
              l,
              "Non-function was applied to an argument" )
        in
        let tm2', _ =
          checkApx
            ( g,
              tm2,
              va,
              Apx.(Level 1),
              "Argument type did not match function domain type" )
        in
        (App_ (tm1', tm2'), u1, vr, l)
        (* probably a confusing message if the problem is the level: *)
    | (Hastype_ (tm1, tm2) as tm) ->
        let l = Apx.newLVar () in
        let tm2', v2 =
          checkApx
            ( g,
              tm2,
              Apx.Uni l,
              next_ l,
              "Right-hand side of ascription must be a type or a kind" )
        in
        let tm1', u1 =
          checkApx (g, tm1, v2, l, "Ascription did not hold")
        in
        ignore (addDelayed (function () ->
              filterLevel
                ( tm,
                  l,
                  2,
                  "Ascription can only be applied to objects and type families"
                )));
        (Hastype_ (tm1', tm2'), u1, v2, l)
    | Omitted_ r ->
        let l = Apx.newLVar () in
        let v = Apx.newCVar () in
        let u = Apx.newCVar () in
        (Omitapx (u, v, l, r), u, v, l)
  (* guaranteed not to be used if L is type *)

  and checkApx (g, tm, v, l, location_msg) =
    let tm', u', v', l' = inferApx (g, tm) in
    try
      begin
        Apx.matchUni l l';
        begin
          Apx.match_ (v, v');
          (tm', u')
        end
      end
    with Apx.Unify problem_msg ->
      begin
        let r = termRegion tm in
        let tm'', u'' = checkApx (g, Omitted_ r, v, l, location_msg) in
        ignore (addDelayed (fun () -> ignore (Apx.makeGroundUni l')));
        (Mismatch_ (tm', tm'', location_msg, problem_msg), u'')
      end
  (* just in case *)

  and inferApxDec (g, Dec_ (name, tm, r)) =
    let tm', v1 =
      checkApx
        (g, tm, uni_ Type, kind_, "Classifier in declaration must be a type")
    in
    let d = Dec (name, v1) in
    (Dec_ (name, tm', r), d)

  let rec inferApxJob (g_, b) = match b with
    | Jnothing -> Jnothing
    | Jand (j1, j2) -> Jand (inferApxJob (g_, j1), inferApxJob (g_, j2))
    | Jwithctx (g, j) ->
        let rec ia = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g'_, g' = ia g in
              ignore (clearDelayed ());
              let tm', d = inferApxDec (g'_, tm) in
              ignore (runDelayed ());
              (decl_ (g'_, d), decl_ (g', tm'))
        in
        let g'_, g' = ia g in
        Jwithctx (g', inferApxJob (g'_, j))
    | Jterm tm ->
        ignore (clearDelayed ());
        let tm', u, v, l = inferApx (g_, tm) in
        ignore (filterLevel
            ( tm',
              l,
              2,
              "The term in this position must be an object or a type family" ));
        ignore (runDelayed ());
        Jterm tm'
    | Jclass tm ->
        ignore (clearDelayed ());
        let l = Apx.newLVar () in
        let tm', v =
          checkApx
            ( g_,
              tm,
              Apx.Uni l,
              next_ l,
              "The term in this position must be a type or a kind" )
        in
        ignore (filterLevel
            ( tm',
              next_ l,
              3,
              "The term in this position must be a type or a kind" ));
        ignore (runDelayed ());
        Jclass tm'
    | Jof (tm1, tm2) ->
        ignore (clearDelayed ());
        let l = Apx.newLVar () in
        let tm2', v2 =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l,
              next_ l,
              "The term in this position must be a type or a kind" )
        in
        let tm1', u1 =
          checkApx (g_, tm1, v2, l, "Ascription in declaration did not hold")
        in
        ignore (filterLevel
            ( tm1',
              l,
              2,
              "The term in this position must be an object or a type family" ));
        ignore (runDelayed ());
        Jof (tm1', tm2')
    | Jof' (tm1, v) ->
        ignore (clearDelayed ());
        let l = Apx.newLVar () in
        let v2, _ = Apx.classToApx v in
        let tm1', u1 =
          checkApx (g_, tm1, v2, l, "Ascription in declaration did not hold")
        in
        ignore (filterLevel
            ( tm1',
              l,
              2,
              "The term in this position must be an object or a type family" ));
        ignore (runDelayed ());
        Jof' (tm1', v)

  let rec ctxToApx = function
    | IntSyn.Null -> IntSyn.Null
    | IntSyn.Decl (g, IntSyn.NDec x) -> IntSyn.Decl (ctxToApx g, NDec x)
    | IntSyn.Decl (g, IntSyn.Dec (name, v)) ->
        let v', _ = Apx.classToApx v in
        IntSyn.Decl (ctxToApx g, Dec (name, v'))

  let inferApxJob' (g, t) = inferApxJob (ctxToApx g, t)

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

  let elimSub (e, s) (s', s_) = e (IntSyn.comp s s', s_)

  let elimApp (e, u) (s, s_) = e (s, IntSyn.App (eClo (u, s), s_))

  let bvarElim n (s, s_) =
        begin match IntSyn.bvarSub n s with
        | Idx n' -> root_ (bVar n', s_)
        | Exp u -> redex_ (u, s_)
        end

  let fvarElim (name, v, s) (s', s_) = root_ (fVar (name, v, IntSyn.comp s s'), s_)

  let redexElim u (s, s_) = redex_ (eClo (u, s), s_)

  (* headElim (H) = E
     assumes H not Proj _ *)
  let headElim = function
    | IntSyn.BVar n -> bvarElim n
    | IntSyn.FVar (name, v, s) -> fvarElim (name, v, s)
    | IntSyn.NSDef d -> redexElim (IntSyn.constDef d)
    | h ->
        begin match IntSyn.conDecStatus (headConDec h) with
        | Foreign (_, f) -> fun (_, s) -> f s
        | _ -> fun (_, s) -> Root (h, s)
        end

  (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[G]] V) *)
  let evarElim (IntSyn.EVar _ as x) (s, s_) = eClo (x, Whnf.spineToSub s_ s)

  let rec etaExpandW (e, a) = match a with
    | (IntSyn.Pi (((IntSyn.Dec (_, va) as d), _), vr), s) ->
        let u1 = etaExpand (bvarElim 1, (va, IntSyn.comp s IntSyn.shift)) in
        let d' = IntSyn.decSub d s in
        IntSyn.Lam
          ( d',
            etaExpand
              (elimApp (elimSub (e, IntSyn.shift), u1), (vr, IntSyn.dot1 s))
          )
    | _ -> e (IntSyn.id, IntSyn.Nil)

  and etaExpand (e, vs) = etaExpandW (e, Whnf.whnfExpandDef vs)

  (* preserves redices *)
  let toElim = function Elim e -> e | Intro u -> redexElim u

  let toIntro (a, vs) = match a with
    | Elim e -> etaExpand (e, vs)
    | Intro u -> u

  let rec addImplicit1W
      (g, e, (IntSyn.Pi ((IntSyn.Dec (_, va), _), vr), s), i (* >= 1 *)) =
    let x = Whnf.newLoweredEVar g (va, s) in
    addImplicit (g, elimApp (e, x), (vr, Whnf.dotEta (exp_ x) s), i - 1)

  and addImplicit (g, e, vs, i) = match i with
    | 0 -> (e, eClo vs)
    | i -> addImplicit1W (g, e, Whnf.whnfExpandDef vs, i)

  (* if no implicit arguments, do not expand Vs!!! *)
  (* Report mismatches after the entire process finishes -- yields better
     error messages *)
  let reportConstraints xnames =
    withConstPath false (fun () ->
        try
          begin match Print.evarCnstrsToStringOpt xnames with
          | None -> ()
          | Some constr -> print (("Constraints:\n" ^ constr) ^ "\n")
          end
        with unprintable -> print "%_constraints unprintable_%\n")

  let reportInst xnames =
    withConstPath false (fun () ->
        try
          Display.debug (Display.string (Print.evarInstToString xnames ^ "\n"))
        with unprintable ->
          Display.debug (Display.string "%_unifier unprintable_%\n"))

  let delayMismatch (g, v1, v2, r2, location_msg, problem_msg) =
    addDelayed (function () ->
        let xs =
          Abstract.collectEVars
            g (v2, IntSyn.id) (Abstract.collectEVars g (v1, IntSyn.id) [])
        in
        let xnames =
          List.map (function x -> (x, Names.evarName IntSyn.Null x)) xs
        in
        let v1fmt = formatExp g v1 in
        let v2fmt = formatExp g v2 in
        let diff =
          F.vbox0 0 1
            [
              F.string "Expected:";
              F.space;
              v2fmt;
              F.break_;
              F.string "Inferred:";
              F.space;
              v1fmt;
            ]
        in
        let diff =
          begin match Print.evarCnstrsToStringOpt xnames with
          | None -> F.makestring_fmt diff
          | Some cnstrs -> (F.makestring_fmt diff ^ "\nConstraints:\n") ^ cnstrs
          end
        in
        error
          r2 ((((("Type mismatch\n" ^ diff) ^ "\n") ^ problem_msg) ^ "\n")
            ^ location_msg))

  let delayAmbiguous (g, u, r, msg) =
    addDelayed (function () ->
        let ufmt = formatExp g u in
        let amb =
          F.hVbox [ F.string "Inferred:"; F.space; formatExp g u ]
        in
        error
          r ((("Ambiguous reconstruction\n" ^ F.makestring_fmt amb) ^ "\n") ^ msg))

  let unifyIdem (g, us, vs) =
    ignore (Unify.reset ());
    ignore (try Unify.unify g us vs
      with Unify.Unify _ as e ->
        begin
          Unify.unwind ();
          raise e
        end);
    ignore (Unify.reset ());
    ()
  (* this reset should be unnecessary -- for safety only *)

  let unifiableIdem (g, us, vs) =
    ignore (Unify.reset ());
    let ok = Unify.unifiable g us vs in
    ignore begin if ok then Unify.reset () else Unify.unwind ()
      end;
    ok
  (* this reset should be unnecessary -- for safety only *)

  (* tracing code *)
  type traceMode = Progressive | Omniscient

  let trace = ref false
  let traceMode = ref Omniscient

  let report f =
    begin match !traceMode with
    | Progressive -> f ()
    | Omniscient -> addDelayed f
    end

  let reportMismatch (g, vs1, vs2, problem_msg) =
    report (function () ->
        let xs =
          Abstract.collectEVars g vs2 (Abstract.collectEVars g vs1 [])
        in
        let xnames =
          List.map (function x -> (x, Names.evarName IntSyn.Null x)) xs
        in
        let eqnsFmt =
          F.hVbox
            [
              F.string "|?";
              F.space;
              formatExp g (eClo vs1);
              F.break_;
              F.string "=";
              F.space;
              formatExp g (eClo vs2);
            ]
        in
        Display.debug (Display.string (F.makestring_fmt eqnsFmt ^ "\n"));
        ignore (reportConstraints xnames);
        Display.debug
          (Display.string
             ((("Failed: " ^ problem_msg) ^ "\n")
             ^ "Continuing with subterm replaced by _\n"));
        ())

  let reportUnify' (g, vs1, vs2) =
    let xs =
      Abstract.collectEVars g vs2 (Abstract.collectEVars g vs1 [])
    in
    let xnames =
      List.map (function x -> (x, Names.evarName IntSyn.Null x)) xs
    in
    let eqnsFmt =
      F.hVbox
        [
          F.string "|?";
          F.space;
          formatExp g (eClo vs1);
          F.break_;
          F.string "=";
          F.space;
          formatExp g (eClo vs2);
        ]
    in
    Display.debug (Display.string (F.makestring_fmt eqnsFmt ^ "\n"));
    ignore (try unifyIdem (g, vs1, vs2)
      with Unify.Unify msg as e ->
        begin
          Display.debug
            (Display.string
               ((("Failed: " ^ msg) ^ "\n")
               ^ "Continuing with subterm replaced by _\n"));
          raise e
        end);
    ignore (reportInst xnames);
    ignore (reportConstraints xnames);
    ()

  let reportUnify (g, vs1, vs2) =
    begin match !traceMode with
    | Progressive -> reportUnify' (g, vs1, vs2)
    | Omniscient -> (
        try unifyIdem (g, vs1, vs2)
        with Unify.Unify msg as e ->
          begin
            reportMismatch (g, vs1, vs2, msg);
            raise e
          end)
    end

  let rec reportInfer' (g, tm, u, v) = match tm with
    | Omitexact (_, _, r) ->
        let xs =
          Abstract.collectEVars
            g (u, IntSyn.id) (Abstract.collectEVars g (v, IntSyn.id) [])
        in
        let xnames =
          List.map (function x -> (x, Names.evarName IntSyn.Null x)) xs
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
              formatExp g u;
              F.break_;
              F.string ":";
              F.space;
              formatExp g v;
            ]
        in
        Display.debug (Display.string (F.makestring_fmt omit ^ "\n"));
        ignore (reportConstraints xnames);
        ()
    | Mismatch_ (tm1, tm2, _, _) -> reportInfer' (g, tm2, u, v)
    | Hastype_ _ -> ()
    | tm ->
        let xs =
          Abstract.collectEVars
            g (u, IntSyn.id) (Abstract.collectEVars g (v, IntSyn.id) [])
        in
        let xnames =
          List.map (function x -> (x, Names.evarName IntSyn.Null x)) xs
        in
        let judg =
          F.hVbox
            [
              F.string "|-";
              F.space;
              formatExp g u;
              F.break_;
              F.string ":";
              F.space;
              formatExp g v;
            ]
        in
        Display.debug (Display.string (F.makestring_fmt judg ^ "\n"));
        ignore (reportConstraints xnames);
        ()

  let reportInfer x = report (function () -> reportInfer' x)

  (* inferExact (G, tm) = (tm', U, V)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = U-
       and  U : V
       and  U, V are most general such
       effect: as for unification *)
  let rec inferExactN (g, c) = match c with
    | (Internal_ (u, v, r) as tm) -> (tm, Intro u, v)
    | (Constant_ (h, r) as tm) ->
        let cd = headConDec h in
        let e, v =
          addImplicit
            ( g,
              headElim h,
              (IntSyn.conDecType cd, IntSyn.id),
              IntSyn.conDecImp cd )
        in
        (tm, Elim e, v)
    | (Bvar_ (k, r) as tm) ->
        let (Dec (_, v)) = IntSyn.ctxDec g k in
        (tm, Elim (bvarElim k), v)
    | (Evar_ (name, r) as tm) ->
        Debug.(
          msg ~src:Group.approx ~level:Level.Debug
            (Fmt.shown_exact (fun name -> "inferring EVar " ^ name) name));
        let x, v =
          try getEVar (name, false)
          with Apx.Ambiguous ->
            let x, v = getEVar (name, true) in
            delayAmbiguous (g, v, r, "Free variable has ambiguous type");
            (x, v)
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g) in
        (tm, Elim (elimSub (evarElim x, s)), eClo (v, s))
        (* externally EVars are raised elim forms *)
        (* necessary? -kw *)
    | (Fvar_ (name, r) as tm) ->
        Debug.(
          msg ~src:Group.approx ~level:Level.Debug
            (Fmt.shown_exact (fun name -> "inferring FVar " ^ name) name));
        let v =
          try getFVarType (name, false)
          with Apx.Ambiguous ->
            let v = getFVarType (name, true) in
            Debug.(
              msg ~src:Group.approx ~level:Level.Debug
                (Fmt.shown_exact
                   (fun name -> "ambiguous type for FVar " ^ name)
                   name));
            delayAmbiguous (g, v, r, "Free variable has ambiguous type");
            v
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g) in
        (tm, Elim (fvarElim (name, v, s)), EClo (v, s))
        (* necessary? -kw *)
    | (Typ_ r as tm) -> (tm, Intro (IntSyn.Uni Type), IntSyn.Uni Kind)
    | Arrow_ (tm1, tm2) ->
        let tm1', b1, _ (* Uni Type *) = inferExact (g, tm1) in
        let d =
          IntSyn.Dec (None, toIntro (b1, (IntSyn.Uni Type, IntSyn.id)))
        in
        let tm2', b2, l = inferExact (g, tm2) in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        ( Arrow_ (tm1', tm2'),
          Intro (IntSyn.Pi ((d, IntSyn.No), eClo (v2, IntSyn.shift))),
          l )
    | Pi_ (tm1, tm2) ->
        let tm1', d = inferExactDec (g, tm1) in
        let tm2', b2, l = inferExact (decl_ (g, d), tm2) in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        (Pi_ (tm1', tm2'), Intro (IntSyn.Pi ((d, IntSyn.Maybe), v2)), l)
    | Lam_ (tm1, tm2) ->
        let tm1', d = inferExactDec (g, tm1) in
        let tm2', b2, v2 = inferExact (decl_ (g, d), tm2) in
        let u2 = toIntro (b2, (v2, IntSyn.id)) in
        ( Lam_ (tm1', tm2'),
          Intro (IntSyn.Lam (d, u2)),
          IntSyn.Pi ((d, IntSyn.Maybe), v2) )
    | App_ (tm1, tm2) ->
        let tm1', b1, v1 = inferExact (g, tm1) in
        let e1 = toElim b1 in
        Debug.(
          msg' ~src:Group.approx ~level:Level.Debug
          @@ Fmt.concat
               Fmt.
                 [
                   const string "Infering exact application of";
                   using fst pp_term;
                   const string "to";
                   using snd pp_term;
                 ])
          (tm1, tm2);
        let IntSyn.Pi ((IntSyn.Dec (_, va), _), vr), s =
          Whnf.whnfExpandDef (v1, IntSyn.id)
        in
        let tm2', b2 =
          checkExact
            ( g,
              tm2,
              (va, s),
              "Argument type did not match function domain type\n\
               (Index object(s) did not match)" )
        in
        let u2 = toIntro (b2, (va, s)) in
        ( App_ (tm1', tm2'),
          Elim (elimApp (e1, u2)),
          eClo (vr, Whnf.dotEta (exp_ u2) s) )
    | Hastype_ (tm1, tm2) ->
        let tm2', b2, l = inferExact (g, tm2) in
        let v = toIntro (b2, (l, IntSyn.id)) in
        let tm1', b1 =
          checkExact
            ( g,
              tm1,
              (v, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        (Hastype_ (tm1', tm2'), b1, v)
    | Mismatch_ (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, v1 = inferExact (g, tm1) in
        let tm2', b, v = inferExactN (g, tm2) in
        ignore begin if !trace then
            reportMismatch (g, (v1, IntSyn.id), (v, IntSyn.id), problem_msg)
          else ()
          end;
        ignore (delayMismatch (g, v1, v, termRegion tm2', location_msg, problem_msg));
        (Mismatch_ (tm1', tm2', location_msg, problem_msg), b, v)
    | Omitapx (u, v, l, r) ->
        let v' =
          try Apx.apxToClass (g, v, l, false)
          with Ambiguous ->
            let v' = Apx.apxToClass (g, v, l, true) in
            delayAmbiguous
              ( g,
                v',
                r,
                "Omitted term has ambiguous "
                ^ begin match Apx.whnfUni l with
                | Apx.Level 1 -> "type"
                | Apx.Level 2 -> "kind"
                | Apx.Level 3 -> "hyperkind"
                (* yes, this can happen in pathological cases, e.g.
                                a : type. b = a : _ _. *)
                (* FIX: this violates an invariant in printing *)
                end );
            v'
        in
        let u' =
          try Apx.apxToExact (g, u, (v', IntSyn.id), false)
          with Ambiguous ->
            let u' = Apx.apxToExact (g, u, (v', IntSyn.id), true) in
            delayAmbiguous
              ( g,
                u',
                r,
                ("Omitted "
                ^ begin match Apx.whnfUni l with
                | Apx.Level 2 -> "type"
                | Apx.Level 3 -> "kind"
                end)
                ^ " is ambiguous" );
            u'
        in
        (Omitexact (u', v', r), Intro u', v')

  and inferExact (g, tm) =
    begin if not !trace then inferExactN (g, tm)
    else
      let tm', b', v' = inferExactN (g, tm) in
      reportInfer (g, tm', toIntro (b', (v', IntSyn.id)), v');
      (tm', b', v')
    end

  and inferExactDec (g, Dec_ (name, tm, r)) =
    let tm', b1, _ (* Uni Type *) = inferExact (g, tm) in
    let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
    let d = IntSyn.Dec (name, v1) in
    (Dec_ (name, tm', r), d)

  and checkExact1 (g, tm, vhs) = match tm with
    | Lam_ (Dec_ (name, tm1, r), tm2) ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1, _ (* Uni Type *)), ok1 =
          unifyExact (g, tm1, (va, s))
        in
        let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
        let d = IntSyn.Dec (name, v1) in
        let (tm2', b2, v2), ok2 =
          begin if ok1 then
            checkExact1 (decl_ (g, d), tm2, (vr, IntSyn.dot1 s))
          else (inferExact (decl_ (g, d), tm2), false)
          end
        in
        let u2 = toIntro (b2, (v2, IntSyn.id)) in
        ( ( Lam_ (Dec_ (name, tm1', r), tm2'),
            Intro (IntSyn.Lam (d, u2)),
            IntSyn.Pi ((d, IntSyn.Maybe), v2) ),
          ok2 )
    | Hastype_ (tm1, tm2) ->
        let (tm2', b2, l), ok2 = unifyExact (g, tm2, vhs) in
        let v = toIntro (b2, (l, IntSyn.id)) in
        let tm1', b1 =
          checkExact
            ( g,
              tm1,
              (v, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        ((Hastype_ (tm1', tm2'), b1, v), ok2)
    | Mismatch_ (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, v1 = inferExact (g, tm1) in
        let (tm2', b, v), ok2 = checkExact1 (g, tm2, vhs) in
        ignore (delayMismatch (g, v1, v, termRegion tm2', location_msg, problem_msg));
        ((Mismatch_ (tm1', tm2', location_msg, problem_msg), b, v), ok2)
    | Omitapx (u, v, l, r (* = Vhs *)) ->
        let v' = eClo vhs in
        let u' =
          try Apx.apxToExact (g, u, vhs, false)
          with Ambiguous ->
            let u' = Apx.apxToExact (g, u, vhs, true) in
            delayAmbiguous
              ( g,
                u',
                r,
                ("Omitted "
                ^ begin match Apx.whnfUni l with
                | Apx.Level 2 -> "type"
                | Apx.Level 3 -> "kind"
                end)
                ^ " is ambiguous" );
            u'
        in
        ((Omitexact (u', v', r), Intro u', v'), true)
    | tm ->
        let tm', b', v' = inferExact (g, tm) in
        ((tm', b', v'), unifiableIdem (g, vhs, (v', IntSyn.id)))

  and checkExact (g, tm, vs, location_msg) =
    begin if not !trace then
      let (tm', b', v'), ok = checkExact1 (g, tm, vs) in
      begin if ok then (tm', b')
      else
        try
          begin
            unifyIdem (g, (v', IntSyn.id), vs);
            raise Match
          end
          (* can't happen *)
        with Unify.Unify problem_msg ->
          let r = termRegion tm in
          let u' = toIntro (b', (v', IntSyn.id)) in
          let uapx, vapx, lapx = Apx.exactToApx u' v' in
          let (tm'', b'', _ (* Vs *)), _ (* true *) =
            checkExact1 (g, Omitapx (uapx, vapx, lapx, r), vs)
          in
          ignore (delayMismatch (g, v', eClo vs, r, location_msg, problem_msg));
          (Mismatch_ (tm', tm'', location_msg, problem_msg), b'')
      end
    else
      let tm', b', v' = inferExact (g, tm) in
      try
        begin
          reportUnify (g, (v', IntSyn.id), vs);
          (tm', b')
        end
      with Unify.Unify problem_msg ->
        let r = termRegion tm in
        let u' = toIntro (b', (v', IntSyn.id)) in
        let uapx, vapx, lapx = Apx.exactToApx u' v' in
        let tm'', b'' =
          checkExact (g, Omitapx (uapx, vapx, lapx, r), vs, location_msg)
        in
        ignore (delayMismatch (g, v', eClo vs, r, location_msg, problem_msg));
        (Mismatch_ (tm', tm'', location_msg, problem_msg), b'')
    end

  and unifyExact (g, tm, vhs) = match tm with
    | Arrow_ (tm1, tm2) ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1, _ (* Uni Type *)), ok1 =
          unifyExact (g, tm1, (va, s))
        in
        let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
        let d = IntSyn.Dec (None, v1) in
        let tm2', b2, l = inferExact (g, tm2) in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        ( ( Arrow_ (tm1', tm2'),
            Intro (IntSyn.Pi ((d, IntSyn.No), eClo (v2, IntSyn.shift))),
            l ),
          ok1
          && unifiableIdem
               (decl_ (g, d), (vr, IntSyn.dot1 s), (v2, IntSyn.shift)) )
    | Pi_ (Dec_ (name, tm1, r), tm2) ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1, _ (* Uni Type *)), ok1 =
          unifyExact (g, tm1, (va, s))
        in
        let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
        let d = IntSyn.Dec (name, v1) in
        let (tm2', b2, l), ok2 =
          begin if ok1 then unifyExact (decl_ (g, d), tm2, (vr, IntSyn.dot1 s))
          else (inferExact (decl_ (g, d), tm2), false)
          end
        in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        ( ( Pi_ (Dec_ (name, tm1', r), tm2'),
            Intro (IntSyn.Pi ((d, IntSyn.Maybe), v2)),
            l ),
          ok2 )
    | Hastype_ (tm1, tm2) ->
        let ( tm2',
              _,
              _
              (* Uni L *)
              (* Uni (Next L) *) ) =
          inferExact (g, tm2)
        in
        let (tm1', b, l), ok1 = unifyExact (g, tm1, vhs) in
        ((Hastype_ (tm1', tm2'), b, l), ok1)
        (* Vh : L by invariant *)
    | Mismatch_ (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, l1 = inferExact (g, tm1) in
        let (tm2', b, l), ok2 = unifyExact (g, tm2, vhs) in
        ignore (delayMismatch (g, l1, l, termRegion tm2', location_msg, problem_msg));
        ((Mismatch_ (tm1', tm2', location_msg, problem_msg), b, l), ok2)
    | Omitapx
          ( v,
            l,
            nL,
            r
            (* = Vhs *)
            (* Next L *) ) ->
        let l' = Apx.apxToClass (g, l, nL, false) in
        let v' = eClo vhs in
        ((Omitexact (v', l', r), Intro v', l'), true)
        (* cannot raise Ambiguous *)
    | tm ->
        let tm', b', l' = inferExact (g, tm) in
        let v' = toIntro (b', (l', IntSyn.id)) in
        ((tm', b', l'), unifiableIdem (g, vhs, (v', IntSyn.id)))
  (* lam impossible *)

  let rec occElim (tm, os, rs, i) = match tm with
    | Constant_ (h, r) ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) r rs in
        ( Paths.root (r', Paths.leaf r, IntSyn.conDecImp (headConDec h), i, os),
          r' )
        (* should probably treat a constant with Foreign
             attribute as a redex *)
    | Bvar_ (k, r) ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | Fvar_ (name, r) ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | App_ (tm1, tm2) ->
        let oc2, r2 = occIntro tm2 in
        occElim (tm1, Paths.app oc2 os, r2 :: rs, i + 1)
    | Hastype_ (tm1, tm2) -> occElim (tm1, os, rs, i)
    | tm ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) (termRegion tm) rs in
        (Paths.leaf r', r')
  (* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)

  and occIntro = function
    | Arrow_ (tm1, tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join r1 r2 in
        (Paths.bind r' (Some oc1) oc2, r')
    | Pi_ (Dec_ (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join r r2 in
        (Paths.bind r' (Some oc1) oc2, r')
        (* not quite consistent with older implementation for dec0 *)
    | Lam_ (Dec_ (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join r r2 in
        (Paths.bind r' (Some oc1) oc2, r')
        (* not quite consistent with older implementation for dec0 *)
    | Hastype_ (tm1, tm2) -> occIntro tm1
    | tm ->
        let oc, r = occElim (tm, Paths.nils, [], 0) in
        (oc, r)
  (* still doesn't work quite right for the location -> occurrence map? *)

  let rec inferExactJob (g_, a) = match a with
    | Jnothing -> JNothing
    | Jand (j1, j2) -> JAnd (inferExactJob (g_, j1), inferExactJob (g_, j2))
    | Jwithctx (g, j) ->
        let rec ie = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g', gresult = ie g in
              let _, d = inferExactDec (g', tm) in
              (decl_ (g', d), decl_ (gresult, d))
        in
        let g', gresult = ie g in
        JWithCtx (gresult, inferExactJob (g', j))
    | Jterm tm ->
        let tm', b, v = inferExact (g_, tm) in
        let u = toIntro (b, (v, IntSyn.id)) in
        let oc, r = occIntro tm' in
        let rec iu = function
          | IntSyn.Uni Type -> IntSyn.Kind
          | IntSyn.Pi (_, v) -> iu v
          | IntSyn.Root _ -> IntSyn.Type
          | IntSyn.Redex (v, _) -> iu v
          | IntSyn.Lam (_, v) -> iu v
          | IntSyn.EClo (v, _) -> iu v
        in
        JTerm ((u, oc), v, iu v)
        (* others impossible *)
    | Jclass tm ->
        let tm', b, l = inferExact (g_, tm) in
        let v = toIntro (b, (l, IntSyn.id)) in
        let oc, r = occIntro tm' in
        let IntSyn.Uni l, _ = Whnf.whnf (l, IntSyn.id) in
        JClass ((v, oc), l)
    | Jof (tm1, tm2) ->
        let tm2', b2, l2 = inferExact (g_, tm2) in
        let v2 = toIntro (b2, (l2, IntSyn.id)) in
        let tm1', b1 =
          checkExact
            ( g_,
              tm1,
              (v2, IntSyn.id),
              "Ascription in declaration did not hold\n"
              ^ "(Index object(s) did not match)" )
        in
        let u1 = toIntro (b1, (v2, IntSyn.id)) in
        let oc2, r2 = occIntro tm2' in
        let oc1, r1 = occIntro tm1' in
        let IntSyn.Uni l2, _ = Whnf.whnf (l2, IntSyn.id) in
        JOf ((u1, oc1), (v2, oc2), l2)
    | Jof' (tm1, v2) ->
        let tm1', b1 =
          checkExact
            ( g_,
              tm1,
              (v2, IntSyn.id),
              "Ascription in declaration did not hold\n"
              ^ "(Index object(s) did not match)" )
        in
        let u1 = toIntro (b1, (v2, IntSyn.id)) in
        let oc1, r1 = occIntro tm1' in
        JOf ((u1, oc1), (v2, oc1), IntSyn.Type)
  (*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
  (*          val (oc2, r2) = occIntro tm2' *)
  (*          val (Uni L2, _) = Whnf.whnf (L2, id) *)

  let recon' j =
    ignore (Apx.varReset ());
    StringTree.clear evarApxTable;
    StringTree.clear fvarApxTable;
    StringTree.clear fvarTable;
    let j' = inferApxJob (IntSyn.Null, j) in
    ignore (clearDelayed ());
    let j'' = inferExactJob (IntSyn.Null, j') in
    ignore (runDelayed ());
    j''
  (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
  (* context must already have called resetErrors *)
  (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the ""best effort"" result returned, even if there were
             errors *)

  let recon j =
    begin
      queryMode := false;
      recon' j
    end

  let reconQuery j =
    begin
      queryMode := true;
      recon' j
    end

  (* Invariant, G must be named! *)
  let reconWithCtx' (g, j) =
    ignore (Apx.varReset ());
    ignore (varReset ());
    let j' = inferApxJob' (g, j) in
    ignore (clearDelayed ());
    let j'' = inferExactJob (g, j') in
    ignore (runDelayed ());
    j''
  (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
  (* context must already have called resetErrors *)
  (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the ""best effort"" result returned, even if there were
             errors *)

  let reconWithCtx g j =
    begin
      queryMode := false;
      reconWithCtx' (g, j)
    end

  let reconQueryWithCtx g j =
    begin
      queryMode := true;
      reconWithCtx' (g, j)
    end

  let internalInst x = raise Match
  let externalInst x = raise Match
end
(* open IntSyn *)
(* functor ReconTerm *)

(* # 1 "src/frontend/ReconTerm.sml.ml" *)
