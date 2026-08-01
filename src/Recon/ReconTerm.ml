open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Table
open! Table.Table_
open! Msg
open! Msg.Msg_
open! Print
open! Print.Print_
open! Debug

exception Error of string

(* Logic copied from src/frontend/ReconTerm.ml.
   The functor takes a second parameter R for the modules that are not in S.S.
   See "Problems" comment at the bottom of this file. *)
module Make_ReconTerm
    (M : S.S)
    (R : sig
      module Names : NAMES
      module Approx : APPROX
      module Whnf : WHNF
      module Unify : UNIFY
      module Abstract : ABSTRACT
      module Print : PRINT
      module StringTree : TABLE with type key = string
      module Msg : MSG
      module CsManager : Solvers.CSMANAGER.CS_MANAGER
    end) =
struct
  module M = M
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Syntax = M.Syntax
  module Names = R.Names
  module Approx = R.Approx
  module Whnf = R.Whnf
  module Unify = R.Unify
  module Abstract = R.Abstract
  module Print = R.Print
  module StringTree = R.StringTree
  module Msg = R.Msg
  module CsManager = R.CsManager

  let loc_to_region : Cst.loc -> Paths.region = Cst.loc_to_region

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
  let errorThreshold = ref (Some 200)
  let exceeds = function i, None -> false | i, Some j -> i > j

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

  let rec chatterOneNewline () =
    begin if !Global.chatter = 1 && !errorCount = 1 then
      Display.debug (Display.string "\n")
    else ()
    end

  (* Both of these report a *type error*, so both emit exactly one message, at
     kind Error.

     They used to use Display.debug for the located text -- which the CLI maps
     to a green "note:" -- and [error] additionally emitted the bare message a
     second time via Display.warning. The result was every type error printed
     twice, once as a note carrying the location and once as a warning without
     it, and never once as an error. The located form is the one worth keeping:
     it is the only one that says where the problem is. *)
  let located (r, msg) =
    Display.string (((!errorFileName ^ ":") ^ Paths.wrap r msg) ^ "\n")

  let fatalError (r, msg) =
    begin
      errorCount := !errorCount + 1;
      begin
        chatterOneNewline ();
        begin
          Display.error (located (r, msg));
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
          Display.error (located (r, msg));
          begin if exceeds (!errorCount, !errorThreshold) then die r else ()
          end
        end
      end
    end

  let formatExp g_ u_ =
    try Print.formatExp g_ u_
    with Names.Unprintable -> F.string "%_unprintable_%"

  (* this is a hack, i know *)
  let queryMode = ref false
  let decl a1 b1 = match a1, b1 with g_, d_ -> IntSyn.Decl (g_, d_)
  let eClo = function v_, s -> IntSyn.EClo (v_, s)
  let root = function h_, s_ -> IntSyn.Root (h_, s_)
  let bVar n = IntSyn.BVar n
  let redex = function u_, s_ -> IntSyn.Redex (u_, s_)
  let fVar = function name, v_, s -> IntSyn.FVar (name, v_, s)
  let exp u_ = IntSyn.Exp u_
  let undefined = Apx.Undefined
  let uni l_ = Apx.Uni (Apx.uniToApx l_)
  let kind = Apx.kind
  let hyperkind = Apx.hyperkind
  let next l_ = Apx.Next l_

  let headConDec (h_ : IntSyn.head) =
    begin match h_ with
    | IntSyn.Const c -> IntSyn.sgnLookup c
    | IntSyn.Skonst c -> IntSyn.sgnLookup c
    | IntSyn.Def d -> IntSyn.sgnLookup d
    | IntSyn.NSDef d -> IntSyn.sgnLookup d
    | IntSyn.FgnConst (_, cd) -> cd
    end

  let rec lowerTypeW = function
    | g_, (IntSyn.Pi ((d_, _), v_), s) ->
        let d'_ = IntSyn.decSub d_ s in
        lowerType (decl g_ d'_, (v_, IntSyn.dot1 s))
    | g_, vs_ -> (g_, eClo vs_)

  and lowerType (g_, vs_) = lowerTypeW (g_, Whnf.whnfExpandDef vs_)

  let rec raiseType a1 b1 = match a1, b1 with
    | IntSyn.Null, v_ -> v_
    | IntSyn.Decl (g_, d_), v_ ->
        raiseType g_ (IntSyn.Pi ((d_, IntSyn.Maybe), v_))

  let evarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarTable : IntSyn.exp StringTree.table = StringTree.new_ 0

  let getEVarTypeApx name =
    begin match StringTree.lookup evarApxTable name with
    | Some v_ -> v_
    | None ->
        begin match Names.getEVarOpt name with
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

  let getFVarTypeApx name =
    begin match StringTree.lookup fvarApxTable name with
    | Some v_ ->
        msg ~src:Group.approx ~level:Level.Debug
          (Fmt.shown_exact
             (fun name -> "getFVarTypeApx: found existing for " ^ name)
             name);
        v_
    | None ->
        let v_ = Apx.newCVar () in
        msg ~src:Group.approx ~level:Level.Debug
          (Fmt.shown_exact
             (fun name -> "getFVarTypeApx: creating fresh CVar for " ^ name)
             name);
        begin
          StringTree.insert fvarApxTable (name, v_);
          v_
        end
    end

  let getEVar (name, allowed) =
    begin match Names.getEVarOpt name with
    | Some (IntSyn.EVar (_, g_, v_, _) as x_) -> (x_, raiseType g_ v_)
    | None ->
        let v_ = Option.valOf (StringTree.lookup evarApxTable name) in
        let v'_ = Apx.apxToClass (IntSyn.Null, v_, Apx.(Level 1), allowed) in
        let g''_, v'' = lowerType (IntSyn.Null, (v'_, IntSyn.id)) in
        let x_ = IntSyn.newEVar g''_ v'' in
        begin
          Names.addEVar x_ name;
          (x_, v'_)
        end
    end

  let getFVarType (name, allowed) =
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

  (* Internal term type — richer than Cst.term; includes reconstruction-internal nodes *)
  type term =
    | Internal of IntSyn.exp * IntSyn.exp * Paths.region
    | Constant of IntSyn.head * Paths.region
    | Bvar of int * Paths.region
    | Evar of string * Paths.region
    | Fvar of string * Paths.region
    | Typ of Paths.region
    | Arrow of term * term
    | Pi of dec * term
    | Lam of dec * term
    | App of term * term
    | Hastype of term * term
    | Mismatch of term * term * string * string
    | Omitted of Paths.region
    | Lcid of string list * string * Paths.region
    | Ucid of string list * string * Paths.region
    | Quid of string list * string * Cst.qid_form * Paths.region
    | Scon of string * Paths.region
    | Omitapx of Apx.exp * Apx.exp * Apx.uni * Paths.region
    | Omitexact of IntSyn.exp * IntSyn.exp * Paths.region
  [@@deriving show { with_path = false }]

  and dec = Dec of string option * term * Paths.region

  let lcid ids name r = Lcid (ids, name, r)
  let ucid ids name r = Ucid (ids, name, r)
  let quid (ids, name, form, r) = Quid (ids, name, form, r)
  let scon value r = Scon (value, r)
  let evar name r = Evar (name, r)
  let fvar name r = Fvar (name, r)
  let typ r = Typ r
  let arrow tm1 tm2 = Arrow (tm1, tm2)
  let pi d tm = Pi (d, tm)
  let lam d tm = Lam (d, tm)
  let app tm1 tm2 = App (tm1, tm2)
  let hastype tm1 tm2 = Hastype (tm1, tm2)
  let omitted r = Omitted r
  let dec (nameOpt, tm, r) = Dec (nameOpt, tm, r)
  let backarrow tm1 tm2 = Arrow (tm2, tm1)
  let dec0 nameOpt r = Dec (nameOpt, Omitted r, r)

  (* Unreconstructed job — uses the richer internal term/dec *)
  type t =
    | Jnothing
    | Jand of t * t
    | Jwithctx of dec IntSyn.ctx * t
    | Jterm of term
    | Jclass of term
    | Jof of term * term

  let jnothing = Jnothing
  let jand j1 j2 = Jand (j1, j2)

  (* Conversions from Cst types to internal types.
     Uses View observers because Cst.term/decl are abstract in the CST signature. *)

  (* Walk a Cst.term and qualify unresolved lowercase/uppercase names that exist
     in ns_comps under ns_path.  Used to implement %local NS EXPR desugaring:
     names found in NS are prefixed with NS's path; everything else is unchanged. *)
  let desugar_local (ns_path : string list) (ns_comps : Names.namespace)
      (t : Cst.term) : Cst.term =
    let module V = Cst.View in
    let exists_in_ns name =
      Names.constLookupIn ns_comps (Names.Qid ([], name)) <> None
    in
    let qualify_lower loc ns name =
      match ns with
      | _ :: _ -> V.Term.(review @@ Lowercase (loc, (ns, name)))
      | [] ->
          let ns' = if exists_in_ns name then ns_path else [] in
          V.Term.(review @@ Lowercase (loc, (ns', name)))
    in
    let qualify_upper loc ns name =
      match ns with
      | _ :: _ -> V.Term.(review @@ Uppercase (loc, (ns, name)))
      | [] ->
          let ns' = if exists_in_ns name then ns_path else [] in
          V.Term.(review @@ Uppercase (loc, (ns', name)))
    in
    let rec go t =
      match V.Term.view t with
      | V.Term.Lowercase (loc, (ns, name)) -> qualify_lower loc ns name
      | V.Term.Uppercase (loc, (ns, name)) -> qualify_upper loc ns name
      | V.Term.Arrow (loc, a, b) -> V.Term.(review @@ Arrow (loc, go a, go b))
      | V.Term.BackArrow (loc, b, a) ->
          V.Term.(review @@ BackArrow (loc, go b, go a))
      | V.Term.Pi (loc, decls, body) ->
          V.Term.(review @@ Pi (loc, List.map go_decl decls, go body))
      | V.Term.Lam (loc, decls, body) ->
          V.Term.(review @@ Lam (loc, List.map go_decl decls, go body))
      | V.Term.App (loc, head, args) ->
          V.Term.(review @@ App (loc, go head, List.map go args))
      | V.Term.HasType (loc, a, b) ->
          V.Term.(review @@ HasType (loc, go a, go b))
      | V.Term.Local (loc, ns2, inner) ->
          V.Term.(review @@ Local (loc, ns2, go inner))
      | other -> V.Term.review other
    and go_decl d =
      match V.Decl.view d with
      | V.Decl.Decl1 (loc, names, ty, def) ->
          V.Decl.(review @@ Decl1 (loc, names, go ty, def))
      | V.Decl.Decl0 (loc, names, ty) ->
          V.Decl.(review @@ Decl0 (loc, names, go ty))
    in
    go t

  let rec cst_term_to_term (t : Cst.term) : term =
    let module V = Cst.View in
    let ghost_r = loc_to_region Cst.ghost in
    let rec fold_pi decls body =
      match decls with
      | [] -> body
      | d :: rest ->
          Stdlib.List.fold_right
            (fun dec acc -> Pi (dec, acc))
            (cst_decl_to_decs d) (fold_pi rest body)
    in
    let rec fold_lam decls body =
      match decls with
      | [] -> body
      | d :: rest ->
          Stdlib.List.fold_right
            (fun dec acc -> Lam (dec, acc))
            (cst_decl_to_decs d) (fold_lam rest body)
    in
    let rec fold_app head args =
      match args with
      | [] -> head
      | a :: rest -> fold_app (App (head, cst_term_to_term a)) rest
    in
    match V.Term.view t with
    | V.Term.Arrow (_, a, b) -> Arrow (cst_term_to_term a, cst_term_to_term b)
    | V.Term.BackArrow (_, b, a) ->
        Arrow (cst_term_to_term a, cst_term_to_term b)
    | V.Term.Pi (_, decls, body) -> fold_pi decls (cst_term_to_term body)
    | V.Term.Lam (_, decls, body) -> fold_lam decls (cst_term_to_term body)
    | V.Term.App (_, head, args) -> fold_app (cst_term_to_term head) args
    | V.Term.HasType (_, a, b) ->
        Hastype (cst_term_to_term a, cst_term_to_term b)
    | V.Term.Lowercase (loc, (ns, n)) -> Lcid (ns, n, loc_to_region loc)
    | V.Term.Uppercase (loc, (ns, n)) -> Ucid (ns, n, loc_to_region loc)
    | V.Term.Qualified (loc, (ns, n), form) ->
        Quid (ns, n, form, loc_to_region loc)
    | V.Term.Text (loc, s) -> Scon (s, loc_to_region loc)
    | V.Term.ExistVar (loc, s) -> Evar (s, loc_to_region loc)
    | V.Term.FreeVar (loc, s) -> Fvar (s, loc_to_region loc)
    | V.Term.Typ loc -> Typ (loc_to_region loc)
    | V.Term.Local (_, ns_path, inner) ->
        let qid =
          match List.rev ns_path with
          | [] -> failwith "%local: empty namespace path"
          | last :: prefix -> Names.Qid (List.rev prefix, last)
        in
        let ns_comps =
          match Names.structLookup qid with
          | Some mid -> Names.getComponents mid
          | None -> Names.newNamespace ()
        in
        cst_term_to_term (desugar_local ns_path ns_comps inner)
    | _ -> Omitted ghost_r

  and cst_decl_to_dec (d : Cst.decl) : dec =
    let names, tm, loc =
      match Cst.View.Decl.view d with
      | Cst.View.Decl.Decl1 (loc, names, tm, _) -> (names, tm, loc)
      | Cst.View.Decl.Decl0 (loc, names, tm) -> (names, tm, loc)
      | _ -> assert false
    in
    (* Cst.decl allows a list of names; internal dec has one name option.
       Callers needing every name (e.g. Pi/Lam binders) use
       [cst_decl_to_decs] instead. *)
    let name_opt = match names with [] -> None | n :: _ -> n in
    Dec (name_opt, cst_term_to_term tm, loc_to_region loc)

  and cst_decl_to_decs (d : Cst.decl) : dec list =
    (* Expands a multi-name decl like [(X Y Z) T] into one [dec] per name,
       all sharing [T] -- so {(X Y Z) T} body / [(X Y Z) T] body produce a
       nested binder per name instead of just the first. *)
    let names, tm, loc =
      match Cst.View.Decl.view d with
      | Cst.View.Decl.Decl1 (loc, names, tm, _) -> (names, tm, loc)
      | Cst.View.Decl.Decl0 (loc, names, tm) -> (names, tm, loc)
      | _ -> assert false
    in
    let tm' = cst_term_to_term tm in
    let r = loc_to_region loc in
    match names with
    | [] -> [ Dec (None, tm', r) ]
    | _ -> List.map (fun name_opt -> Dec (name_opt, tm', r)) names

  let jwithctx g j =
    let rec cvt = function
      | Ast.Null -> IntSyn.Null
      | Ast.Decl (g', d) -> IntSyn.Decl (cvt g', cst_decl_to_dec d)
    in
    Jwithctx (cvt g, j)

  let jterm tm = Jterm (cst_term_to_term tm)
  let jclass tm = Jclass (cst_term_to_term tm)
  let jof tm1 tm2 = Jof (cst_term_to_term tm1, cst_term_to_term tm2)

  (* Internal region functions operating on the internal term/dec types *)
  let rec termRegion_ = function
    | Internal (u_, v_, r) -> r
    | Constant (h_, r) -> r
    | Bvar (k, r) -> r
    | Evar (name, r) -> r
    | Fvar (name, r) -> r
    | Typ r -> r
    | Arrow (tm1, tm2) -> Paths.join (termRegion_ tm1) (termRegion_ tm2)
    | Pi (tm1, tm2) -> Paths.join (decRegion_ tm1) (termRegion_ tm2)
    | Lam (tm1, tm2) -> Paths.join (decRegion_ tm1) (termRegion_ tm2)
    | App (tm1, tm2) -> Paths.join (termRegion_ tm1) (termRegion_ tm2)
    | Hastype (tm1, tm2) -> Paths.join (termRegion_ tm1) (termRegion_ tm2)
    | Mismatch (tm1, tm2, _, _) -> termRegion_ tm2
    | Omitted r -> r
    | Lcid (_, _, r) -> r
    | Ucid (_, _, r) -> r
    | Quid (_, _, _, r) -> r
    | Scon (_, r) -> r
    | Omitapx (u_, v_, l_, r) -> r
    | Omitexact (u_, v_, r) -> r

  and decRegion_ (Dec (name, tm, r)) = r

  let rec ctxRegion_internal = function
    | IntSyn.Null -> None
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, decRegion_ tm)

  and ctxRegion' = function
    | IntSyn.Null, r -> Some r
    | IntSyn.Decl (g, tm), r -> ctxRegion' (g, Paths.join r (decRegion_ tm))

  let ctxRegion (g : Cst.decl Ast.ctx) : Paths.region option =
    let rec cvt = function
      | Ast.Null -> IntSyn.Null
      | Ast.Decl (g', d) -> IntSyn.Decl (cvt g', cst_decl_to_dec d)
    in
    ctxRegion_internal (cvt g)

  (* Inside reconstruction logic, termRegion operates on internal term type *)
  let termRegion = termRegion_

  type apx_dec = Dec of string option * Apx.exp | NDec of string option

  open Apx

  let filterLevel (tm, l_, max, msg) =
    let notGround = Apx.makeGroundUni l_ in
    let (Apx.Level i) = Apx.whnfUni l_ in
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

  let findOmitted (g_, qid, r) =
    begin
      error
        r ("Undeclared identifier "
          ^ Names.qidToString (valOf (Names.constUndef qid)));
      Omitted r
    end

  let rec findBVar' = function
    | IntSyn.Null, name, k -> None
    | IntSyn.Decl (g_, Dec (None, _)), name, k -> findBVar' (g_, name, k + 1)
    | IntSyn.Decl (g_, NDec _), name, k -> findBVar' (g_, name, k + 1)
    | IntSyn.Decl (g_, Dec (Some name', _)), name, k ->
        begin if name = name' then Some k else findBVar' (g_, name, k + 1)
        end

  let findBVar fc (g_, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g_, qid, r)
    | Some name ->
        begin match findBVar' (g_, name, 1) with
        | None -> fc (g_, qid, r)
        | Some k -> Bvar (k, r)
        end
    end

  let findConst ?(shortest = false) fc (g_, qid, r) =
    begin match Names.resolveQid ~shortest qid with
    | None -> fc (g_, qid, r)
    | Some cid ->
        begin match IntSyn.sgnLookup cid with
        | IntSyn.ConDec _ -> Constant (IntSyn.Const cid, r)
        | IntSyn.ConDef _ -> Constant (IntSyn.Def cid, r)
        | IntSyn.AbbrevDef _ -> Constant (IntSyn.NSDef cid, r)
        | _ -> begin
            error
              r ((("Invalid identifier\n" ^ "Identifier `")
                ^ Names.qidToString qid)
                ^ "' is not a constant, definition or abbreviation");
            Omitted r
          end
        end
    end

  let findCSConst fc (g_, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g_, qid, r)
    | Some name ->
        begin match CsManager.parse name with
        | None -> fc (g_, qid, r)
        | Some (cs, conDec) -> Constant (IntSyn.FgnConst (cs, conDec), r)
        end
    end

  let findEFVar fc (g_, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g_, qid, r)
    | Some name ->
        begin if !queryMode || String.isPrefix "__" name then Evar (name, r)
        else Fvar (name, r)
        end
    end

  let findLCID x = findBVar (findConst (findCSConst findOmitted)) x
  let findUCID x = findBVar (findConst (findCSConst (findEFVar findOmitted))) x

  let findQUID form x =
    findConst ~shortest:(form = Cst.Abs) (findCSConst findOmitted) x

  let rec inferApx = function
    | g_, (Internal (u_, v_, r) as tm) ->
        let u'_, v'_, l'_ = Apx.exactToApx u_ v_ in
        (tm, u'_, v'_, l'_)
    | g_, (Lcid (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g_, findLCID (g_, qid, r))
    | g_, (Ucid (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g_, findUCID (g_, qid, r))
    | g_, (Quid (ids, name, form, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g_, findQUID form (g_, qid, r))
    | g_, (Scon (name, r) as tm) ->
        begin match CsManager.parse name with
        | None -> begin
            error r ("Strings unsupported in current signature");
            inferApx (g_, Omitted r)
          end
        | Some (cs, conDec) ->
            inferApx (g_, Constant (IntSyn.FgnConst (cs, conDec), r))
        end
    | g_, (Constant (h_, r) as tm) ->
        let cd = headConDec h_ in
        let u'_, v'_, l'_ =
          Apx.exactToApx (IntSyn.Root (h_, IntSyn.Nil)) (IntSyn.conDecType cd)
        in
        let rec dropImplicit = function
          | v_, 0 -> v_
          | Apx.Arrow (_, v_), i -> dropImplicit (v_, i - 1)
        in
        let v'' = dropImplicit (v'_, IntSyn.conDecImp cd) in
        (tm, u'_, v'', l'_)
    | g_, (Bvar (k, r) as tm) ->
        let (Dec (_, v_)) = IntSyn.ctxLookup g_ k in
        (tm, undefined, v_, Apx.(Level 1))
    | g_, (Evar (name, r) as tm) ->
        (tm, undefined, getEVarTypeApx name, Apx.(Level 1))
    | g_, (Fvar (name, r) as tm) ->
        (tm, undefined, getFVarTypeApx name, Apx.(Level 1))
    | g_, (Typ r as tm) -> (tm, uni Type, Apx.Uni kind, hyperkind)
    | g_, Arrow (tm1, tm2) ->
        let l_ = Apx.newLVar () in
        let tm1', v1_ =
          checkApx
            (g_, tm1, uni Type, kind, "Left-hand side of arrow must be a type")
        in
        let tm2', v2_ =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l_,
              next l_,
              "Right-hand side of arrow must be a type or a kind" )
        in
        (Arrow (tm1', tm2'), Arrow (v1_, v2_), Apx.Uni l_, next l_)
    | g_, Pi (tm1, tm2) ->
        let tm1', (Dec (_, v1_) as d_) = inferApxDec (g_, tm1) in
        let l_ = Apx.newLVar () in
        let tm2', v2_ =
          checkApx
            ( decl g_ d_,
              tm2,
              Apx.Uni l_,
              next l_,
              "Body of pi must be a type or a kind" )
        in
        (Pi (tm1', tm2'), Arrow (v1_, v2_), Apx.Uni l_, next l_)
    | g_, (Lam (tm1, tm2) as tm) ->
        let tm1', (Dec (_, v1_) as d_) = inferApxDec (g_, tm1) in
        let tm2', u2_, v2_, l2_ = inferApx (decl g_ d_, tm2) in
        (Lam (tm1', tm2'), u2_, Arrow (v1_, v2_), l2_)
    | g_, (App (tm1, tm2) as tm) ->
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
        let l_ = Apx.newLVar () in
        let va = Apx.newCVar () in
        let vr = Apx.newCVar () in
        let tm1', u1_ =
          checkApx
            ( g_,
              tm1,
              Arrow (va, vr),
              l_,
              "Non-function was applied to an argument" )
        in
        let tm2', _ =
          checkApx
            ( g_,
              tm2,
              va,
              Apx.(Level 1),
              "Argument type did not match function domain type" )
        in
        (App (tm1', tm2'), u1_, vr, l_)
    | g_, (Hastype (tm1, tm2) as tm) ->
        let l_ = Apx.newLVar () in
        let tm2', v2_ =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l_,
              next l_,
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
        (Hastype (tm1', tm2'), u1_, v2_, l_)
    | g_, Omitted r ->
        let l_ = Apx.newLVar () in
        let v_ = Apx.newCVar () in
        let u_ = Apx.newCVar () in
        (Omitapx (u_, v_, l_, r), u_, v_, l_)

  and checkApx (g_, tm, v_, l_, location_msg) =
    let tm', u'_, v'_, l'_ = inferApx (g_, tm) in
    try
      begin
        Apx.matchUni l_ l'_;
        begin
          Apx.match_ (v_, v'_);
          (tm', u'_)
        end
      end
    with Apx.Unify problem_msg ->
      begin
        let r = termRegion tm in
        let tm'', u'' = checkApx (g_, Omitted r, v_, l_, location_msg) in
        ignore (addDelayed (fun () -> ignore (Apx.makeGroundUni l'_)));
        (Mismatch (tm', tm'', location_msg, problem_msg), u'')
      end

  and inferApxDec (g_, Dec (name, tm, r)) =
    let tm', v1_ =
      checkApx
        (g_, tm, uni Type, kind, "Classifier in declaration must be a type")
    in
    let d_ = Dec (name, v1_) in
    (Dec (name, tm', r), d_)

  let rec inferApxJob = function
    | g_, Jnothing -> Jnothing
    | g_, Jand (j1, j2) -> Jand (inferApxJob (g_, j1), inferApxJob (g_, j2))
    | g_, Jwithctx (g, j) ->
        let rec ia = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g'_, g' = ia g in
              ignore (clearDelayed ());
              let tm', d_ = inferApxDec (g'_, tm) in
              ignore (runDelayed ());
              (decl g'_ d_, decl g' tm')
        in
        let g'_, g' = ia g in
        Jwithctx (g', inferApxJob (g'_, j))
    | g_, Jterm tm ->
        ignore (clearDelayed ());
        let tm', u_, v_, l_ = inferApx (g_, tm) in
        let _ =
          filterLevel
            ( tm',
              l_,
              2,
              "The term in this position must be an object or a type family" )
        in
        ignore (runDelayed ());
        Jterm tm'
    | g_, Jclass tm ->
        ignore (clearDelayed ());
        let l_ = Apx.newLVar () in
        let tm', v_ =
          checkApx
            ( g_,
              tm,
              Apx.Uni l_,
              next l_,
              "The term in this position must be a type or a kind" )
        in
        let _ =
          filterLevel
            ( tm',
              next l_,
              3,
              "The term in this position must be a type or a kind" )
        in
        ignore (runDelayed ());
        Jclass tm'
    | g_, Jof (tm1, tm2) ->
        ignore (clearDelayed ());
        let l_ = Apx.newLVar () in
        let tm2', v2_ =
          checkApx
            ( g_,
              tm2,
              Apx.Uni l_,
              next l_,
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
        ignore (runDelayed ());
        Jof (tm1', tm2')

  (* Fully reconstructed job *)
  type result =
    | JNothing
    | JAnd of result * result
    | JWithCtx of IntSyn.dec IntSyn.ctx * result
    | JTerm of (IntSyn.exp * Paths.occExp) * IntSyn.exp * IntSyn.uni
    | JClass of (IntSyn.exp * Paths.occExp) * IntSyn.uni
    | JOf of
        (IntSyn.exp * Paths.occExp) * (IntSyn.exp * Paths.occExp) * IntSyn.uni

  type bidi =
    | Elim of (IntSyn.sub * IntSyn.spine -> IntSyn.exp)
    | Intro of IntSyn.exp

  let elimSub (e_, s) = function s', s_ -> e_ (IntSyn.comp s s', s_)

  let elimApp (e_, u_) = function
    | s, s_ -> e_ (s, IntSyn.App (eClo (u_, s), s_))

  let bvarElim n = function
    | s, s_ ->
        begin match IntSyn.bvarSub n s with
        | Idx n' -> root (bVar n', s_)
        | Exp u_ -> redex (u_, s_)
        end

  let fvarElim (name, v_, s) = function
    | s', s_ -> root (fVar (name, v_, IntSyn.comp s s'), s_)

  let redexElim u_ = function s, s_ -> redex (eClo (u_, s), s_)

  let headElim = function
    | IntSyn.BVar n -> bvarElim n
    | IntSyn.FVar (name, v_, s) -> fvarElim (name, v_, s)
    | IntSyn.NSDef d -> redexElim (IntSyn.constDef d)
    | h_ ->
        begin match IntSyn.conDecStatus (headConDec h_) with
        | Foreign (_, f) -> fun (_, s_) -> f s_
        | _ -> fun (_, s_) -> Root (h_, s_)
        end

  let evarElim (IntSyn.EVar _ as x_) = function
    | s, s_ -> eClo (x_, Whnf.spineToSub s_ s)

  let rec etaExpandW = function
    | e_, (IntSyn.Pi (((IntSyn.Dec (_, va) as d_), _), vr), s) ->
        let u1_ = etaExpand (bvarElim 1, (va, IntSyn.comp s IntSyn.shift)) in
        let d'_ = IntSyn.decSub d_ s in
        IntSyn.Lam
          ( d'_,
            etaExpand
              (elimApp (elimSub (e_, IntSyn.shift), u1_), (vr, IntSyn.dot1 s))
          )
    | e_, _ -> e_ (IntSyn.id, IntSyn.Nil)

  and etaExpand (e_, vs_) = etaExpandW (e_, Whnf.whnfExpandDef vs_)

  let toElim = function Elim e_ -> e_ | Intro u_ -> redexElim u_

  let toIntro = function
    | Elim e_, vs_ -> etaExpand (e_, vs_)
    | Intro u_, vs_ -> u_

  let rec addImplicit1W
      (g_, e_, (IntSyn.Pi ((IntSyn.Dec (_, va), _), vr), s), i (* >= 1 *)) =
    let x_ = Whnf.newLoweredEVar g_ (va, s) in
    addImplicit (g_, elimApp (e_, x_), (vr, Whnf.dotEta (exp x_) s), i - 1)

  and addImplicit = function
    | g_, e_, vs_, 0 -> (e_, eClo vs_)
    | g_, e_, vs_, i -> addImplicit1W (g_, e_, Whnf.whnfExpandDef vs_, i)

  let reportConstraints xnames =
    try
      begin match Print.evarCnstrsToStringOpt xnames with
      | None -> ()
      | Some constr ->
          Display.debug ~level:Display.Level.verbose
            (Display.Form.string (("Constraints:\n" ^ constr) ^ "\n"))
      end
    with Names.Unprintable ->
      Display.debug ~level:Display.Level.verbose
        (Display.Form.string "%_constraints unprintable_%\n")

  let reportInst xnames =
    try
      Display.debug ~level:Display.Level.verbose
        (Display.Form.string (Print.evarInstToString xnames ^ "\n"))
    with Names.Unprintable ->
      Display.debug ~level:Display.Level.verbose
        (Display.Form.string "%_unifier unprintable_%\n")

  let delayMismatch (g_, v1_, v2_, r2, location_msg, problem_msg) =
    addDelayed (function () ->
        let xs_ =
          Abstract.collectEVars
            g_ (v2_, IntSyn.id) (Abstract.collectEVars g_ (v1_, IntSyn.id) [])
        in
        let xnames =
          List.map (function x_ -> (x_, Names.evarName IntSyn.Null x_)) xs_
        in
        let v1fmt = formatExp g_ v1_ in
        let v2fmt = formatExp g_ v2_ in
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

  let delayAmbiguous (g_, u_, r, msg) =
    addDelayed (function () ->
        let ufmt = formatExp g_ u_ in
        let amb =
          F.hVbox [ F.string "Inferred:"; F.space; formatExp g_ u_ ]
        in
        let fstr = F.makestring_fmt amb in
        Display.debug ~level:Display.Level.verbose
          Display.Form.(
            nl ()
            ++ string "Ambiguous reconstruction of term: "
            ++ string fstr ++ nl ());
        error r ((("Ambiguous reconstruction\n" ^ fstr) ^ "\n") ^ msg))

  let unifyIdem x =
    ignore (Unify.reset ());
    let _ =
      try Unify.unify x
      with Unify.Unify _ as e ->
        begin
          Unify.unwind ();
          raise e
        end
    in
    ignore (Unify.reset ());
    ()

  let unifiableIdem x =
    ignore (Unify.reset ());
    let ok = Unify.unifiable x in
    let _ =
      begin if ok then Unify.reset () else Unify.unwind ()
      end
    in
    ok

  (* tracing code *)
  type traceMode = Progressive | Omniscient

  let trace = ref false
  let traceMode = ref Omniscient

  let report f =
    begin match !traceMode with
    | Progressive -> f ()
    | Omniscient -> addDelayed f
    end

  let reportMismatch (g_, vs1, vs2, problem_msg) =
    report (function () ->
        let xs_ =
          Abstract.collectEVars g_ vs2 (Abstract.collectEVars g_ vs1 [])
        in
        let xnames =
          List.map (function x_ -> (x_, Names.evarName IntSyn.Null x_)) xs_
        in
        let eqnsFmt =
          F.hVbox
            [
              F.string "|?";
              F.space;
              formatExp g_ (eClo vs1);
              F.break_;
              F.string "=";
              F.space;
              formatExp g_ (eClo vs2);
            ]
        in
        let _ =
          Display.debug ~level:Display.Level.debug
            (Display.Form.string (F.makestring_fmt eqnsFmt ^ "\n"))
        in
        ignore (reportConstraints xnames);
        let _ =
          Display.debug ~level:Display.Level.debug
            (Display.Form.string
               ((("Failed: " ^ problem_msg) ^ "\n")
               ^ "Continuing with subterm replaced by _\n"))
        in
        ())

  let reportUnify' (g_, vs1, vs2) =
    let xs_ =
      Abstract.collectEVars g_ vs2 (Abstract.collectEVars g_ vs1 [])
    in
    let xnames =
      List.map (function x_ -> (x_, Names.evarName IntSyn.Null x_)) xs_
    in
    let eqnsFmt =
      F.hVbox
        [
          F.string "|?";
          F.space;
          formatExp g_ (eClo vs1);
          F.break_;
          F.string "=";
          F.space;
          formatExp g_ (eClo vs2);
        ]
    in
    let _ =
      Display.debug ~level:Display.Level.debug
        (Display.Form.string (F.makestring_fmt eqnsFmt ^ "\n"))
    in
    let _ =
      try unifyIdem (g_, vs1, vs2)
      with Unify.Unify msg as e ->
        begin
          Display.debug ~level:Display.Level.debug
            (Display.Form.string
               ((("Failed: " ^ msg) ^ "\n")
               ^ "Continuing with subterm replaced by _\n"));
          raise e
        end
    in
    ignore (reportInst xnames);
    ignore (reportConstraints xnames);
    ()

  let reportUnify (g_, vs1, vs2) =
    begin match !traceMode with
    | Progressive -> reportUnify' (g_, vs1, vs2)
    | Omniscient -> (
        try unifyIdem (g_, vs1, vs2)
        with Unify.Unify msg as e ->
          begin
            reportMismatch (g_, vs1, vs2, msg);
            raise e
          end)
    end

  let rec reportInfer' = function
    | g_, Omitexact (_, _, r), u_, v_ ->
        let xs_ =
          Abstract.collectEVars
            g_ (u_, IntSyn.id) (Abstract.collectEVars g_ (v_, IntSyn.id) [])
        in
        let xnames =
          List.map (function x_ -> (x_, Names.evarName IntSyn.Null x_)) xs_
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
              formatExp g_ u_;
              F.break_;
              F.string ":";
              F.space;
              formatExp g_ v_;
            ]
        in
        let _ =
          Display.debug ~level:Display.Level.verbose
            (Display.Form.string (F.makestring_fmt omit ^ "\n"))
        in
        ignore (reportConstraints xnames);
        ()
    | g_, Mismatch (tm1, tm2, _, _), u_, v_ -> reportInfer' (g_, tm2, u_, v_)
    | g_, Hastype _, u_, v_ -> ()
    | g_, tm, u_, v_ ->
        let xs_ =
          Abstract.collectEVars
            g_ (u_, IntSyn.id) (Abstract.collectEVars g_ (v_, IntSyn.id) [])
        in
        let xnames =
          List.map (function x_ -> (x_, Names.evarName IntSyn.Null x_)) xs_
        in
        let judg =
          F.hVbox
            [
              F.string "|-";
              F.space;
              formatExp g_ u_;
              F.break_;
              F.string ":";
              F.space;
              formatExp g_ v_;
            ]
        in
        let _ =
          Display.debug ~level:Display.Level.verbose
            (Display.Form.string (F.makestring_fmt judg ^ "\n"))
        in
        ignore (reportConstraints xnames);
        ()

  let reportInfer x = report (function () -> reportInfer' x)

  let rec inferExactN = function
    | g_, (Internal (u_, v_, r) as tm) -> (tm, Intro u_, v_)
    | g_, (Constant (h_, r) as tm) ->
        let cd = headConDec h_ in
        let e_, v_ =
          addImplicit
            ( g_,
              headElim h_,
              (IntSyn.conDecType cd, IntSyn.id),
              IntSyn.conDecImp cd )
        in
        (tm, Elim e_, v_)
    | g_, (Bvar (k, r) as tm) ->
        let (Dec (_, v_)) = IntSyn.ctxDec g_ k in
        (tm, Elim (bvarElim k), v_)
    | g_, (Evar (name, r) as tm) ->
        msg ~src:Group.approx ~level:Level.Debug
          (Fmt.shown_exact (fun name -> "inferring EVar " ^ name) name);
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
        (tm, Elim (elimSub (evarElim x_, s)), eClo (v_, s))
    | g_, (Fvar (name, r) as tm) ->
        Display.debug ~level:Display.Level.verbose
          Display.Form.(
            nl ()
            ++ string "Inferring exact type of FVar"
            ++ string name ++ nl ());
        let v_ =
          try getFVarType (name, false)
          with Apx.Ambiguous ->
            let v_ = getFVarType (name, true) in
            begin
              Display.debug ~level:Display.Level.verbose
                Display.Form.(
                  string "Type of FVar" ++ string name
                  ++ string
                       " is ambiguous, but continuing with one of the \
                        possibilities"
                  ++ nl ());
              delayAmbiguous (g_, v_, r, "Free variable has ambiguous type");
              v_
            end
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g_) in
        (tm, Elim (fvarElim (name, v_, s)), EClo (v_, s))
    | g_, (Typ r as tm) -> (tm, Intro (IntSyn.Uni Type), IntSyn.Uni Kind)
    | g_, Arrow (tm1, tm2) ->
        let tm1', b1_, _ (* Uni Type *) = inferExact (g_, tm1) in
        let d_ =
          IntSyn.Dec (None, toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)))
        in
        let tm2', b2_, l_ = inferExact (g_, tm2) in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        ( Arrow (tm1', tm2'),
          Intro (IntSyn.Pi ((d_, IntSyn.No), eClo (v2_, IntSyn.shift))),
          l_ )
    | g_, Pi (tm1, tm2) ->
        let tm1', d_ = inferExactDec (g_, tm1) in
        let tm2', b2_, l_ = inferExact (decl g_ d_, tm2) in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        (Pi (tm1', tm2'), Intro (IntSyn.Pi ((d_, IntSyn.Maybe), v2_)), l_)
    | g_, Lam (tm1, tm2) ->
        let tm1', d_ = inferExactDec (g_, tm1) in
        let tm2', b2_, v2_ = inferExact (decl g_ d_, tm2) in
        let u2_ = toIntro (b2_, (v2_, IntSyn.id)) in
        ( Lam (tm1', tm2'),
          Intro (IntSyn.Lam (d_, u2_)),
          IntSyn.Pi ((d_, IntSyn.Maybe), v2_) )
    | g_, App (tm1, tm2) ->
        let tm1', b1_, v1_ = inferExact (g_, tm1) in
        let e1_ = toElim b1_ in
        Display.(
          debug ~level:Level.verbose
            Form.(
              nl ()
              ++ string "Inferring exact application of"
              ++ shown show_term tm1 ++ string "to" ++ shown show_term tm2
              ++ nl ()));
        let t, s = Whnf.whnfExpandDef (v1_, IntSyn.id) in
        begin match t with
        | IntSyn.Pi ((IntSyn.Dec (_, va), _), vr) -> begin
            let tm2', b2_ =
              checkExact
                ( g_,
                  tm2,
                  (va, s),
                  "Argument type did not match function domain type\n\
                   (Index object(s) did not match)" )
            in
            let u2_ = toIntro (b2_, (va, s)) in
            ( App (tm1', tm2'),
              Elim (elimApp (e1_, u2_)),
              eClo (vr, Whnf.dotEta (exp u2_) s) )
          end
        | _ -> begin
            failwith
              "Expected a pi type after whnf in application, but got something \
               else"
          end
        end
    | g_, Hastype (tm1, tm2) ->
        let tm2', b2_, l_ = inferExact (g_, tm2) in
        let v_ = toIntro (b2_, (l_, IntSyn.id)) in
        let tm1', b1_ =
          checkExact
            ( g_,
              tm1,
              (v_, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        (Hastype (tm1', tm2'), b1_, v_)
    | g_, Mismatch (tm1, tm2, location_msg, problem_msg) ->
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
        (Mismatch (tm1', tm2', location_msg, problem_msg), b_, v_)
    | g_, Omitapx (u_, v_, l_, r) ->
        let v'_ =
          try Apx.apxToClass (g_, v_, l_, false)
          with Ambiguous ->
            let v'_ = Apx.apxToClass (g_, v_, l_, true) in
            begin
              Display.debug ~level:Display.Level.verbose
                Display.Form.(
                  string
                    "Classifier of omitted term is ambiguous, but continuing \
                     with one of the possibilities"
                  ++ nl ());
              delayAmbiguous
                ( g_,
                  v'_,
                  r,
                  "Omitted term has ambiguous "
                  ^ begin match Apx.whnfUni l_ with
                  | Apx.Level 1 -> "type"
                  | Apx.Level 2 -> "kind"
                  | Apx.Level 3 -> "hyperkind"
                  end );
              v'_
            end
        in
        let u'_ =
          try Apx.apxToExact (g_, u_, (v'_, IntSyn.id), false)
          with Ambiguous ->
            let u'_ = Apx.apxToExact (g_, u_, (v'_, IntSyn.id), true) in
            begin
              Display.debug ~level:Display.Level.verbose
                Display.Form.(
                  string
                    "Exact term of omitted term is ambiguous, but continuing \
                     with one of the possibilities"
                  ++ nl ());
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
        (Omitexact (u'_, v'_, r), Intro u'_, v'_)

  and inferExact (g_, tm) =
    begin if not !trace then inferExactN (g_, tm)
    else
      let tm', b'_, v'_ = inferExactN (g_, tm) in
      begin
        reportInfer (g_, tm', toIntro (b'_, (v'_, IntSyn.id)), v'_);
        (tm', b'_, v'_)
      end
    end

  and inferExactDec (g_, Dec (name, tm, r)) =
    let tm', b1_, _ (* Uni Type *) = inferExact (g_, tm) in
    let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
    let d_ = IntSyn.Dec (name, v1_) in
    (Dec (name, tm', r), d_)

  and checkExact1 = function
    | g_, Lam (Dec (name, tm1, r), tm2), vhs ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1_, _ (* Uni Type *)), ok1 =
          unifyExact (g_, tm1, (va, s))
        in
        let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
        let d_ = IntSyn.Dec (name, v1_) in
        let (tm2', b2_, v2_), ok2 =
          begin if ok1 then checkExact1 (decl g_ d_, tm2, (vr, IntSyn.dot1 s))
          else (inferExact (decl g_ d_, tm2), false)
          end
        in
        let u2_ = toIntro (b2_, (v2_, IntSyn.id)) in
        ( ( Lam (Dec (name, tm1', r), tm2'),
            Intro (IntSyn.Lam (d_, u2_)),
            IntSyn.Pi ((d_, IntSyn.Maybe), v2_) ),
          ok2 )
    | g_, Hastype (tm1, tm2), vhs ->
        let (tm2', b2_, l_), ok2 = unifyExact (g_, tm2, vhs) in
        let v_ = toIntro (b2_, (l_, IntSyn.id)) in
        let tm1', b1_ =
          checkExact
            ( g_,
              tm1,
              (v_, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        ((Hastype (tm1', tm2'), b1_, v_), ok2)
    | g_, Mismatch (tm1, tm2, location_msg, problem_msg), vhs ->
        let tm1', _, v1_ = inferExact (g_, tm1) in
        let (tm2', b_, v_), ok2 = checkExact1 (g_, tm2, vhs) in
        let _ =
          delayMismatch (g_, v1_, v_, termRegion tm2', location_msg, problem_msg)
        in
        ((Mismatch (tm1', tm2', location_msg, problem_msg), b_, v_), ok2)
    | g_, Omitapx (u_, v_, l_, r (* = Vhs *)), vhs ->
        let v'_ = eClo vhs in
        let u'_ =
          try Apx.apxToExact (g_, u_, vhs, false)
          with Ambiguous ->
            let u'_ = Apx.apxToExact (g_, u_, vhs, true) in
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
        ((Omitexact (u'_, v'_, r), Intro u'_, v'_), true)
    | g_, tm, vhs ->
        let tm', b'_, v'_ = inferExact (g_, tm) in
        ((tm', b'_, v'_), unifiableIdem (g_, vhs, (v'_, IntSyn.id)))

  and checkExact (g_, tm, vs_, location_msg) =
    Display.(
      debug ~level:Level.verbose
        Form.(
          nl () ++ string "Checking exact term" ++ shown show_term tm ++ nl ()));
    begin if not !trace then
      let (tm', b'_, v'_), ok = checkExact1 (g_, tm, vs_) in
      begin if ok then (tm', b'_)
      else
        try
          begin
            unifyIdem (g_, (v'_, IntSyn.id), vs_);
            raise Match
          end
        with Unify.Unify problem_msg ->
          let r = termRegion tm in
          let u'_ = toIntro (b'_, (v'_, IntSyn.id)) in
          let uapx, vapx, lapx = Apx.exactToApx u'_ v'_ in
          let (tm'', b'', _ (* Vs *)), _ (* true *) =
            checkExact1 (g_, Omitapx (uapx, vapx, lapx, r), vs_)
          in
          let _ =
            delayMismatch (g_, v'_, eClo vs_, r, location_msg, problem_msg)
          in
          (Mismatch (tm', tm'', location_msg, problem_msg), b'')
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
        let uapx, vapx, lapx = Apx.exactToApx u'_ v'_ in
        let tm'', b'' =
          checkExact (g_, Omitapx (uapx, vapx, lapx, r), vs_, location_msg)
        in
        let _ =
          delayMismatch (g_, v'_, eClo vs_, r, location_msg, problem_msg)
        in
        (Mismatch (tm', tm'', location_msg, problem_msg), b'')
    end

  and unifyExact = function
    | g_, Arrow (tm1, tm2), vhs ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1_, _ (* Uni Type *)), ok1 =
          unifyExact (g_, tm1, (va, s))
        in
        let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
        let d_ = IntSyn.Dec (None, v1_) in
        let tm2', b2_, l_ = inferExact (g_, tm2) in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        ( ( Arrow (tm1', tm2'),
            Intro (IntSyn.Pi ((d_, IntSyn.No), eClo (v2_, IntSyn.shift))),
            l_ ),
          ok1
          && unifiableIdem
               (decl g_ d_, (vr, IntSyn.dot1 s), (v2_, IntSyn.shift)) )
    | g_, Pi (Dec (name, tm1, r), tm2), vhs ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1_, _ (* Uni Type *)), ok1 =
          unifyExact (g_, tm1, (va, s))
        in
        let v1_ = toIntro (b1_, (IntSyn.Uni Type, IntSyn.id)) in
        let d_ = IntSyn.Dec (name, v1_) in
        let (tm2', b2_, l_), ok2 =
          begin if ok1 then unifyExact (decl g_ d_, tm2, (vr, IntSyn.dot1 s))
          else (inferExact (decl g_ d_, tm2), false)
          end
        in
        let v2_ = toIntro (b2_, (l_, IntSyn.id)) in
        ( ( Pi (Dec (name, tm1', r), tm2'),
            Intro (IntSyn.Pi ((d_, IntSyn.Maybe), v2_)),
            l_ ),
          ok2 )
    | g_, Hastype (tm1, tm2), vhs ->
        let tm2', _, _ = inferExact (g_, tm2) in
        let (tm1', b_, l_), ok1 = unifyExact (g_, tm1, vhs) in
        ((Hastype (tm1', tm2'), b_, l_), ok1)
    | g_, Mismatch (tm1, tm2, location_msg, problem_msg), vhs ->
        let tm1', _, l1_ = inferExact (g_, tm1) in
        let (tm2', b_, l_), ok2 = unifyExact (g_, tm2, vhs) in
        let _ =
          delayMismatch (g_, l1_, l_, termRegion tm2', location_msg, problem_msg)
        in
        ((Mismatch (tm1', tm2', location_msg, problem_msg), b_, l_), ok2)
    | g_, Omitapx (v_, l_, nL, r), vhs ->
        let l'_ = Apx.apxToClass (g_, l_, nL, false) in
        let v'_ = eClo vhs in
        ((Omitexact (v'_, l'_, r), Intro v'_, l'_), true)
    | g_, tm, vhs ->
        let tm', b'_, l'_ = inferExact (g_, tm) in
        let v'_ = toIntro (b'_, (l'_, IntSyn.id)) in
        ((tm', b'_, l'_), unifiableIdem (g_, vhs, (v'_, IntSyn.id)))

  let rec occElim = function
    | Constant (h_, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        ( Paths.root (r', Paths.leaf r, IntSyn.conDecImp (headConDec h_), i, os),
          r' )
    | Bvar (k, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | Fvar (name, r), os, rs, i ->
        let r' = List.foldr Paths.join r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | App (tm1, tm2), os, rs, i ->
        let oc2, r2 = occIntro tm2 in
        occElim (tm1, Paths.app oc2 os, r2 :: rs, i + 1)
    | Hastype (tm1, tm2), os, rs, i -> occElim (tm1, os, rs, i)
    | tm, os, rs, i ->
        let r' = List.foldr Paths.join (termRegion tm) rs in
        (Paths.leaf r', r')

  and occIntro = function
    | Arrow (tm1, tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join r1 r2 in
        (Paths.bind r' (Some oc1) oc2, r')
    | Pi (Dec (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join r r2 in
        (Paths.bind r' (Some oc1) oc2, r')
    | Lam (Dec (name, tm1, r), tm2) ->
        let oc1, r1 = occIntro tm1 in
        let oc2, r2 = occIntro tm2 in
        let r' = Paths.join r r2 in
        (Paths.bind r' (Some oc1) oc2, r')
    | Hastype (tm1, tm2) -> occIntro tm1
    | tm ->
        let oc, r = occElim (tm, Paths.nils, [], 0) in
        (oc, r)

  let rec inferExactJob = function
    | g_, Jnothing -> JNothing
    | g_, Jand (j1, j2) -> JAnd (inferExactJob (g_, j1), inferExactJob (g_, j2))
    | g_, Jwithctx (g, j) ->
        let rec ie = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g'_, gresult = ie g in
              let _, d_ = inferExactDec (g'_, tm) in
              (decl g'_ d_, decl gresult d_)
        in
        let g'_, gresult = ie g in
        JWithCtx (gresult, inferExactJob (g'_, j))
    | g_, Jterm tm ->
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
    | g_, Jclass tm ->
        let tm', b_, l_ = inferExact (g_, tm) in
        let v_ = toIntro (b_, (l_, IntSyn.id)) in
        let oc, r = occIntro tm' in
        let IntSyn.Uni l_, _ = Whnf.whnf (l_, IntSyn.id) in
        JClass ((v_, oc), l_)
    | g_, Jof (tm1, tm2) ->
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

  let internalInst x = raise Match
  let externalInst x = raise Match

  (* Re-expose public-facing termRegion/decRegion for the RECON_TERM interface *)
  let termRegion (t : Cst.term) : Paths.region =
    termRegion_ (cst_term_to_term t)

  let decRegion (d : Cst.decl) : Paths.region = decRegion_ (cst_decl_to_dec d)
end
