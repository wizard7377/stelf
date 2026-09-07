open! Basis
open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Table.Table_
open! Msg.Msg_
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

  let formatExp g u =
    try Print.formatExp g u
    with Names.Unprintable -> F.string "%_unprintable_%"

  (* this is a hack, i know *)
  let queryMode = ref false
  let decl a1 b1 = match a1, b1 with g, d -> IntSyn.Decl (g, d)
  let eClo (v, s) = IntSyn.EClo (v, s)
  let root (h, s) = IntSyn.Root (h, s)
  let bVar n = IntSyn.BVar n
  let redex (u, s) = IntSyn.Redex (u, s)
  let fVar (name, v, s) = IntSyn.FVar (name, v, s)
  let exp u = IntSyn.Exp u
  let undefined = Apx.Undefined
  let uni l = Apx.Uni (Apx.uniToApx l)
  let kind = Apx.kind
  let hyperkind = Apx.hyperkind
  let next l = Apx.Next l

  let headConDec (h : IntSyn.head) =
    begin match h with
    | IntSyn.Const c -> IntSyn.sgnLookup c
    | IntSyn.Skonst c -> IntSyn.sgnLookup c
    | IntSyn.Def d -> IntSyn.sgnLookup d
    | IntSyn.NSDef d -> IntSyn.sgnLookup d
    | IntSyn.FgnConst (_, cd) -> cd
    end

  let rec lowerTypeW (g, vs) = match vs with
    | (IntSyn.Pi ((d, _), v), s) ->
        let d' = IntSyn.decSub d s in
        lowerType (decl g d', (v, IntSyn.dot1 s))
    | vs -> (g, eClo vs)

  and lowerType (g, vs) = lowerTypeW (g, Whnf.whnfExpandDef vs)

  let rec raiseType a1 b1 = match a1, b1 with
    | IntSyn.Null, v -> v
    | IntSyn.Decl (g, d), v ->
        raiseType g (IntSyn.Pi ((d, IntSyn.Maybe), v))

  let evarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarApxTable : Apx.exp StringTree.table = StringTree.new_ 0
  let fvarTable : IntSyn.exp StringTree.table = StringTree.new_ 0

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
        msg ~src:Group.approx ~level:Level.Debug
          (Fmt.shown_exact
             (fun name -> "getFVarTypeApx: found existing for " ^ name)
             name);
        v
    | None ->
        let v = Apx.newCVar () in
        msg ~src:Group.approx ~level:Level.Debug
          (Fmt.shown_exact
             (fun name -> "getFVarTypeApx: creating fresh CVar for " ^ name)
             name);
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
    | Internal (u, v, r) -> r
    | Constant (h, r) -> r
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
    | Omitapx (u, v, l, r) -> r
    | Omitexact (u, v, r) -> r

  and decRegion_ (Dec (name, tm, r)) = r

  let rec ctxRegion_internal = function
    | IntSyn.Null -> None
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, decRegion_ tm)

  and ctxRegion' (a, r) = match a with
    | IntSyn.Null -> Some r
    | IntSyn.Decl (g, tm) -> ctxRegion' (g, Paths.join r (decRegion_ tm))

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
      Omitted r
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
        | Some k -> Bvar (k, r)
        end
    end

  let findConst ?(shortest = false) fc (g, qid, r) =
    begin match Names.resolveQid ~shortest qid with
    | None -> fc (g, qid, r)
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

  let findCSConst fc (g, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g, qid, r)
    | Some name ->
        begin match CsManager.parse name with
        | None -> fc (g, qid, r)
        | Some (cs, conDec) -> Constant (IntSyn.FgnConst (cs, conDec), r)
        end
    end

  let findEFVar fc (g, qid, r) =
    begin match Names.unqualified qid with
    | None -> fc (g, qid, r)
    | Some name ->
        begin if !queryMode || String.isPrefix "__" name then Evar (name, r)
        else Fvar (name, r)
        end
    end

  let findLCID x = findBVar (findConst (findCSConst findOmitted)) x
  let findUCID x = findBVar (findConst (findCSConst (findEFVar findOmitted))) x

  let findQUID form x =
    findConst ~shortest:(form = Cst.Abs) (findCSConst findOmitted) x

  let rec inferApx (g, b) = match b with
    | (Internal (u, v, r) as tm) ->
        let u', v', l' = Apx.exactToApx u v in
        (tm, u', v', l')
    | (Lcid (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g, findLCID (g, qid, r))
    | (Ucid (ids, name, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g, findUCID (g, qid, r))
    | (Quid (ids, name, form, r) as tm) ->
        let qid = Names.Qid (ids, name) in
        inferApx (g, findQUID form (g, qid, r))
    | (Scon (name, r) as tm) ->
        begin match CsManager.parse name with
        | None -> begin
            error r ("Strings unsupported in current signature");
            inferApx (g, Omitted r)
          end
        | Some (cs, conDec) ->
            inferApx (g, Constant (IntSyn.FgnConst (cs, conDec), r))
        end
    | (Constant (h, r) as tm) ->
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
    | (Bvar (k, r) as tm) ->
        let (Dec (_, v)) = IntSyn.ctxLookup g k in
        (tm, undefined, v, Apx.(Level 1))
    | (Evar (name, r) as tm) ->
        (tm, undefined, getEVarTypeApx name, Apx.(Level 1))
    | (Fvar (name, r) as tm) ->
        (tm, undefined, getFVarTypeApx name, Apx.(Level 1))
    | (Typ r as tm) -> (tm, uni Type, Apx.Uni kind, hyperkind)
    | Arrow (tm1, tm2) ->
        let l = Apx.newLVar () in
        let tm1', v1 =
          checkApx
            (g, tm1, uni Type, kind, "Left-hand side of arrow must be a type")
        in
        let tm2', v2 =
          checkApx
            ( g,
              tm2,
              Apx.Uni l,
              next l,
              "Right-hand side of arrow must be a type or a kind" )
        in
        (Arrow (tm1', tm2'), Arrow (v1, v2), Apx.Uni l, next l)
    | Pi (tm1, tm2) ->
        let tm1', (Dec (_, v1) as d) = inferApxDec (g, tm1) in
        let l = Apx.newLVar () in
        let tm2', v2 =
          checkApx
            ( decl g d,
              tm2,
              Apx.Uni l,
              next l,
              "Body of pi must be a type or a kind" )
        in
        (Pi (tm1', tm2'), Arrow (v1, v2), Apx.Uni l, next l)
    | (Lam (tm1, tm2) as tm) ->
        let tm1', (Dec (_, v1) as d) = inferApxDec (g, tm1) in
        let tm2', u2, v2, l2 = inferApx (decl g d, tm2) in
        (Lam (tm1', tm2'), u2, Arrow (v1, v2), l2)
    | (App (tm1, tm2) as tm) ->
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
        (App (tm1', tm2'), u1, vr, l)
    | (Hastype (tm1, tm2) as tm) ->
        let l = Apx.newLVar () in
        let tm2', v2 =
          checkApx
            ( g,
              tm2,
              Apx.Uni l,
              next l,
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
        (Hastype (tm1', tm2'), u1, v2, l)
    | Omitted r ->
        let l = Apx.newLVar () in
        let v = Apx.newCVar () in
        let u = Apx.newCVar () in
        (Omitapx (u, v, l, r), u, v, l)

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
        let tm'', u'' = checkApx (g, Omitted r, v, l, location_msg) in
        ignore (addDelayed (fun () -> ignore (Apx.makeGroundUni l')));
        (Mismatch (tm', tm'', location_msg, problem_msg), u'')
      end

  and inferApxDec (g, Dec (name, tm, r)) =
    let tm', v1 =
      checkApx
        (g, tm, uni Type, kind, "Classifier in declaration must be a type")
    in
    let d = Dec (name, v1) in
    (Dec (name, tm', r), d)

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
              (decl g'_ d, decl g' tm')
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
              next l,
              "The term in this position must be a type or a kind" )
        in
        ignore (filterLevel
            ( tm',
              next l,
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
              next l,
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

  let elimSub (e, s) (s', s_) = e (IntSyn.comp s s', s_)

  let elimApp (e, u) (s, s_) = e (s, IntSyn.App (eClo (u, s), s_))

  let bvarElim n (s, s_) =
        begin match IntSyn.bvarSub n s with
        | Idx n' -> root (bVar n', s_)
        | Exp u -> redex (u, s_)
        end

  let fvarElim (name, v, s) (s', s_) = root (fVar (name, v, IntSyn.comp s s'), s_)

  let redexElim u (s, s_) = redex (eClo (u, s), s_)

  let headElim = function
    | IntSyn.BVar n -> bvarElim n
    | IntSyn.FVar (name, v, s) -> fvarElim (name, v, s)
    | IntSyn.NSDef d -> redexElim (IntSyn.constDef d)
    | h ->
        begin match IntSyn.conDecStatus (headConDec h) with
        | Foreign (_, f) -> fun (_, s) -> f s
        | _ -> fun (_, s) -> Root (h, s)
        end

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

  let toElim = function Elim e -> e | Intro u -> redexElim u

  let toIntro (a, vs) = match a with
    | Elim e -> etaExpand (e, vs)
    | Intro u -> u

  let rec addImplicit1W
      (g, e, (IntSyn.Pi ((IntSyn.Dec (_, va), _), vr), s), i (* >= 1 *)) =
    let x = Whnf.newLoweredEVar g (va, s) in
    addImplicit (g, elimApp (e, x), (vr, Whnf.dotEta (exp x) s), i - 1)

  and addImplicit (g, e, vs, i) = match i with
    | 0 -> (e, eClo vs)
    | i -> addImplicit1W (g, e, Whnf.whnfExpandDef vs, i)

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
        let fstr = F.makestring_fmt amb in
        Display.debug ~level:Display.Level.verbose
          Display.Form.(
            nl ()
            ++ string "Ambiguous reconstruction of term: "
            ++ string fstr ++ nl ());
        error r ((("Ambiguous reconstruction\n" ^ fstr) ^ "\n") ^ msg))

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

  let unifiableIdem (g, us, vs) =
    ignore (Unify.reset ());
    let ok = Unify.unifiable g us vs in
    ignore begin if ok then Unify.reset () else Unify.unwind ()
      end;
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
        ignore (Display.debug ~level:Display.Level.debug
            (Display.Form.string (F.makestring_fmt eqnsFmt ^ "\n")));
        ignore (reportConstraints xnames);
        ignore (Display.debug ~level:Display.Level.debug
            (Display.Form.string
               ((("Failed: " ^ problem_msg) ^ "\n")
               ^ "Continuing with subterm replaced by _\n")));
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
    ignore (Display.debug ~level:Display.Level.debug
        (Display.Form.string (F.makestring_fmt eqnsFmt ^ "\n")));
    ignore (try unifyIdem (g, vs1, vs2)
      with Unify.Unify msg as e ->
        begin
          Display.debug ~level:Display.Level.debug
            (Display.Form.string
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
        ignore (Display.debug ~level:Display.Level.verbose
            (Display.Form.string (F.makestring_fmt omit ^ "\n")));
        ignore (reportConstraints xnames);
        ()
    | Mismatch (tm1, tm2, _, _) -> reportInfer' (g, tm2, u, v)
    | Hastype _ -> ()
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
        ignore (Display.debug ~level:Display.Level.verbose
            (Display.Form.string (F.makestring_fmt judg ^ "\n")));
        ignore (reportConstraints xnames);
        ()

  let reportInfer x = report (function () -> reportInfer' x)

  let rec inferExactN (g, b) = match b with
    | (Internal (u, v, r) as tm) -> (tm, Intro u, v)
    | (Constant (h, r) as tm) ->
        let cd = headConDec h in
        let e, v =
          addImplicit
            ( g,
              headElim h,
              (IntSyn.conDecType cd, IntSyn.id),
              IntSyn.conDecImp cd )
        in
        (tm, Elim e, v)
    | (Bvar (k, r) as tm) ->
        let (Dec (_, v)) = IntSyn.ctxDec g k in
        (tm, Elim (bvarElim k), v)
    | (Evar (name, r) as tm) ->
        msg ~src:Group.approx ~level:Level.Debug
          (Fmt.shown_exact (fun name -> "inferring EVar " ^ name) name);
        let x, v =
          try getEVar (name, false)
          with Apx.Ambiguous ->
            let x, v = getEVar (name, true) in
            delayAmbiguous (g, v, r, "Free variable has ambiguous type");
            (x, v)
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g) in
        (tm, Elim (elimSub (evarElim x, s)), eClo (v, s))
    | (Fvar (name, r) as tm) ->
        Display.debug ~level:Display.Level.verbose
          Display.Form.(
            nl ()
            ++ string "Inferring exact type of FVar"
            ++ string name ++ nl ());
        let v =
          try getFVarType (name, false)
          with Apx.Ambiguous ->
            let v = getFVarType (name, true) in
            Display.debug ~level:Display.Level.verbose
              Display.Form.(
                string "Type of FVar" ++ string name
                ++ string
                     " is ambiguous, but continuing with one of the \
                      possibilities"
                ++ nl ());
            delayAmbiguous (g, v, r, "Free variable has ambiguous type");
            v
        in
        let s = IntSyn.Shift (IntSyn.ctxLength g) in
        (tm, Elim (fvarElim (name, v, s)), EClo (v, s))
    | (Typ r as tm) -> (tm, Intro (IntSyn.Uni Type), IntSyn.Uni Kind)
    | Arrow (tm1, tm2) ->
        let tm1', b1, _ (* Uni Type *) = inferExact (g, tm1) in
        let d =
          IntSyn.Dec (None, toIntro (b1, (IntSyn.Uni Type, IntSyn.id)))
        in
        let tm2', b2, l = inferExact (g, tm2) in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        ( Arrow (tm1', tm2'),
          Intro (IntSyn.Pi ((d, IntSyn.No), eClo (v2, IntSyn.shift))),
          l )
    | Pi (tm1, tm2) ->
        let tm1', d = inferExactDec (g, tm1) in
        let tm2', b2, l = inferExact (decl g d, tm2) in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        (Pi (tm1', tm2'), Intro (IntSyn.Pi ((d, IntSyn.Maybe), v2)), l)
    | Lam (tm1, tm2) ->
        let tm1', d = inferExactDec (g, tm1) in
        let tm2', b2, v2 = inferExact (decl g d, tm2) in
        let u2 = toIntro (b2, (v2, IntSyn.id)) in
        ( Lam (tm1', tm2'),
          Intro (IntSyn.Lam (d, u2)),
          IntSyn.Pi ((d, IntSyn.Maybe), v2) )
    | App (tm1, tm2) ->
        let tm1', b1, v1 = inferExact (g, tm1) in
        let e1 = toElim b1 in
        Display.(
          debug ~level:Level.verbose
            Form.(
              nl ()
              ++ string "Inferring exact application of"
              ++ shown show_term tm1 ++ string "to" ++ shown show_term tm2
              ++ nl ()));
        let t, s = Whnf.whnfExpandDef (v1, IntSyn.id) in
        begin match t with
        | IntSyn.Pi ((IntSyn.Dec (_, va), _), vr) -> begin
            let tm2', b2 =
              checkExact
                ( g,
                  tm2,
                  (va, s),
                  "Argument type did not match function domain type\n\
                   (Index object(s) did not match)" )
            in
            let u2 = toIntro (b2, (va, s)) in
            ( App (tm1', tm2'),
              Elim (elimApp (e1, u2)),
              eClo (vr, Whnf.dotEta (exp u2) s) )
          end
        | _ -> begin
            failwith
              "Expected a pi type after whnf in application, but got something \
               else"
          end
        end
    | Hastype (tm1, tm2) ->
        let tm2', b2, l = inferExact (g, tm2) in
        let v = toIntro (b2, (l, IntSyn.id)) in
        let tm1', b1 =
          checkExact
            ( g,
              tm1,
              (v, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        (Hastype (tm1', tm2'), b1, v)
    | Mismatch (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, v1 = inferExact (g, tm1) in
        let tm2', b, v = inferExactN (g, tm2) in
        ignore begin if !trace then
            reportMismatch (g, (v1, IntSyn.id), (v, IntSyn.id), problem_msg)
          else ()
          end;
        ignore (delayMismatch (g, v1, v, termRegion tm2', location_msg, problem_msg));
        (Mismatch (tm1', tm2', location_msg, problem_msg), b, v)
    | Omitapx (u, v, l, r) ->
        let v' =
          try Apx.apxToClass (g, v, l, false)
          with Ambiguous ->
            let v' = Apx.apxToClass (g, v, l, true) in
            Display.debug ~level:Display.Level.verbose
              Display.Form.(
                string
                  "Classifier of omitted term is ambiguous, but continuing \
                   with one of the possibilities"
                ++ nl ());
            delayAmbiguous
              ( g,
                v',
                r,
                "Omitted term has ambiguous "
                ^ begin match Apx.whnfUni l with
                | Apx.Level 1 -> "type"
                | Apx.Level 2 -> "kind"
                | Apx.Level 3 -> "hyperkind"
                end );
            v'
        in
        let u' =
          try Apx.apxToExact (g, u, (v', IntSyn.id), false)
          with Ambiguous ->
            let u' = Apx.apxToExact (g, u, (v', IntSyn.id), true) in
            Display.debug ~level:Display.Level.verbose
              Display.Form.(
                string
                  "Exact term of omitted term is ambiguous, but continuing \
                   with one of the possibilities"
                ++ nl ());
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

  and inferExactDec (g, Dec (name, tm, r)) =
    let tm', b1, _ (* Uni Type *) = inferExact (g, tm) in
    let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
    let d = IntSyn.Dec (name, v1) in
    (Dec (name, tm', r), d)

  and checkExact1 (g, tm, vhs) = match tm with
    | Lam (Dec (name, tm1, r), tm2) ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1, _ (* Uni Type *)), ok1 =
          unifyExact (g, tm1, (va, s))
        in
        let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
        let d = IntSyn.Dec (name, v1) in
        let (tm2', b2, v2), ok2 =
          begin if ok1 then checkExact1 (decl g d, tm2, (vr, IntSyn.dot1 s))
          else (inferExact (decl g d, tm2), false)
          end
        in
        let u2 = toIntro (b2, (v2, IntSyn.id)) in
        ( ( Lam (Dec (name, tm1', r), tm2'),
            Intro (IntSyn.Lam (d, u2)),
            IntSyn.Pi ((d, IntSyn.Maybe), v2) ),
          ok2 )
    | Hastype (tm1, tm2) ->
        let (tm2', b2, l), ok2 = unifyExact (g, tm2, vhs) in
        let v = toIntro (b2, (l, IntSyn.id)) in
        let tm1', b1 =
          checkExact
            ( g,
              tm1,
              (v, IntSyn.id),
              "Ascription did not hold\n(Index object(s) did not match)" )
        in
        ((Hastype (tm1', tm2'), b1, v), ok2)
    | Mismatch (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, v1 = inferExact (g, tm1) in
        let (tm2', b, v), ok2 = checkExact1 (g, tm2, vhs) in
        ignore (delayMismatch (g, v1, v, termRegion tm2', location_msg, problem_msg));
        ((Mismatch (tm1', tm2', location_msg, problem_msg), b, v), ok2)
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
    Display.(
      debug ~level:Level.verbose
        Form.(
          nl () ++ string "Checking exact term" ++ shown show_term tm ++ nl ()));
    begin if not !trace then
      let (tm', b', v'), ok = checkExact1 (g, tm, vs) in
      begin if ok then (tm', b')
      else
        try
          begin
            unifyIdem (g, (v', IntSyn.id), vs);
            raise Match
          end
        with Unify.Unify problem_msg ->
          let r = termRegion tm in
          let u' = toIntro (b', (v', IntSyn.id)) in
          let uapx, vapx, lapx = Apx.exactToApx u' v' in
          let (tm'', b'', _ (* Vs *)), _ (* true *) =
            checkExact1 (g, Omitapx (uapx, vapx, lapx, r), vs)
          in
          ignore (delayMismatch (g, v', eClo vs, r, location_msg, problem_msg));
          (Mismatch (tm', tm'', location_msg, problem_msg), b'')
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
        (Mismatch (tm', tm'', location_msg, problem_msg), b'')
    end

  and unifyExact (g, tm, vhs) = match tm with
    | Arrow (tm1, tm2) ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1, _ (* Uni Type *)), ok1 =
          unifyExact (g, tm1, (va, s))
        in
        let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
        let d = IntSyn.Dec (None, v1) in
        let tm2', b2, l = inferExact (g, tm2) in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        ( ( Arrow (tm1', tm2'),
            Intro (IntSyn.Pi ((d, IntSyn.No), eClo (v2, IntSyn.shift))),
            l ),
          ok1
          && unifiableIdem
               (decl g d, (vr, IntSyn.dot1 s), (v2, IntSyn.shift)) )
    | Pi (Dec (name, tm1, r), tm2) ->
        let Pi ((Dec (_, va), _), vr), s = Whnf.whnfExpandDef vhs in
        let (tm1', b1, _ (* Uni Type *)), ok1 =
          unifyExact (g, tm1, (va, s))
        in
        let v1 = toIntro (b1, (IntSyn.Uni Type, IntSyn.id)) in
        let d = IntSyn.Dec (name, v1) in
        let (tm2', b2, l), ok2 =
          begin if ok1 then unifyExact (decl g d, tm2, (vr, IntSyn.dot1 s))
          else (inferExact (decl g d, tm2), false)
          end
        in
        let v2 = toIntro (b2, (l, IntSyn.id)) in
        ( ( Pi (Dec (name, tm1', r), tm2'),
            Intro (IntSyn.Pi ((d, IntSyn.Maybe), v2)),
            l ),
          ok2 )
    | Hastype (tm1, tm2) ->
        let tm2', _, _ = inferExact (g, tm2) in
        let (tm1', b, l), ok1 = unifyExact (g, tm1, vhs) in
        ((Hastype (tm1', tm2'), b, l), ok1)
    | Mismatch (tm1, tm2, location_msg, problem_msg) ->
        let tm1', _, l1 = inferExact (g, tm1) in
        let (tm2', b, l), ok2 = unifyExact (g, tm2, vhs) in
        ignore (delayMismatch (g, l1, l, termRegion tm2', location_msg, problem_msg));
        ((Mismatch (tm1', tm2', location_msg, problem_msg), b, l), ok2)
    | Omitapx (v, l, nL, r) ->
        let l' = Apx.apxToClass (g, l, nL, false) in
        let v' = eClo vhs in
        ((Omitexact (v', l', r), Intro v', l'), true)
    | tm ->
        let tm', b', l' = inferExact (g, tm) in
        let v' = toIntro (b', (l', IntSyn.id)) in
        ((tm', b', l'), unifiableIdem (g, vhs, (v', IntSyn.id)))

  let rec occElim (tm, os, rs, i) = match tm with
    | Constant (h, r) ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) r rs in
        ( Paths.root (r', Paths.leaf r, IntSyn.conDecImp (headConDec h), i, os),
          r' )
    | Bvar (k, r) ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | Fvar (name, r) ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) r rs in
        (Paths.root (r', Paths.leaf r, 0, i, os), r')
    | App (tm1, tm2) ->
        let oc2, r2 = occIntro tm2 in
        occElim (tm1, Paths.app oc2 os, r2 :: rs, i + 1)
    | Hastype (tm1, tm2) -> occElim (tm1, os, rs, i)
    | tm ->
        let r' = List.foldr (fun (a, b) -> Paths.join a b) (termRegion tm) rs in
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

  let rec inferExactJob (g_, a) = match a with
    | Jnothing -> JNothing
    | Jand (j1, j2) -> JAnd (inferExactJob (g_, j1), inferExactJob (g_, j2))
    | Jwithctx (g, j) ->
        let rec ie = function
          | IntSyn.Null -> (g_, IntSyn.Null)
          | Decl (g, tm) ->
              let g', gresult = ie g in
              let _, d = inferExactDec (g', tm) in
              (decl g' d, decl gresult d)
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
