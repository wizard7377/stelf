open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index.Index_

(* # 1 "src/modes/Modecheck.sig.ml" *)
open Modesyn

(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
include MODECHECK

(* raises Error(msg) *)
(* signature MODECHECK *)

(* # 1 "src/modes/Modecheck.fun.ml" *)
open! Basis
open Modesyn
open Modetable
open Origins

(** Mode Checking *)
(** @author Carsten Schuermann *)
(** Modified: Frank Pfenning, Roberto Virga *)
exception Error of string
let () = Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeModeCheck
    (ModeTable : MODETABLE)
    (Whnf : WHNF)
    (Index : INDEX)
    (Origins : ORIGINS) : MODECHECK = struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure ModeSyn = ModeSyn !*)
  (*! structure Paths = Paths !*)

  exception Error = Error

  open! struct
    let print' s = Display.(debug Form.(string s))
    
    module I = IntSyn
    module M = ModeSyn
    module P = Paths

    (** Uniqueness information *)
    type uniqueness = Unique | Ambig [@@deriving eq, ord, show]

    (** Groundedness information *)
    type info = Free | Unknown | Ground of uniqueness
    [@@deriving eq, ord, show]

    (** Variable status *)
    type status = Existential of info * string option | Universal
    [@@deriving eq, ord, show]

    (** hack: if true, check freeness of output arguments in subgoals *)
    let checkFree = ref false

    (** copied from worldcheck/worldsyn.fun *)
    let wrapMsg (c, occ, msg) =
      begin match Origins.originLookup c with
      | fileName, None -> (fileName ^ ":") ^ msg
      | fileName, Some occDec ->
          P.wrapLoc'
            (P.Loc (fileName, P.occToRegionClause occDec occ)) (Origins.linesInfoLookup fileName) ((("Constant " ^ Names.qidToString (Names.constQid c)) ^ "\n")
              ^ msg)
      end

    let wrapMsg' (fileName, r, msg) = P.wrapLoc (P.Loc (fileName, r)) msg

    exception ModeError of P.occ * string
    exception Error' of P.occ * string

    let modeError' (occ, msg) = Display.debug (Display.Form.string msg) ; raise (ModeError (occ, msg))
    let error'' (occ, msg) = Display.debug (Display.Form.string msg) ; raise (Error' (occ, msg))
    (** [lookup (a, occ) = mSs]

       Invariant: mS are the argument modes for a
       Raises an error if no mode for a has declared.
       (occ is used in error message)
    *)
    let lookup (a, occ) =
      begin match ModeTable.mmodeLookup a with
      | [] ->
          raise
            (Error'
               (occ, "No mode declaration for " ^ I.conDecName (I.sgnLookup a)))
      | sMs -> sMs
      end

    let nameOf = function
      | Existential (_, None) -> "?"
      | Existential (_, Some name) -> name
      | _ -> "?"

    (** unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *)
    let rec unique (k, a) = match a with
      | [] -> true
      | k' :: ks -> k <> k' && unique (k, ks)

    (** isUniversal S = B

       Invariant:
       B iff S = Par
    *)
    let isUniversal = function Universal -> true | _ -> false
    (** isGround S = B

       Invariant:
       B iff S = Ex (T x)
    *)
    let isGround = function Existential (Ground _, _) -> true | _ -> false

    (** uniqueness S = u
       where u is the uniqueness property of status S
    *)
    let uniqueness = function
      | Existential (Ground u, _) -> u
      | Universal -> Unique

    (** ambiguate (mode) = mode'
       where mode' forgets uniqueness properties
    *)
    let ambiguate = function
      | M.Plus -> M.Plus
      | M.Minus -> M.Minus
      | M.Minus1 -> M.Minus

    (** andUnique (u1, u2) = Unique if u1 = u2 = Unique
       = Ambig otherwise
    *)
    let andUnique = function Unique, Unique -> Unique | _ -> Ambig
    (** isFree S = b

       Invariant:
       b iff S = Ex (B x)
    *)
    let isFree = function Existential (Free, _) -> true | _ -> false

    exception Eta

    (** etaContract (U, n) = k

       if lam V1... lam Vn. U =eta*=> k
       otherwise raise exception Eta

       Invariant: G, V1,..., Vn |- U : V for some G, Vi, V.
                  U in NF
    *)
    let rec etaContract = function
      | I.Root (I.BVar k, s), n ->
          begin if k > n then begin
            etaSpine (s, n);
            k - n
          end
          else raise Eta
          end
      | I.Lam (d, u), n -> etaContract (u, n + 1)
      | _ -> raise Eta

    and etaSpine = function
      | I.Nil, 0 -> ()
      | I.App (u, s), n ->
          begin if etaContract (u, 0) = n then etaSpine (s, n - 1)
          else raise Eta
          end

    (** isPattern (D, k, mS) = B

       Invariant:
       B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
    *)
    let rec checkPattern (d, k, args, a) = match a with
      | I.Nil -> ()
      | I.App (u, s) ->
          let k' = etaContract (u, 0) in
          begin if
            k > k' && isUniversal (I.ctxLookup d k') && unique (k', args)
          then checkPattern (d, k, k' :: args, s)
          else raise Eta
          end

    let isPattern (d, k, s) =
      try
        begin
          checkPattern (d, k, [], s);
          true
        end
      with Eta -> false

    (* ------------------------------------------- strictness check *)
    (* This repeats some code from ../typecheck/strict.fun *)
    (* Interface here is somewhat different *)
    let rec strictExpN (d_, p, a) = match a with
      | I.Uni _ -> false
      | I.Lam (_, u) -> strictExpN (I.Decl (d_, Universal), p + 1, u)
      | I.Pi ((d', _), u) ->
          strictDecN (d_, p, d')
          || strictExpN (I.Decl (d_, Universal), p + 1, u)
      | I.Root (h, s) ->
          begin match h with
          | I.BVar k' ->
              begin if k' = p then isPattern (d_, k', s)
              else
                begin if isUniversal (I.ctxLookup d_ k') then
                  strictSpineN (d_, p, s)
                else false
                end
              end
          | I.Const c -> strictSpineN (d_, p, s)
          | I.Def d -> strictSpineN (d_, p, s)
          | I.FgnConst (cs, conDec) -> strictSpineN (d_, p, s)
          end
      | I.FgnExp (cs, ops) -> false
      (* this is a hack - until we investigate this further   -rv *)

    and strictSpineN (d, p, a) = match a with
      | I.Nil -> false
      | I.App (u, s) ->
          strictExpN (d, p, u) || strictSpineN (d, p, s)

    and strictDecN (d, p, I.Dec (_, v)) = strictExpN (d, p, v)

    (* ------------------------------------------- freeness check *)
    (** freeExpN (D, mode, U, occ = ()

       If G |- U : V  (U in nf)
       and G ~ D
       then freeExpN terminates with () if D |- U free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    let rec freeExpN (d_, d, mode, a, occ, strictFun) = match a with
      | I.Root (I.BVar k, s) -> begin
          freeVar (d_, d, mode, k, P.head occ, strictFun);
          freeSpineN (d_, d, mode, s, (1, occ), strictFun)
        end
      | I.Root (I.Const _, s) ->
          freeSpineN (d_, d, mode, s, (1, occ), strictFun)
      | I.Root (I.Def _, s) ->
          freeSpineN (d_, d, mode, s, (1, occ), strictFun)
      | I.Root (I.FgnConst (cs, conDec), s) ->
          freeSpineN (d_, d, mode, s, (1, occ), strictFun)
      | I.Lam (_, u) ->
          freeExpN
            (I.Decl (d_, Universal), d + 1, mode, u, P.body occ, strictFun)
      | I.FgnExp (csfe1, csfe2) ->
          I.FgnExpStd.App.apply csfe1 csfe2 (function u ->
              freeExpN (d_, d, mode, Whnf.normalize (u, I.id), occ, strictFun))

    (** freeSpineN (D, mode, S, occ, strictFun)  = ()

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then freeSpineN terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    and freeSpineN (d_, d, mode, a, b, strictFun) = match a, b with
      | I.Nil, _ -> ()
      | I.App (u, s), (p, occ) -> begin
          freeExpN (d_, d, mode, u, P.arg p occ, strictFun);
          freeSpineN (d_, d, mode, s, (p + 1, occ), strictFun)
        end

    (** freeVar (D, mode, k, occ, strictFun)  = ()

       If   G |- k : V1
       and  G ~ D
       then freeVar terminates with () if  D |- S free
       else exception ModeError is raised

       (occ and mode are used in error messages)
    *)
    and freeVar (d_, d, mode, k, occ, strictFun) =
      let status = I.ctxLookup d_ k in
      begin if isFree status || isUniversal status || strictFun (k - d) then ()
      else
        raise
          (ModeError
             ( occ,
               ((("Occurrence of variable " ^ nameOf status) ^ " in ")
               ^ M.modeToString mode)
               ^ " argument not free" ))
      end

    (* -------------------------------- non-strict mode context update *)
    (** nonStrictExpN (D, U) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Unknown for all existential variables k
            in U that are free in D
    *)
    let rec nonStrictExpN (d_, a) = match a with
      | I.Root (I.BVar k, s) -> nonStrictSpineN (nonStrictVarD (d_, k), s)
      | I.Root (I.Const c, s) -> nonStrictSpineN (d_, s)
      | I.Root (I.Def d, s) -> nonStrictSpineN (d_, s)
      | I.Root (I.FgnConst (cs, conDec), s) -> nonStrictSpineN (d_, s)
      | I.Lam (_, u) ->
          I.ctxPop (nonStrictExpN (I.Decl (d_, Universal), u))
      | I.FgnExp (csfe1, csfe2) ->
          raise
            (Error "Foreign expressions not permitted when checking freeness")

    (** nonStrictSpineN (D, S) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Unkown for all existential variables k
            in S that are Free in D
    *)
    and nonStrictSpineN (d, a) = match a with
      | I.Nil -> d
      | I.App (u, s) -> nonStrictSpineN (nonStrictExpN (d, u), s)

    (** nonStrictVarD (D, k) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is nonStrictd as described in  nonStrictExpN
    *)
    and nonStrictVarD = function
      | I.Decl (d, Existential (Free, name)), 1 ->
          I.Decl (d, Existential (Unknown, name))
      | d, 1 -> d
      | I.Decl (d, status), k -> I.Decl (nonStrictVarD (d, k - 1), status)

    (* ------------------------------------------- mode context update *)
    (** updateExpN (D, U, u) = D'

       If   G |- U : V     (U in nf)
       and  D ~ G
       then D' >= D where D'(k) Ground for all existential variables k
            with a strict occurrence in U
            and D'(k) Unkown for all existential variable k
            with a non-strict occurrence, but no strict occurrence in U
            (if !checkFree is true)

       u is the uniqueness property for the new ground assumptions
    *)
    let rec updateExpN (d_, a, u) = match a with
      | I.Root (I.BVar k, s) ->
          begin if isUniversal (I.ctxLookup d_ k) then
            updateSpineN (d_, s, u)
          else
            begin if isPattern (d_, k, s) then updateVarD (d_, k, u)
            else
              begin if !checkFree then
                nonStrictSpineN (nonStrictVarD (d_, k), s)
              else d_
              end
            end
          end
      | I.Root (I.Const c, s) -> updateSpineN (d_, s, u)
      | I.Root (I.Def d, s) -> updateSpineN (d_, s, u)
      | I.Root (I.FgnConst (cs, conDec), s) -> updateSpineN (d_, s, u)
      | I.Lam (_, u_) ->
          I.ctxPop (updateExpN (I.Decl (d_, Universal), u_, u))
      | I.FgnExp (csfe1, csfe2) -> d_

    (** updateSpineN (D, S, u) = D'

       If   G |- S : V1 > V2      (S in nf)
       and  D ~ G
       then D' >= D' where D'(k) Ground for all existential variables k
            with a strict occurrence in S
    *)
    and updateSpineN (d, a, u) = match a with
      | I.Nil -> d
      | I.App (u_, s) -> updateSpineN (updateExpN (d, u_, u), s, u)

    (** updateVarD (D, k, u) = D'

       If   G |- k : V
       and  D ~ G
       and  k is an existential variable
       then D' >= D where k is updated as described in  updateExpN
    *)
    and updateVarD (a, k, u) = match a, k with
      | I.Decl (d, Existential (_, name)), 1 ->
          I.Decl (d, Existential (Ground u, name))
      | I.Decl (d, status), k -> I.Decl (updateVarD (d, k - 1, u), status)

    (* ----------------------- mode context update by argument modes *)
    (** updateAtom (D, m, S, mS, (p,occ)) = D'

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode
       then D' >= D where
            all Ui are updated if mi = m (mod uniqueness)

       The new ground variables are marked Unique
         if m = (-1) and mi = (-1) (when updating from subgoals with unique inputs)
         or m = mi = (+) (when updating from the clause head)
       Otherwise they are marked Ambig.

       (p,occ) is used in error message if freeness is to be checked
    *)
    let rec updateAtom' (d, _mode, a, b, c) = match _mode, a, b, c with
      | _mode, I.Nil, M.Mnil, _ -> d
      | M.Plus, I.App (u, s), M.Mapp (M.Marg (M.Plus, _), mS), (p, occ) ->
          updateAtom' (updateExpN (d, u, Unique), M.Plus, s, mS, (p + 1, occ))
      | M.Minus, I.App (u, s), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)
        ->
          updateAtom' (updateExpN (d, u, Ambig), M.Minus, s, mS, (p + 1, occ))
      | M.Minus, I.App (u, s), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ)
        ->
          updateAtom' (updateExpN (d, u, Ambig), M.Minus, s, mS, (p + 1, occ))
      | M.Minus1, I.App (u, s), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)
        ->
          updateAtom'
            (updateExpN (d, u, Ambig), M.Minus1, s, mS, (p + 1, occ))
      | M.Minus1, I.App (u, s), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ)
        ->
          updateAtom'
            (updateExpN (d, u, Unique), M.Minus1, s, mS, (p + 1, occ))
      | mode, I.App (u, s), M.Mapp (_, mS), (p, occ) ->
          updateAtom' (d, mode, s, mS, (p + 1, occ))
      (* when checking freeness, all arguments must be input (+) or output (-) *)
      (* therefore, no case for M.Mapp (M.Marg (M.Minus, _), mS) is provided here *)

    (** freeAtom (D, m, S, (V,s), mS, (p, occ)) = ()

       checks if all output arguments in S according to mS are free.
       Invariant: G |- S : V[s] >> P for some G and P  (S in nf)
                  G ~ D
                  mode = (-) or (+); ( * ) or (-1) are excluded
    *)
    let rec freeAtom (d, _mode, a, _vs_, b, c) = match _mode, a, _vs_, b, c with
      | _mode, I.Nil, _vs_, M.Mnil, _ -> ()
      | M.Minus, I.App (u, s_), (I.Pi ((I.Dec (_, v1), _), v2), s), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ) -> begin
          freeExpN
            ( d,
              0,
              M.Minus,
              u,
              P.arg p occ,
              function q -> strictExpN (d, q, Whnf.normalize (v1, s)) );
          freeAtom
            ( d,
              M.Minus,
              s_,
              Whnf.whnfExpandDef (v2, I.Dot (I.Exp u, s)),
              mS,
              (p + 1, occ) )
        end
      | mode, I.App (u, s_), (I.Pi (_, v2), s), M.Mapp (_, mS), (p, occ)
        ->
          freeAtom
            ( d,
              mode,
              s_,
              Whnf.whnfExpandDef (v2, I.Dot (I.Exp u, s)),
              mS,
              (p + 1, occ) )

    (** updateAtom (D, m, S, a, mS, (p, occ))
       see updateAtom', and performs additional freeness check if required
    *)
    let updateAtom (d, mode, s, a, mS, (p, occ)) =
      ignore begin if !checkFree then
          freeAtom (d, ambiguate mode, s, (I.constType a, I.id), mS, (p, occ))
        else ()
        end;
      updateAtom' (d, mode, s, mS, (p, occ))

    (* ------------------------------------------- groundness check *)
    (** groundExpN (D, mode, U, occ)  = u

       If   G |- U : V    (U in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundExpN terminates with u if  D |- U ground
                 else exception ModeError is raised
            if mode = (-1) then D |- U ground and U unique
                           else exception ModeError is raised

       u = Unique if all known variables in U are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
    let rec groundExpN (d_, mode, a, occ) = match a with
      | I.Root (I.BVar k, s) ->
          andUnique
            ( groundVar (d_, mode, k, P.head occ),
              groundSpineN (d_, mode, s, (1, occ)) )
      | I.Root (I.Const c, s) ->
          groundSpineN (d_, mode, s, (1, occ))
      | I.Root (I.Def d, s) ->
          groundSpineN (d_, mode, s, (1, occ))
      | I.Root (I.FgnConst (cs, conDec), s) ->
          groundSpineN (d_, mode, s, (1, occ))
      | I.Lam (_, u) ->
          groundExpN (I.Decl (d_, Universal), mode, u, P.body occ)
      | I.FgnExp (csfe1, csfe2) ->
          I.FgnExpStd.fold csfe1 csfe2
            (function
              | u_, u ->
                  andUnique
                    (groundExpN (d_, mode, Whnf.normalize (u_, I.id), occ), u))
            Unique
      (* punting on the occ here  - ak *)

    (** groundSpineN (D, mode, S, occ)  = u

       If   G |- S : V1  > V2   (S in nf)
       and  G ~ D
       then if mode = (+) or (-)
            then groundSpineN terminates with u if  D |- S ground
                 else exception ModeError is raised
            if mode = (-1) then D |- S ground and S unique
                           else exception ModeError is raised

       u = Unique if all known variables in S are Unique
       u = Ambig otherwise

       (occ and mode are used in error messages)
    *)
    and groundSpineN (d, mode, a, b) = match a, b with
      | I.Nil, _ -> Unique
      | I.App (u, s), (p, occ) ->
          andUnique
            ( groundExpN (d, mode, u, P.arg p occ),
              groundSpineN (d, mode, s, (p + 1, occ)) )

    (** groundVar (D, mode, k, occ)  = u

       If   G |- k : V1
       and  G ~ D
       then if mode = (+) or (-)
            then groundVar terminates with u if  D |- k ground
                 else exception ModeError is raised
            if mode = (-1) then D |- k ground and k unique
                           else exception ModeError is raised

       u = Unique if k is known to be unique, Ambig otherwise

       (occ and mode are used in error messages)
    *)
    and groundVar (d, mode, k, occ) = match mode with
      | M.Minus1 ->
          begin match I.ctxLookup d k with
          | Existential (Ground Unique, _) -> Unique
          | Universal -> Unique
          | Existential (Ground Ambig, x) as s ->
              raise
                (ModeError
                   ( occ,
                     ((("Occurrence of variable " ^ nameOf s) ^ " in ")
                     ^ M.modeToString M.Minus1)
                     ^ " argument not necessarily unique" ))
          | s ->
              raise
                (ModeError
                   ( occ,
                     ((("Occurrence of variable " ^ nameOf s) ^ " in ")
                     ^ M.modeToString M.Minus1)
                     ^ " argument not necessarily ground" ))
          end
      | mode ->
          let status = I.ctxLookup d k in
          begin if isGround status || isUniversal status then uniqueness status
          else
            raise
              (ModeError
                 ( occ,
                   ((("Occurrence of variable " ^ nameOf status) ^ " in ")
                   ^ M.modeToString mode)
                   ^ " argument not necessarily ground" ))
          end

    (* ------------------------------------------- groundness check by polarity *)
    (** groundAtom (D, m, S, mS, (p,occ))  = u

       If   G |- S : V > V'   ( S = U1 ; .. ; Un)
       and  D ~ G
       and  S ~ mS            (mS = m1 , .. , mn)
       and  m mode = (+) or (-1)
       then groundAtom returns u if  D |- Ui ground
            for all i s.t. mi = m (mod uniqueness)
            and checks that D |- Ui unique if mi = (-1) and m = (-)
       otherwise exception ModeError is raised

       u = Unique if all mi = m (mod uniqueness) are unique,
       u = Ambig otherwise

       ((p,occ) used in error messages)
    *)
    let rec groundAtom (d, mode, a, b, c) = match mode, a, b, c with
      | _, I.Nil, M.Mnil, _ -> Unique
      | M.Plus, I.App (u, s), M.Mapp (M.Marg (M.Plus, _), mS), (p, occ) ->
          andUnique
            ( groundExpN (d, M.Plus, u, P.arg p occ),
              groundAtom (d, M.Plus, s, mS, (p + 1, occ)) )
      | M.Minus, I.App (u, s), M.Mapp (M.Marg (M.Minus, _), mS), (p, occ)
        ->
          ignore (groundExpN (d, M.Minus, u, P.arg p occ));
          groundAtom (d, M.Minus, s, mS, (p + 1, occ))
      | M.Minus, I.App (u, s), M.Mapp (M.Marg (M.Minus1, _), mS), (p, occ)
        ->
          ignore (groundExpN (d, M.Minus1, u, P.arg p occ));
          groundAtom (d, M.Minus, s, mS, (p + 1, occ))
      | mode, I.App (u, s), M.Mapp (_, mS), (p, occ) ->
          groundAtom (d, mode, s, mS, (p + 1, occ))

    let ctxPush (m, ds) = List.map (function d -> I.Decl (d, m)) ds
    let ctxPop ds = List.map (function I.Decl (d, m) -> d) ds

    (* ------------------------------------------- mode checking first phase *)
    (* ctxPush (Ds, m) = Ds'
       raises the contexts Ds prepending m
    *)
    (* ctxPop Ds = Ds'
       lowers the contexts Ds
    *)
    (** checkD1 (D, V, occ, k) = ()

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then
            for each  mode mS of the head of V
              exists  some Di s.t. all (-) evars of mS are ground
                where  D' ~ G, D' >= D is obtained by updating D
                  and  k D' = [D1, ..., Di, ..., Dn]
                  and  Di ~ G, Di >= D' is obtained by mode checking on the subgoals of V

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *)
    let rec checkD1 (d_, b, occ, k) = match b with
      | I.Pi ((I.Dec (name, _), Maybe), v) ->
          checkD1
            ( I.Decl (d_, Existential (Free, name)),
              v,
              P.body occ,
              function I.Decl (d', m) -> ctxPush (m, k d') )
      | I.Pi ((I.Dec (name, v1), No), v2) ->
          checkD1
            ( I.Decl (d_, Existential (Free, name)),
              v2,
              P.body occ,
              function
              | I.Decl (d', m) ->
                  ctxPush (m, checkG1 (d', v1, P.label occ, k)) )
      | I.Root (I.Const a, s) ->
          let rec checkAll = function
            | [] -> ()
            | mS :: mSs ->
                let rec checkSome = function
                  | d' :: [] ->
                      (* D' is the only (last) possibility; on failure, we raise ModeError *)
                      ignore (groundAtom (d', M.Minus, s, mS, (1, occ)));
                      checkAll mSs
                  | d' :: ds ->
                      (* try D', if it doesn't work, try another context in the Ds *)
                      (try ignore (groundAtom (d', M.Minus, s, mS, (1, occ)))
                       with ModeError _ -> checkSome ds);
                      checkAll mSs
                in
                checkSome (k (updateAtom (d_, M.Plus, s, a, mS, (1, occ))))
          in
          checkAll (lookup (a, occ))
      | I.Root (I.Def d, s) ->
          let rec checkAll = function
            | [] -> ()
            | mS :: mSs ->
                let rec checkSome = function
                  | d' :: [] ->
                      (* D' is the only (last) possibility; on failure, we raise ModeError *)
                      ignore (groundAtom (d', M.Minus, s, mS, (1, occ)));
                      checkAll mSs
                  | d' :: ds ->
                      (* try D', if it doesn't work, try another context in the Ds *)
                      (try ignore (groundAtom (d', M.Minus, s, mS, (1, occ)))
                       with ModeError _ -> checkSome ds);
                      checkAll mSs
                in
                checkSome (k (updateAtom (d_, M.Plus, s, d, mS, (1, occ))))
          in
          checkAll (lookup (d, occ))

    (** checkG1 (D, V, occ, k) = Ds

       Invariant:
         if G |- V : L
         and  V does not contain Skolem constants
         and  D ~ G
         then forall D' >= D that mode checks V, (k D') is a sublist of Ds
         and for each Di in Ds, Di ~ G and Di >= D'

       exception ModeError is raised if the expression does not mode check
       exception Error' is raised if the expression contains type families
       that have no mode information associated with them
       (occ used in error messages)
    *)
    and checkG1 (d_, b, occ, k) = match b with
      | I.Pi ((_, Maybe), v) ->
          ctxPop
            (checkG1
               ( I.Decl (d_, Universal),
                 v,
                 P.body occ,
                 function I.Decl (d', m) -> ctxPush (m, k d') ))
      | I.Pi ((I.Dec (_, v1), No), v2) ->
          ctxPop
            begin
              checkD1 (d_, v1, P.label occ, function d' -> [ d' ]);
              checkG1
                ( I.Decl (d_, Universal),
                  v2,
                  P.body occ,
                  function I.Decl (d', m) -> ctxPush (m, k d') )
            end
      | I.Root (I.Const a, s) ->
          let rec checkList arg__1 arg__2 =
            begin match (arg__1, arg__2) with
            | found, [] -> []
            | false, mS :: [] ->
                begin match groundAtom (d_, M.Plus, s, mS, (1, occ)) with
                | Unique -> k (updateAtom (d_, M.Minus1, s, a, mS, (1, occ)))
                | Ambig -> k (updateAtom (d_, M.Minus, s, a, mS, (1, occ)))
                end
            | found, mS :: mSs ->
                let found' =
                  try
                    begin
                      ignore (groundAtom (d_, M.Plus, s, mS, (1, occ)));
                      true
                    end
                  with ModeError _ -> false
                in
                let ds' = checkList (found || found') mSs in
                begin if found' then
                  k (updateAtom (d_, M.Minus, s, a, mS, (1, occ))) @ ds'
                else ds'
                end
            end
          in
          checkList false (lookup (a, occ))
      | I.Root (I.Def d, s) ->
          let rec checkList arg__3 arg__4 =
            begin match (arg__3, arg__4) with
            | found, [] -> []
            | false, mS :: [] ->
                begin match groundAtom (d_, M.Plus, s, mS, (1, occ)) with
                | Unique -> k (updateAtom (d_, M.Minus1, s, d, mS, (1, occ)))
                | Ambig -> k (updateAtom (d_, M.Minus, s, d, mS, (1, occ)))
                end
            | found, mS :: mSs ->
                let found' =
                  try
                    begin
                      ignore (groundAtom (d_, M.Plus, s, mS, (1, occ)));
                      true
                    end
                  with ModeError _ -> false
                in
                let ds' = checkList (found || found') mSs in
                begin if found' then
                  k (updateAtom (d_, M.Minus, s, d, mS, (1, occ))) @ ds'
                else ds'
                end
            end
          in
          checkList false (lookup (d, occ))

    (** checkDlocal (D, V, occ) = ()

       Invariant:
       If   G |- V : L
       and  D ~ G
       then checkD terminates with ()  iff V is mode correct.

       otherwise exception ModeError is raised (occ used in error messages)
    *)
    let checkDlocal (d, v, occ) =
      try checkD1 (d, v, occ, function d' -> [ d' ])
      with ModeError (occ, msg) -> error'' ( (occ, msg))

    (* --------------------------------------------------------- mode checking *)
    let cidFromHead = function I.Const a -> a | I.Def a -> a

    (** checkD (ConDec, occOpt)  = ()

       checkD terminates with () if ConDec is mode correct
       otherwise exception Error is raised

       (occOpt is used in error messages)
    *)
    let checkD conDec fileName occOpt =
      ignore (checkFree := false);
      let rec checkable = function
        | I.Root (ha, _) ->
            begin match ModeTable.mmodeLookup (cidFromHead ha) with
            | [] -> false
            | _ -> true
            end
        | I.Uni _ -> false
        | I.Pi (_, v) -> checkable v
      in
      let v = I.conDecType conDec in
      begin if checkable v then
        try checkDlocal (I.Null, v, P.top)
        with Error' (occ, msg) ->
          begin match occOpt with
          | None -> raise (Error msg)
          | Some occTree ->
              raise
                (Error
                   (wrapMsg' (fileName, P.occToRegionClause occTree occ, msg)))
          end
      else ()
      end

    let rec checkAll = function
      | [] -> ()
      | I.Const c :: clist -> begin
          Display.(debug Form.(string "checking mode of constant" ++ space () ++ shown (fun x -> Names.qidToString @@ Names.constQid c) c ++ space () ++ string "..." ++ nl ()));
          
          (try checkDlocal (I.Null, I.constType c, P.top)
           with Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))));
          checkAll clist
        end
      | I.Def d :: clist -> begin
          begin if !Global.chatter > 3 then
            print' (Names.qidToString (Names.constQid d) ^ " ")
          else ()
          end;
          (try checkDlocal (I.Null, I.constType d, P.top)
           with Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))));
          checkAll clist
        end

    let checkMode a ms =
      ignore begin if !Global.chatter > 3 then
          print'
            (("Mode checking family " ^ Names.qidToString (Names.constQid a))
            ^ ":\n")
        else ()
        end;
      let clist = Index.lookup a in
      ignore (checkFree := false);
      ignore (checkAll clist);
      ignore begin if !Global.chatter > 3 then print' "\n" else ()
        end;
      ()

    let checkFreeOut a ms =
      ignore begin if !Global.chatter > 3 then
          print'
            (("Checking output freeness of "
             ^ Names.qidToString (Names.constQid a))
            ^ ":\n")
        else ()
        end;
      let clist = Index.lookup a in
      ignore (checkFree := true);
      ignore (checkAll clist);
      ignore begin if !Global.chatter > 3 then print' "\n" else ()
        end;
      ()
  end

  let checkD = checkD
  let checkMode = checkMode
  let checkFreeOut = checkFreeOut
end
(*! sharing Origins.Paths = Paths !*)
(*! sharing Origins.IntSyn = IntSyn !*)
(* functor ModeCheck *)

(* # 1 "src/modes/Modecheck.sml.ml" *)
