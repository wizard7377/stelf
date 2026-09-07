open! Global.Global_
open! Table.Table_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print.Print_
open! Index.Index_
open! Subordinate
open! Solvers.Solvers_

(* # 1 "src/worldcheck/Worldify.sig.ml" *)

(* Worldify *)
(* Author: Carsten Schuermann *)
include WORLDIFY

(*  val check : Tomega.Worlds -> IntSyn.cid list -> unit
  val closure : Tomega.Worlds -> Tomega.Worlds *)
(* signature WORLDIFY *)

(* # 1 "src/worldcheck/Worldify.fun.ml" *)
open! Basis

(* Worldification and World-checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception Error' of Paths.occ * string

let () =
  Printexc.register_printer (function Error' (_, msg) -> Some msg | _ -> None)

module Worldify (Worldify__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  (*! sharing Tomega.IntSyn = IntSyn !*)
  module WorldSyn : WorldSyn.WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn !*)
  (*! sharing WorldSyn.Tomega = Tomega !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn !*)
  module CsManager : CsManager.CS_MANAGER

  (*! sharing CsManager.IntSyn = IntSyn !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Table : TABLE
  module MemoTable : TABLE
  module IntSet : Intset.INTSET

  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS
end) : WORLDIFY = struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure Tomega = Tomega !*)
  module Origins = Worldify__0.Origins
  module Subordinate = Worldify__0.Subordinate
  module I = IntSyn
  module T = Tomega
  module P = Paths
  module F = Print.Formatter
  module Unify = Worldify__0.Unify
  module CsManager = Worldify__0.CsManager
  module WorldSyn = Worldify__0.WorldSyn

  exception Error = Error
  exception Error' = Error'

  (* copied from terminates/Reduces.fun *)
  let wrapMsg (c, occ, msg) =
    begin match Origins.originLookup c with
    | fileName, None -> (fileName ^ ":") ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          (P.Loc (fileName, P.occToRegionDec occDec occ)) (Origins.linesInfoLookup fileName) ((("Constant " ^ Names.qidToString (Names.constQid c)) ^ ":") ^ msg)
    end

  let wrapMsgBlock (c, occ, msg) =
    begin match Origins.originLookup c with
    | fileName, None -> (fileName ^ ":") ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          (P.Loc (fileName, P.occToRegionDec occDec occ)) (Origins.linesInfoLookup fileName) ((("Block " ^ Names.qidToString (Names.constQid c)) ^ ":") ^ msg)
    end

  type nonrec dlist = IntSyn.dec list

  open! struct
    module W = WorldSyn

    type reg =
      | Block of I.cid * (I.dctx * dlist)
      | Seq of int * dlist * I.sub
      | Star of reg
      | Plus of reg * reg
      | One

    exception Success of I.exp

    let rec createEVarSub (g, a) = match a with
      | I.Null -> I.Shift (I.ctxLength g)
      | I.Decl (g', (I.Dec (_, v) as d)) ->
          let s = createEVarSub (g, g') in
          let v' = I.EClo (v, s) in
          let x = I.newEVar g v' in
          I.Dot (I.Exp x, s)

    let rec collectConstraints = function
      | [] -> []
      | I.EVar (_, _, _, { contents = [] }) :: xs -> collectConstraints xs
      | I.EVar (_, _, _, { contents = constrs }) :: xs ->
          Constraints.simplify constrs @ collectConstraints xs

    let rec collectEVars a3 b3 c3 = match a3, b3, c3 with
      | g, I.Dot (I.Exp x, s), xs ->
          collectEVars g s (Abstract.collectEVars g (x, I.id) xs)
      | g, I.Shift _, xs -> xs

    let noConstraints (g, s) =
      begin match collectConstraints (collectEVars g s []) with
      | [] -> true
      | _ -> false
      end

    let formatD (g, d) =
      F.hbox [ F.string "{"; Print.formatDec g d; F.string "}" ]

    let rec formatDList (g, a, t) = match a with
      | [] -> []
      | d :: [] ->
          let d' = I.decSub d t in
          [ formatD (g, d') ]
      | d :: l ->
          let d' = I.decSub d t in
          formatD (g, d')
          :: F.break_
          :: formatDList (I.Decl (g, d'), l, I.dot1 t)

    let wGoalToString ((g, l), Seq (_, piDecs, t)) =
      F.makestring_fmt
        (F.hVbox
           [
             F.hVbox (formatDList (g, l, I.id));
             F.break_;
             F.string "<|";
             F.break_;
             F.hVbox (formatDList (g, piDecs, t));
           ])

    let worldToString (g, Seq (_, piDecs, t)) =
      F.makestring_fmt (F.hVbox (formatDList (g, piDecs, t)))

    let hypsToString (g, l) =
      F.makestring_fmt (F.hVbox (formatDList (g, l, I.id)))

    let mismatchToString (g, (v1, s1), (v2, s2)) =
      F.makestring_fmt
        (F.hVbox
           [
             Print.formatExp g (I.EClo (v1, s1));
             F.break_;
             F.string "<>";
             F.break_;
             Print.formatExp g (I.EClo (v2, s2));
           ])

    module Trace : sig
      val clause : I.cid -> unit
      val constraintsRemain : unit -> unit
      val matchBlock : (I.dctx * dlist) * reg -> unit
      val unmatched : I.dctx -> dlist -> unit
      val missing : I.dctx -> reg -> unit
      val mismatch : I.dctx -> I.eclo -> I.eclo -> unit
      val success : unit -> unit
    end = struct
      let clause c =
        print
          (("World checking clause " ^ Names.qidToString (Names.constQid c))
          ^ "\n")

      let constraintsRemain () =
        begin if !Global.chatter > 7 then
          print
            "Constraints remain after matching hypotheses against context block\n"
        else ()
        end

      let matchBlock (gl, r) =
        begin if !Global.chatter > 7 then
          print (("Matching:\n" ^ wGoalToString (gl, r)) ^ "\n")
        else ()
        end

      let unmatched g l =
        let gl = (g, l) in
        begin if !Global.chatter > 7 then
          print (("Unmatched hypotheses:\n" ^ hypsToString gl) ^ "\n")
        else ()
        end

      let missing g r =
        begin if !Global.chatter > 7 then
          print (("Missing hypotheses:\n" ^ worldToString (g, r)) ^ "\n")
        else ()
        end

      let mismatch g vs1 vs2 =
        begin if !Global.chatter > 7 then
          print (("Mismatch:\n" ^ mismatchToString (g, vs1, vs2)) ^ "\n")
        else ()
        end

      let success () =
        begin if !Global.chatter > 7 then print "Success\n" else ()
        end
    end

    let decUName g d = I.Decl (g, Names.decUName g d)
    let decEName g d = I.Decl (g, Names.decEName g d)

    let rec equivList (g, a, b) = match a, b with
      | (_, []), [] -> true
      | (t, I.Dec (_, v1) :: l1), I.Dec (_, v2) :: l2 -> (
          try
            begin
              Unify.unify g (v1, t) (v2, I.id);
              equivList (g, (I.dot1 t, l1), l2)
            end
          with
          | Unify.Unify _ -> false
          | _ -> false)

    let equivBlock ((g, l), l') =
      let t = createEVarSub (I.Null, g) in
      equivList (I.Null, (t, l), l')

    let rec equivBlocks arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | w1, [] -> true
      | [], l' -> false
      | b :: w1, l' -> equivBlock (I.constBlock b, l') || equivBlocks w1 l'
      end

    let rec strengthen arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | a, (t, []) -> []
      | a, (t, (I.Dec (_, v) as d) :: l) ->
          begin if Subordinate.below (I.targetFam v) a then
            I.decSub d t :: strengthen a (I.dot1 t, l)
          else strengthen a (I.Dot (I.Undef, t), l)
          end
      end

    let subsumedBlock a w1 (g, l) =
      let t = createEVarSub (I.Null, g) in
      let l' = strengthen a (t, l) in
      begin if equivBlocks w1 l' then ()
      else raise (Error "Static world subsumption failed")
      end

    let rec subsumedBlocks arg__5 arg__6 arg__7 =
      begin match (arg__5, arg__6, arg__7) with
      | a, w1, [] -> ()
      | a, w1, b :: w2 -> begin
          subsumedBlock a w1 (I.constBlock b);
          subsumedBlocks a w1 w2
        end
      end

    let subsumedWorld a (T.Worlds w1) (T.Worlds w2) = subsumedBlocks a w1 w2

    let rec eqCtx = function
      | I.Null, I.Null -> true
      | I.Decl (g1, d1), I.Decl (g2, d2) ->
          eqCtx (g1, g2) && Conv.convDec d1 I.id (d2, I.id)
      | _ -> false

    let rec eqList = function
      | [], [] -> true
      | d1 :: l1, d2 :: l2 ->
          Conv.convDec d1 I.id (d2, I.id) && eqList (l1, l2)
      | _ -> false

    let eqBlock (b1, b2) =
      let g1, l1 = I.constBlock b1 in
      let g2, l2 = I.constBlock b2 in
      eqCtx (g1, g2) && eqList (l1, l2)

    let rec subsumedCtx = function
      | I.Null, w -> ()
      | I.Decl (g, I.BDec (_, (b, _))), (T.Worlds bs as w) -> begin
          begin if List.exists (function b' -> eqBlock (b, b')) bs then ()
          else raise (Error "Dynamic world subsumption failed")
          end;
          subsumedCtx (g, w)
        end
      | I.Decl (g, _), (T.Worlds bs as w) -> subsumedCtx (g, w)

    let rec checkGoal arg__8 arg__9 =
      begin match (arg__8, arg__9) with
      | w, (g, I.Root (I.Const a, s), occ) ->
          let w' = W.getWorlds a in
          subsumedWorld a w' w;
          subsumedCtx (g, w)
      | w, (g, I.Pi ((d, _), v2), occ) ->
          checkGoal w (decUName g d, v2, P.body occ)
      end

    let rec checkClause arg__10 arg__11 =
      begin match (arg__10, arg__11) with
      | w, (g, I.Root (a, s), occ) -> ()
      | w, (g, I.Pi (((I.Dec (_, v1) as d), Maybe), v2), occ) ->
          checkClause w (decEName g d, v2, P.body occ)
      | w, (g, I.Pi (((I.Dec (_, v1) as d), No), v2), occ) -> begin
          checkClause w (decEName g d, v2, P.body occ);
          checkGoal w (g, v1, P.label occ)
        end
      end

    let checkConDec w (I.ConDec (s, m, k, status, v, l)) =
      checkClause w (I.Null, v, P.top)

    let rec subGoalToDList = function
      | I.Pi ((d, _), v) -> d :: subGoalToDList v
      | I.Root _ -> []

    let rec worldsToReg = function
      | T.Worlds [] -> One
      | T.Worlds cids -> Star (worldsToReg' cids)

    and worldsToReg' = function
      | cid :: [] -> Block (cid, I.constBlock cid)
      | cid :: cids -> Plus (Block (cid, I.constBlock cid), worldsToReg' cids)

    let init (g, a) = match a with
      | ((I.Root _, s) as vs) -> begin
          Trace.success ();
          raise (Success (Whnf.normalize vs))
        end
      | ((I.Pi (((I.Dec (_, v1) as d1), _), v2) as v), s) -> begin
          Trace.unmatched g (subGoalToDList (Whnf.normalize (v, s)));
          ()
        end

    let rec accR (a, b, k) = match a, b with
      | gVs, One -> k gVs
      | ((g, (v, s)) as gVs), Block (c, (someDecs, piDecs)) -> (
          let t = createEVarSub (g, someDecs) in
          ignore (Trace.matchBlock
              ((g, subGoalToDList (Whnf.normalize (v, s))), Seq (1, piDecs, t)));
          let k' (g', vs') =
                begin if noConstraints (g, t) then k (g', vs')
                else begin
                  Trace.constraintsRemain ();
                  ()
                end
                end
          in
          try
            accR
              ( (decUName g (I.BDec (None, (c, t))), (v, I.comp s I.shift)),
                Seq (1, piDecs, I.comp t I.shift),
                k' )
          with Success v ->
            raise
              (Success
                 (Whnf.normalize
                    (I.Pi ((I.BDec (None, (c, t)), I.Maybe), v), I.id))))
      | (g, ((I.Pi (((I.Dec (_, v1) as d), _), v2) as v), s)), (Seq (j, I.Dec (_, v1') :: l2', t) as l') ->
          begin if Unify.unifiable g (v1, s) (v1', t) then
            accR
              ( ( g,
                  (v2, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), s))
                ),
                Seq
                  ( j + 1,
                    l2',
                    I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), t) ),
                k )
          else begin
            Trace.mismatch g (v1, I.id) (v1', t);
            ()
          end
          end
      | gVs, Seq (_, [], t) -> k gVs
      | ((g, (I.Root _, s)) as gVs), (Seq (_, l', t) as r) -> begin
          Trace.missing g r;
          ()
        end
      | gVs, Plus (r1, r2) -> begin
          CsManager.trail (function () -> accR (gVs, r1, k));
          accR (gVs, r2, k)
        end
      | gVs, Star One -> k gVs
      | gVs, (Star r' as r) -> begin
          CsManager.trail (function () -> k gVs);
          accR (gVs, r', function gVs' -> accR (gVs', r, k))
        end

    let worldifyGoal (g, v, (T.Worlds cids as w), occ) =
      try
        let b = I.targetFam v in
        let wb = W.getWorlds b in
        let rb = worldsToReg wb in
        accR ((g, (v, I.id)), rb, init);
        raise (Error' (occ, "World violation"))
      with Success v' -> v'

    let rec worldifyClause (g, b, w, occ) = match b with
      | (I.Root (a, s) as v) -> v
      | I.Pi (((I.Dec (x, v1) as d), Maybe), v2) ->
          ignore (print "{");
          let w2 = worldifyClause (decEName g d, v2, w, P.body occ) in
          ignore (print "}");
          I.Pi ((I.Dec (x, v1), I.Maybe), w2)
      | I.Pi (((I.Dec (x, v1) as d), No), v2) ->
          let w1 = worldifyGoal (g, v1, w, P.label occ) in
          let w2 = worldifyClause (decEName g d, v2, w, P.body occ) in
          I.Pi ((I.Dec (x, w1), I.No), w2)

    let worldifyConDec w (c, I.ConDec (s, m, k, status, v, l)) =
      begin
        begin if !Global.chatter = 4 then
          print (Names.qidToString (Names.constQid c) ^ " ")
        else ()
        end;
        begin
          begin if !Global.chatter > 4 then Trace.clause c else ()
          end;
          try
            I.ConDec
              (s, m, k, status, worldifyClause (I.Null, v, w, P.top), l)
          with Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg)))
        end
      end

    let rec worldifyBlock (g, b) = match b with
      | [] -> ()
      | (I.Dec (_, v) as d) :: l ->
          let a = I.targetFam v in
          let w' = W.getWorlds a in
          checkClause w' (g, worldifyClause (I.Null, v, w', P.top), P.top);
          worldifyBlock (decUName g d, l)

    let rec worldifyBlocks = function
      | [] -> ()
      | b :: bs -> (
          ignore (worldifyBlocks bs);
          let gsome, lblock = I.constBlock b in
          ignore (print "|");
          try worldifyBlock (gsome, lblock)
          with Error' (occ, s) ->
            raise
              (Error (wrapMsgBlock (b, occ, "World not hereditarily closed"))))

    let worldifyWorld (T.Worlds bs) = worldifyBlocks bs

    let worldify a =
      let w = W.getWorlds a in
      ignore (print "[?");
      let w' = worldifyWorld w in
      ignore (print ";");
      ignore begin if !Global.chatter > 3 then
          print
            (("World checking family " ^ Names.qidToString (Names.constQid a))
            ^ ":\n")
        else ()
        end;
      let condecs =
        map
          (function
            | I.Const c -> (
                try worldifyConDec w (c, I.sgnLookup c)
                with Error' (occ, s) -> raise (Error (wrapMsg (c, occ, s)))))
          (Index.lookup a)
      in
      ignore (map
          (function
            | condec -> begin
                print "#";
                checkConDec w condec
              end)
          condecs);
      ignore (print "]");
      ignore begin if !Global.chatter = 4 then print "\n" else ()
        end;
      condecs
  end

  (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
  (* Regular world expressions  *)
  (* R ::= LD                   *)
  (*     | (Di,...,Dn)[s]       *)
  (*     | R*                   *)
  (*     | R1 + R2              *)
  (*     | 1                    *)
  (* signals worldcheck success *)
  (* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
  (* from Cover.fun *)
  (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are ""hard""
    *)
  (* constrs <> nil *)
  (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
  (* other cases impossible by invariants since s is EVarSubst *)
  (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
  (************)
  (* Printing *)
  (************)
  (* Declarations *)
  (* Declaration lists *)
  (* Names.decUName (G, I.decSub(D, t)) *)
  (* Names.decUName (G, I.decSub (D, t)) *)
  (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *)
  (* Hypotheses and declaration lists *)
  (* Declaration list *)
  (* Hypotheses *)
  (* Mismatch between hypothesis and world declaration *)
  (***********)
  (* Tracing *)
  (***********)
  (* R = (D1,...,Dn)[t] *)
  (* R = (D1,...,Dn)[t] *)
  (* ******************** *)
  (* World Subsumption    *)
  (* The STATIC part      *)
  (* ******************** *)
  (* equivList (G, (t, L), L')

        Invariant:
        If  . |- t : G
        and G |- L block
        then  B = true if  L [t] unifies with L'
              B = false otherwise
     *)
  (* equivBlock ((G, L), L') = B

        Invariant:
        If   G |- L block
        then B = true if there exists a substitution . |- t : G, s.t. L[t] = L'
             B = false otherwise
     *)
  (* equivBlocks W L = B

        Invariant:
        Let W be a world and L be a block.
        B = true if exists L' in W such that L = L'
        B = false otherwise
     *)
  (* strengthen a (t, L) = L'

        Invariant:
        If   a is a type family,
        and  . |- t : G
        and  G |- L block
        then . |- L' block
        where V \in L and not V < a then V \in L'
        and   V \in L and V < a then not V \in L'
     *)
  (* subsumedBlock a W1 (G, L) = ()

        Invariant:
        If   a is a type family
        and  W1 the world in which the callee is defined
        and (G, L) one block in the world of the caller
        Then the function returns () if (G, L) is subsumed by W1
        otherwise Error is raised
     *)
  (* G |- t : someDecs *)
  (* subsumedBlocks a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
  (* subsumedWorld a W1 W2 = ()

        Invariant:
        Let W1 be the world in which the callee is defined
        Let W2 be the world in which the caller is defined
        Then the function returns () if W2 is subsumed by W1
        otherwise Error is raised
     *)
  (* ******************** *)
  (* World Subsumption    *)
  (* The DYNAMIC part     *)
  (* ******************** *)
  (* eqCtx (G1, G2) = B

        Invariant:
        Let  G1, G2 constexts of declarations (as the occur in the some part
                    of a block).
        B = true if G1 and G2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
  (* eqList (L1, L2) = B

        Invariant:
        Let  L1, L2 lists of declarations (as the occur in a block).
        B = true if L1 and L2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
  (* eqBlock (b1, b2) = B

        Invariant:
        Let  b1, b2 blocks.
        B = true if b1 and b2 are equal (modulo renaming of variables)
        B = false otherwise
     *)
  (* sumbsumedCtx (G, W) = ()

        Invariant:
        Let G be a context of blocks
        and W a world
        Then the function returns () if every block in G
        is listed in W
        otherwise Error is raised
     *)
  (******************************)
  (* Checking clauses and goals *)
  (******************************)
  (* checkGoal W (G, V, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
  (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
  (**************************************)
  (* Matching hypotheses against worlds *)
  (**************************************)
  (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *)
  (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
  (* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
  (* G |- t : someDecs *)
  (* L is missing *)
  (* only possibility for non-termination in next rule *)
  (* r' does not accept empty declaration list *)
  (******************************)
  (* Worldifying clauses and goals *)
  (******************************)
  (* worldifyGoal (G, V, W, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
    *)
  (* worldifyClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
  (*         val W1 = worldifyGoal (G, V1, W, P.label occ) *)
  (* W1*)
  (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
  (* by invariant, other cases cannot apply *)
  let worldify = worldify

  let worldifyGoal a3 b3 = match a3, b3 with
    | g, v -> worldifyGoal (g, v, W.getWorlds (I.targetFam v), P.top)
end
(*! sharing Origins.Paths = Paths !*)
(*! sharing Origins.IntSyn = IntSyn !*)
(* functor Worldify *)

(* # 1 "src/worldcheck/Worldify.sml.ml" *)
