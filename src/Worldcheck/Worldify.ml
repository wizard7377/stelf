open! Basis
open! Global
open! Global.Global_
open! Timing
open! Timing.Timing_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Index
open! Index.Index_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/worldcheck/Worldify.sig.ml" *)
open! Basis

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

    let rec createEVarSub (g_, a) = match a with
      | I.Null -> I.Shift (I.ctxLength g_)
      | I.Decl (g'_, (I.Dec (_, v_) as d_)) ->
          let s = createEVarSub (g_, g'_) in
          let v'_ = I.EClo (v_, s) in
          let x_ = I.newEVar g_ v'_ in
          I.Dot (I.Exp x_, s)

    let rec collectConstraints = function
      | [] -> []
      | I.EVar (_, _, _, { contents = [] }) :: xs_ -> collectConstraints xs_
      | I.EVar (_, _, _, { contents = constrs }) :: xs_ ->
          Constraints.simplify constrs @ collectConstraints xs_

    let rec collectEVars a3 b3 c3 = match a3, b3, c3 with
      | g_, I.Dot (I.Exp x_, s), xs_ ->
          collectEVars g_ s (Abstract.collectEVars g_ (x_, I.id) xs_)
      | g_, I.Shift _, xs_ -> xs_

    let noConstraints (g_, s) =
      begin match collectConstraints (collectEVars g_ s []) with
      | [] -> true
      | _ -> false
      end

    let formatD (g_, d_) =
      F.hbox [ F.string "{"; Print.formatDec g_ d_; F.string "}" ]

    let rec formatDList (g_, a, t) = match a with
      | [] -> []
      | d_ :: [] ->
          let d'_ = I.decSub d_ t in
          [ formatD (g_, d'_) ]
      | d_ :: l_ ->
          let d'_ = I.decSub d_ t in
          formatD (g_, d'_)
          :: F.break_
          :: formatDList (I.Decl (g_, d'_), l_, I.dot1 t)

    let wGoalToString ((g_, l_), Seq (_, piDecs, t)) =
      F.makestring_fmt
        (F.hVbox
           [
             F.hVbox (formatDList (g_, l_, I.id));
             F.break_;
             F.string "<|";
             F.break_;
             F.hVbox (formatDList (g_, piDecs, t));
           ])

    let worldToString (g_, Seq (_, piDecs, t)) =
      F.makestring_fmt (F.hVbox (formatDList (g_, piDecs, t)))

    let hypsToString (g_, l_) =
      F.makestring_fmt (F.hVbox (formatDList (g_, l_, I.id)))

    let mismatchToString (g_, (v1_, s1), (v2_, s2)) =
      F.makestring_fmt
        (F.hVbox
           [
             Print.formatExp g_ (I.EClo (v1_, s1));
             F.break_;
             F.string "<>";
             F.break_;
             Print.formatExp g_ (I.EClo (v2_, s2));
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

      let matchBlock (gl_, r_) =
        begin if !Global.chatter > 7 then
          print (("Matching:\n" ^ wGoalToString (gl_, r_)) ^ "\n")
        else ()
        end

      let unmatched g_ l_ =
        let gl_ = (g_, l_) in
        begin if !Global.chatter > 7 then
          print (("Unmatched hypotheses:\n" ^ hypsToString gl_) ^ "\n")
        else ()
        end

      let missing g_ r_ =
        begin if !Global.chatter > 7 then
          print (("Missing hypotheses:\n" ^ worldToString (g_, r_)) ^ "\n")
        else ()
        end

      let mismatch g_ vs1 vs2 =
        begin if !Global.chatter > 7 then
          print (("Mismatch:\n" ^ mismatchToString (g_, vs1, vs2)) ^ "\n")
        else ()
        end

      let success () =
        begin if !Global.chatter > 7 then print "Success\n" else ()
        end
    end

    let decUName g_ d_ = I.Decl (g_, Names.decUName g_ d_)
    let decEName g_ d_ = I.Decl (g_, Names.decEName g_ d_)

    let rec equivList (g_, a, b) = match a, b with
      | (_, []), [] -> true
      | (t, I.Dec (_, v1_) :: l1_), I.Dec (_, v2_) :: l2_ -> (
          try
            begin
              Unify.unify g_ (v1_, t) (v2_, I.id);
              equivList (g_, (I.dot1 t, l1_), l2_)
            end
          with
          | Unify.Unify _ -> false
          | _ -> false)

    let equivBlock ((g_, l_), l'_) =
      let t = createEVarSub (I.Null, g_) in
      equivList (I.Null, (t, l_), l'_)

    let rec equivBlocks arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | w1_, [] -> true
      | [], l'_ -> false
      | b :: w1_, l'_ -> equivBlock (I.constBlock b, l'_) || equivBlocks w1_ l'_
      end

    let rec strengthen arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | a, (t, []) -> []
      | a, (t, (I.Dec (_, v_) as d_) :: l_) ->
          begin if Subordinate.below (I.targetFam v_) a then
            I.decSub d_ t :: strengthen a (I.dot1 t, l_)
          else strengthen a (I.Dot (I.Undef, t), l_)
          end
      end

    let subsumedBlock a w1_ (g_, l_) =
      let t = createEVarSub (I.Null, g_) in
      let l'_ = strengthen a (t, l_) in
      begin if equivBlocks w1_ l'_ then ()
      else raise (Error "Static world subsumption failed")
      end

    let rec subsumedBlocks arg__5 arg__6 arg__7 =
      begin match (arg__5, arg__6, arg__7) with
      | a, w1_, [] -> ()
      | a, w1_, b :: w2_ -> begin
          subsumedBlock a w1_ (I.constBlock b);
          subsumedBlocks a w1_ w2_
        end
      end

    let subsumedWorld a (T.Worlds w1_) (T.Worlds w2_) = subsumedBlocks a w1_ w2_

    let rec eqCtx = function
      | I.Null, I.Null -> true
      | I.Decl (g1_, d1_), I.Decl (g2_, d2_) ->
          eqCtx (g1_, g2_) && Conv.convDec d1_ I.id (d2_, I.id)
      | _ -> false

    let rec eqList = function
      | [], [] -> true
      | d1_ :: l1_, d2_ :: l2_ ->
          Conv.convDec d1_ I.id (d2_, I.id) && eqList (l1_, l2_)
      | _ -> false

    let eqBlock (b1, b2) =
      let g1_, l1_ = I.constBlock b1 in
      let g2_, l2_ = I.constBlock b2 in
      eqCtx (g1_, g2_) && eqList (l1_, l2_)

    let rec subsumedCtx = function
      | I.Null, w_ -> ()
      | I.Decl (g_, I.BDec (_, (b, _))), (T.Worlds bs_ as w_) -> begin
          begin if List.exists (function b' -> eqBlock (b, b')) bs_ then ()
          else raise (Error "Dynamic world subsumption failed")
          end;
          subsumedCtx (g_, w_)
        end
      | I.Decl (g_, _), (T.Worlds bs_ as w_) -> subsumedCtx (g_, w_)

    let rec checkGoal arg__8 arg__9 =
      begin match (arg__8, arg__9) with
      | w_, (g_, I.Root (I.Const a, s_), occ) ->
          let w'_ = W.getWorlds a in
          subsumedWorld a w'_ w_;
          subsumedCtx (g_, w_)
      | w_, (g_, I.Pi ((d_, _), v2_), occ) ->
          checkGoal w_ (decUName g_ d_, v2_, P.body occ)
      end

    let rec checkClause arg__10 arg__11 =
      begin match (arg__10, arg__11) with
      | w_, (g_, I.Root (a, s_), occ) -> ()
      | w_, (g_, I.Pi (((I.Dec (_, v1_) as d_), Maybe), v2_), occ) ->
          checkClause w_ (decEName g_ d_, v2_, P.body occ)
      | w_, (g_, I.Pi (((I.Dec (_, v1_) as d_), No), v2_), occ) -> begin
          checkClause w_ (decEName g_ d_, v2_, P.body occ);
          checkGoal w_ (g_, v1_, P.label occ)
        end
      end

    let checkConDec w_ (I.ConDec (s, m, k, status, v_, l_)) =
      checkClause w_ (I.Null, v_, P.top)

    let rec subGoalToDList = function
      | I.Pi ((d_, _), v_) -> d_ :: subGoalToDList v_
      | I.Root _ -> []

    let rec worldsToReg = function
      | T.Worlds [] -> One
      | T.Worlds cids -> Star (worldsToReg' cids)

    and worldsToReg' = function
      | cid :: [] -> Block (cid, I.constBlock cid)
      | cid :: cids -> Plus (Block (cid, I.constBlock cid), worldsToReg' cids)

    let init (g_, a) = match a with
      | ((I.Root _, s) as vs_) -> begin
          Trace.success ();
          raise (Success (Whnf.normalize vs_))
        end
      | ((I.Pi (((I.Dec (_, v1_) as d1_), _), v2_) as v_), s) -> begin
          Trace.unmatched g_ (subGoalToDList (Whnf.normalize (v_, s)));
          ()
        end

    let rec accR (a, b, k) = match a, b with
      | gVs, One -> k gVs
      | ((g_, (v_, s)) as gVs), Block (c, (someDecs, piDecs)) -> (
          let t = createEVarSub (g_, someDecs) in
          ignore (Trace.matchBlock
              ((g_, subGoalToDList (Whnf.normalize (v_, s))), Seq (1, piDecs, t)));
          let k' (g'_, vs'_) =
                begin if noConstraints (g_, t) then k (g'_, vs'_)
                else begin
                  Trace.constraintsRemain ();
                  ()
                end
                end
          in
          try
            accR
              ( (decUName g_ (I.BDec (None, (c, t))), (v_, I.comp s I.shift)),
                Seq (1, piDecs, I.comp t I.shift),
                k' )
          with Success v_ ->
            raise
              (Success
                 (Whnf.normalize
                    (I.Pi ((I.BDec (None, (c, t)), I.Maybe), v_), I.id))))
      | (g_, ((I.Pi (((I.Dec (_, v1_) as d_), _), v2_) as v_), s)), (Seq (j, I.Dec (_, v1') :: l2'_, t) as l'_) ->
          begin if Unify.unifiable g_ (v1_, s) (v1', t) then
            accR
              ( ( g_,
                  (v2_, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), s))
                ),
                Seq
                  ( j + 1,
                    l2'_,
                    I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), t) ),
                k )
          else begin
            Trace.mismatch g_ (v1_, I.id) (v1', t);
            ()
          end
          end
      | gVs, Seq (_, [], t) -> k gVs
      | ((g_, (I.Root _, s)) as gVs), (Seq (_, l'_, t) as r_) -> begin
          Trace.missing g_ r_;
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

    let worldifyGoal (g_, v_, (T.Worlds cids as w_), occ) =
      try
        let b = I.targetFam v_ in
        let wb = W.getWorlds b in
        let rb = worldsToReg wb in
        accR ((g_, (v_, I.id)), rb, init);
        raise (Error' (occ, "World violation"))
      with Success v'_ -> v'_

    let rec worldifyClause (g_, b, w_, occ) = match b with
      | (I.Root (a, s_) as v_) -> v_
      | I.Pi (((I.Dec (x, v1_) as d_), Maybe), v2_) ->
          ignore (print "{");
          let w2_ = worldifyClause (decEName g_ d_, v2_, w_, P.body occ) in
          ignore (print "}");
          I.Pi ((I.Dec (x, v1_), I.Maybe), w2_)
      | I.Pi (((I.Dec (x, v1_) as d_), No), v2_) ->
          let w1_ = worldifyGoal (g_, v1_, w_, P.label occ) in
          let w2_ = worldifyClause (decEName g_ d_, v2_, w_, P.body occ) in
          I.Pi ((I.Dec (x, w1_), I.No), w2_)

    let worldifyConDec w_ (c, I.ConDec (s, m, k, status, v_, l_)) =
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
              (s, m, k, status, worldifyClause (I.Null, v_, w_, P.top), l_)
          with Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg)))
        end
      end

    let rec worldifyBlock (g_, b) = match b with
      | [] -> ()
      | (I.Dec (_, v_) as d_) :: l_ ->
          let a = I.targetFam v_ in
          let w'_ = W.getWorlds a in
          checkClause w'_ (g_, worldifyClause (I.Null, v_, w'_, P.top), P.top);
          worldifyBlock (decUName g_ d_, l_)

    let rec worldifyBlocks = function
      | [] -> ()
      | b :: bs_ -> (
          ignore (worldifyBlocks bs_);
          let gsome_, lblock_ = I.constBlock b in
          ignore (print "|");
          try worldifyBlock (gsome_, lblock_)
          with Error' (occ, s) ->
            raise
              (Error (wrapMsgBlock (b, occ, "World not hereditarily closed"))))

    let worldifyWorld (T.Worlds bs_) = worldifyBlocks bs_

    let worldify a =
      let w_ = W.getWorlds a in
      ignore (print "[?");
      let w'_ = worldifyWorld w_ in
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
                try worldifyConDec w_ (c, I.sgnLookup c)
                with Error' (occ, s) -> raise (Error (wrapMsg (c, occ, s)))))
          (Index.lookup a)
      in
      ignore (map
          (function
            | condec_ -> begin
                print "#";
                checkConDec w_ condec_
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
    | g_, v_ -> worldifyGoal (g_, v_, W.getWorlds (I.targetFam v_), P.top)
end
(*! sharing Origins.Paths = Paths !*)
(*! sharing Origins.IntSyn = IntSyn !*)
(* functor Worldify *)

(* # 1 "src/worldcheck/Worldify.sml.ml" *)
