open! Global.Global_
open! Timing
open! Table
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print.Print_
open! Index.Index_
open! Subordinate
open! Solvers.Solvers_

(* # 1 "src/worldcheck/WorldSyn.sig.ml" *)

(* World Checking *)
(* Author: Carsten Schuermann *)
include WORLDSYN
(* signature WORLDSYN *)

(* # 1 "src/worldcheck/WorldSyn.fun.ml" *)
open! Basis
open Origins
open Timers
open Table_

(* World Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception Error' of Paths.occ * string

let () =
  Printexc.register_printer (function Error' (_, msg) -> Some msg | _ -> None)

module WorldSyn (WorldSyn__0 : sig
  module Global : GLOBAL
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
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Table : TABLE with type key = int

  (*! structure Paths : PATHS !*)
  module Origins : ORIGINS.ORIGINS

  (*! sharing Origins.Paths = Paths !*)
  (*! sharing Origins.IntSyn = IntSyn !*)
  module Timers : TIMERS.TIMERS
end) : WORLDSYN = struct
  module Origins = WorldSyn__0.Origins
  module Subordinate = WorldSyn__0.Subordinate
  module I = IntSyn
  module T = Tomega
  module P = Paths
  module F = Print.Formatter
  module Table = WorldSyn__0.Table
  module Unify = WorldSyn__0.Unify

  exception Error = Error
  exception Error' = Error'

  (* copied from terminates/Reduces.fun *)
  let wrapMsg (c, occ, msg) =
    begin match Origins.originLookup c with
    | fileName, None -> (fileName ^ ":") ^ msg
    | fileName, Some occDec ->
        P.wrapLoc'
          (P.Loc (fileName, P.occToRegionDec occDec occ)) (Origins.linesInfoLookup fileName) ((("While checking constant " ^ Names.qidToString (Names.constQid c))
            ^ ":\n")
            ^ msg)
    end

  type nonrec dlist = IntSyn.dec list

  open! struct
    let worldsTable : T.worlds Table.table = Table.new_ 0
    let reset () = Table.clear worldsTable
    let insert cid w = Table.insert worldsTable (cid, w)

    let getWorlds b =
      begin match Table.lookup worldsTable b with
      | None ->
          raise
            (Error
               (("Family " ^ Names.qidToString (Names.constQid b))
               ^ " has no worlds declaration"))
      | Some wb -> wb
      end

    let subsumedTable : unit Table.table = Table.new_ 0
    let subsumedReset () = Table.clear subsumedTable
    let subsumedInsert cid = Table.insert subsumedTable (cid, ())

    let subsumedLookup cid =
      begin match Table.lookup subsumedTable cid with
      | None -> false
      | Some _ -> true
      end

    type reg =
      | Block of (I.dctx * dlist)
      | Seq of dlist * I.sub
      | Star of reg
      | Plus of reg * reg
      | One

    exception Success

    let rec formatReg r =
      begin match r with
      | Block (g, dl) -> Print.formatDecList g dl
      | Seq (dl, s) -> Print.formatDecList' I.Null (dl, s)
      | Star r -> F.hbox [ F.string "("; formatReg r; F.string ")*" ]
      | Plus (r1, r2) ->
          F.hVbox
            [
              F.string "(";
              formatReg r1;
              F.string ")";
              F.break_;
              F.string "|";
              F.space;
              F.string "(";
              formatReg r2;
              F.string ")";
            ]
      | One -> F.string "1"
      end

    let formatSubsump msg (g, dl, rb, b) =
      F.hVbox
        [
          F.string msg;
          F.space;
          F.string "for family";
          F.space;
          F.string (Names.qidToString (Names.constQid b) ^ ":");
          F.break_;
          Print.formatDecList g dl;
          F.break_;
          F.string "</:";
          F.space;
          formatReg rb;
        ]

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

    let rec collectEVars a2 b2 c2 = match a2, b2, c2 with
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

    let wGoalToString ((g, l), Seq (piDecs, t)) =
      F.makestring_fmt
        (F.hVbox
           [
             F.hVbox (formatDList (g, l, I.id));
             F.break_;
             F.string "<|";
             F.break_;
             F.hVbox (formatDList (g, piDecs, t));
           ])

    let worldToString (g, Seq (piDecs, t)) =
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

    let rec subGoalToDList = function
      | I.Pi ((d, _), v) -> d :: subGoalToDList v
      | I.Root _ -> []

    let rec worldsToReg = function
      | T.Worlds [] -> One
      | T.Worlds cids -> Star (worldsToReg' cids)

    and worldsToReg' = function
      | cid :: [] -> Block (I.constBlock cid)
      | cid :: cids -> Plus (Block (I.constBlock cid), worldsToReg' cids)

    let rec init arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | b, (_, []) -> begin
          Trace.success ();
          raise Success
        end
      | b, (g, ((I.Dec (_, v1) as d1) :: l2 as l)) ->
          begin if Subordinate.belowEq (I.targetFam v1) b then begin
            Trace.unmatched g l;
            ()
          end
          else init b (decUName g d1, l2)
          end
      end

    let rec accR (a, c, b, k) = match a, c with
      | gl, One -> k gl
      | ((g, l) as gl), Block (someDecs, piDecs) ->
          let t = createEVarSub (g, someDecs) in
          ignore (Trace.matchBlock (gl, Seq (piDecs, t)));
          let k' = function
            | gl' ->
                begin if noConstraints (g, t) then k gl'
                else begin
                  Trace.constraintsRemain ();
                  ()
                end
                end
          in
          accR (gl, Seq (piDecs, t), b, k')
      | (g, ((I.Dec (_, v1) as d) :: l2 as l)), (Seq ((I.Dec (_, v1') :: l2' as b'), t) as l') ->
          begin if Unify.unifiable g (v1, I.id) (v1', t) then
            accR ((decUName g d, l2), Seq (l2', I.dot1 t), b, k)
          else
            begin if Subordinate.belowEq (I.targetFam v1) b then begin
              Trace.mismatch g (v1, I.id) (v1', t);
              ()
            end
            else
              accR
                ((decUName g d, l2), Seq (b', I.comp t I.shift), b, k)
            end
          end
      | gl, Seq ([], t) -> k gl
      | ((g, []) as gl), (Seq (l', t) as r) -> begin
          Trace.missing g r;
          ()
        end
      | gl, Plus (r1, r2) -> begin
          CsManager.trail (function () -> accR (gl, r1, b, k));
          accR (gl, r2, b, k)
        end
      | gl, Star One -> k gl
      | gl, (Star r' as r) -> begin
          CsManager.trail (function () -> k gl);
          accR (gl, r', b, function gl' -> accR (gl', r, b, k))
        end

    let checkSubsumedBlock (g, l', rb, b) =
      try
        begin
          accR ((g, l'), rb, b, init b);
          raise
            (Error
               (F.makestring_fmt
                  (formatSubsump "World subsumption failure" (g, l', rb, b))))
        end
      with Success -> ()

    let rec checkSubsumedWorlds (a, rb, b) = match a with
      | [] -> ()
      | cid :: cids ->
          let someDecs, piDecs = I.constBlock cid in
          checkSubsumedBlock (Names.ctxName someDecs, piDecs, rb, b);
          checkSubsumedWorlds (cids, rb, b)

    let checkBlocks (T.Worlds cids) (g, v, occ) =
      try
        let b = I.targetFam v in
        let wb =
          try getWorlds b with Error msg -> raise (Error' (occ, msg))
        in
        let rb = worldsToReg wb in
        ignore begin if subsumedLookup b then ()
          else
            try
              begin
                checkSubsumedWorlds (cids, rb, b);
                subsumedInsert b
              end
            with Error msg -> raise (Error' (occ, msg))
          end;
        let l = subGoalToDList v in
        accR ((g, l), rb, b, init b);
        raise
          (Error'
             ( occ,
               F.makestring_fmt
                 (formatSubsump "World violation" (g, l, rb, b)) ))
      with Success -> ()

    let rec checkClause (g, b, w, occ) = match b with
      | I.Root (a, s) -> ()
      | I.Pi (((I.Dec (_, v1) as d), Maybe), v2) -> begin
          checkClause (decEName g d, v2, w, P.body occ);
          checkGoal (g, v1, w, P.label occ)
        end
      | I.Pi (((I.Dec (_, v1) as d), No), v2) -> begin
          checkBlocks w (g, v1, P.label occ);
          begin
            checkClause (decEName g d, v2, w, P.body occ);
            checkGoal (g, v1, w, P.label occ)
          end
        end

    and checkGoal (g, b, w, occ) = match b with
      | I.Root (a, s) -> ()
      | I.Pi (((I.Dec (_, v1) as d), _), v2) -> begin
          checkGoal (decUName g d, v2, w, P.body occ);
          checkClause (g, v1, w, P.label occ)
        end

    let worldcheck w a =
      ignore begin if !Global.chatter > 3 then
          print
            (("World checking family " ^ Names.qidToString (Names.constQid a))
            ^ ":\n")
        else ()
        end;
      ignore (subsumedReset ());
      let rec checkAll = function
        | [] -> ()
        | I.Const c :: clist ->
            if !Global.chatter = 4 then
              print (Names.qidToString (Names.constQid c) ^ " ")
            else ();
            if !Global.chatter > 4 then Trace.clause c else ();
            (try checkClause (I.Null, I.constType c, w, P.top)
             with Error' (occ, msg) -> raise (Error (wrapMsg (c, occ, msg))));
            checkAll clist
        | I.Def d :: clist ->
            if !Global.chatter = 4 then
              print (Names.qidToString (Names.constQid d) ^ " ")
            else ();
            if !Global.chatter > 4 then Trace.clause d else ();
            (try checkClause (I.Null, I.constType d, w, P.top)
             with Error' (occ, msg) -> raise (Error (wrapMsg (d, occ, msg))));
            checkAll clist
      in
      ignore (checkAll (Index.lookup a));
      ignore begin if !Global.chatter = 4 then print "\n" else ()
        end;
      ()

    let rec ctxAppend (g, a) = match a with
      | I.Null -> g
      | I.Decl (g', d) -> I.Decl (ctxAppend (g, g'), d)

    let rec checkSubordBlock (g, g', l) =
      checkSubordBlock' (ctxAppend (g, g'), l)

    and checkSubordBlock' (g, a) = match a with
      | (I.Dec (_, v) as d) :: l' -> begin
          Subordinate.respectsN g v;
          checkSubordBlock' (I.Decl (g, d), l')
        end
      | [] -> ()

    let conDecBlock = function
      | I.BlockDec (_, _, gsome, lpi) -> (gsome, lpi)
      | condec ->
          raise
            (Error
               (("Identifier " ^ I.conDecName condec) ^ " is not a block label"))

    let constBlock cid = conDecBlock (I.sgnLookup cid)

    let rec checkSubordWorlds = function
      | [] -> ()
      | cid :: cids ->
          let someDecs, piDecs = constBlock cid in
          checkSubordBlock (I.Null, someDecs, piDecs);
          checkSubordWorlds cids

    let install a (T.Worlds cids as w) =
      begin
        (try checkSubordWorlds cids
         with Subordinate.Error msg -> raise (Error msg));
        insert a w
      end

    let uninstall a =
      begin match Table.lookup worldsTable a with
      | None -> false
      | Some _ -> begin
          Table.delete worldsTable a;
          true
        end
      end

    let lookup a = getWorlds a

    let ctxToList gin =
      let rec ctxToList' = function
        | I.Null, g -> g
        | I.Decl (g, d), g' -> ctxToList' (g, d :: g')
      in
      ctxToList' (gin, [])

    let isSubsumed (T.Worlds cids) b =
      let wb = getWorlds b in
      let rb = worldsToReg wb in
      begin if subsumedLookup b then ()
      else begin
        checkSubsumedWorlds (cids, rb, b);
        subsumedInsert b
      end
      end
  end

  (* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *)
  (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
  (* Regular world expressions  *)
  (* R ::= LD                   *)
  (*     | (D1,...,Dn)[s]       *)
  (*     | R*                   *)
  (*     | R1 + R2              *)
  (*     | 1                    *)
  (* signals worldcheck success *)
  (* Format a regular world *)
  (* Is this correct? - gaw *)
  (* Fixed June 3, 2009 -fp,cs *)
  (* Format a subsumption failure judgment
       msg: Prefix for the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for family b:
         G |- dl </: Rb
     *)
  (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ "":"")])
        *)
  (* F.Newline (), *)
  (* Do not print some-variables; reenable if necessary *)
  (* June 3, 2009 -fp,cs *)
  (* Print.formatCtx(I.Null, G), F.Break, F.String ""|-"", F.Space, *)
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
  (* end from Cover.fun *)
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
  (* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
  (* G |- t : someDecs *)
  (* if block matches, check for remaining constraints *)
  (* relevant to family b, fail *)
  (* not relevant to family b, skip in L *)
  (* fixed bug in previous line; was: t instead of t o ^ *)
  (* Mon May 7 2007 -fp *)
  (* L is missing *)
  (* only possibility for non-termination in next rule *)
  (* r' does not accept empty declaration list *)
  (* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
  (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
  (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
  (******************************)
  (* Checking clauses and goals *)
  (******************************)
  (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
  (* checkGoal (G, V, W, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *)
  (* Question: should dependent Pi's really be checked recursively? *)
  (* Thu Mar 29 09:38:20 2001 -fp *)
  (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *)
  (* initialize table of subsumed families *)
  (**************************)
  (* Checking Subordination *)
  (**************************)
  (*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *)
  (* checkSubordBlock (G, G', L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME G'. PI L'
       Invariants: G |- SOME G'. PI L' block
    *)
  (* is V nf?  Assume here: yes! *)
  (* conDecBlock (condec) = (Gsome, Lpi)
       if condec is a block declaration
       raise Error (msg) otherwise
    *)
  (* constBlock cid = (someDecs, piDecs)
       if cid is defined as a context block
       Effect: raise Error (msg) otherwise
    *)
  (* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *)
  (* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W does not respect subordination
    *)
  (* lookup (a) = SOME W if worlds declared for a, NONE otherwise *)
  (* ctxToList G = L

       Invariant:
       G = L  (G is left associative, L is right associative)
    *)
  (* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *)
  let reset = reset
  let install = install
  let lookup = lookup
  let uninstall = uninstall
  let worldcheck = worldcheck
  let ctxToList = ctxToList
  let isSubsumed = isSubsumed
  let getWorlds = getWorlds
end
(* functor WorldSyn *)

(* # 1 "src/worldcheck/WorldSyn.sml.ml" *)
