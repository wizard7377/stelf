open! Basis;;
(* World Checking *);;
(* Author: Carsten Schuermann *);;
(* Modified: Frank Pfenning *);;
module WorldSyn(WorldSyn__0: sig
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
                             (*! structure CSManager : CS_MANAGER !*)
                             (*! sharing CSManager.IntSyn = IntSyn !*)
                             module Subordinate : SUBORDINATE
                             (*! sharing Subordinate.IntSyn = IntSyn !*)
                             module Print : PRINT
                             (*! sharing Print.IntSyn = IntSyn !*)
                             module Table : TABLE
                             (*! structure Paths : PATHS !*)
                             module Origins : ORIGINS
                             (*! sharing Origins.Paths = Paths !*)
                             (*! sharing Origins.IntSyn = IntSyn !*)
                             module Timers : TIMERS
                             end) : WORLDSYN
  =
  struct
    module I = IntSyn;;
    module T = Tomega;;
    module P = Paths;;
    module F = Print.Formatter;;
    exception Error of string ;;
    exception Error' of P.occ * string ;;
    (* copied from terminates/reduces.fun *);;
    let rec wrapMsg (c, occ, msg) =
      begin
      match Origins.originLookup c
      with 
           | (fileName, None) -> (fileName ^ ":") ^ msg
           | (fileName, Some occDec)
               -> P.wrapLoc'
                  ((P.Loc (fileName, P.occToRegionDec occDec occ)),
                   Origins.linesInfoLookup fileName,
                   (("While checking constant " ^
                       (Names.qidToString (Names.constQid c)))
                      ^ ":\n")
                     ^ msg)
      end;;
    type nonrec dlist = IntSyn.dec_ list;;
    open!
      struct
        let worldsTable : T.worlds_ Table.table_ = Table.new_ 0;;
        let rec reset () = Table.clear worldsTable;;
        let rec insert (cid, w_) = Table.insert worldsTable (cid, w_);;
        let rec getWorlds b =
          begin
          match Table.lookup worldsTable b
          with 
               | None
                   -> raise
                      ((Error
                        (("Family " ^ (Names.qidToString (Names.constQid b)))
                           ^ " has no worlds declaration")))
               | Some wb_ -> wb_
          end;;
        let subsumedTable : unit Table.table_ = Table.new_ 0;;
        let rec subsumedReset () = Table.clear subsumedTable;;
        let rec subsumedInsert cid = Table.insert subsumedTable (cid, ());;
        let rec subsumedLookup cid =
          begin
          match Table.lookup subsumedTable cid
          with 
               | None -> false
               | Some _ -> true
          end;;
        type reg_ =
          | Block of I.dctx * dlist 
          | Seq of dlist * I.sub_ 
          | Star of reg_ 
          | Plus of reg_ * reg_ 
          | One ;;
        exception Success ;;
        let rec formatReg r =
          begin
          match r
          with 
               | Block (g_, dl) -> Print.formatDecList (g_, dl)
               | Seq (dl, s) -> Print.formatDecList' (I.null_, (dl, s))
               | Star r
                   -> (F.Hbox [(F.String "("); formatReg r; (F.String ")*")])
               | Plus (r1, r2)
                   -> (F.HVbox
                       [(F.String "("); formatReg r1; (F.String ")");
                        F.break_; (F.String "|"); F.space_; (F.String "(");
                        formatReg r2; (F.String ")")])
               | One -> (F.String "1")
          end;;
        let rec formatSubsump msg (g_, dl, rb_, b) =
          (F.HVbox
           [(F.String msg); F.space_; (F.String "for family"); F.space_;
            (F.String ((Names.qidToString (Names.constQid b)) ^ ":"));
            F.break_; Print.formatDecList (g_, dl); F.break_;
            (F.String "</:"); F.space_; formatReg rb_]);;
        let rec createEVarSub =
          function 
                   | (g_, null_) -> (I.Shift (I.ctxLength g_))
                   | (g_, I.Decl (g'_, (I.Dec (_, v_) as d_)))
                       -> let s = createEVarSub (g_, g'_)
                            in let v'_ = (I.EClo (v_, s))
                                 in let x_ = I.newEVar (g_, v'_)
                                      in (I.Dot ((I.Exp x_), s));;
        let rec collectConstraints =
          function 
                   | [] -> []
                   | (I.EVar (_, _, _, { contents = []}) :: xs_)
                       -> collectConstraints xs_
                   | (I.EVar (_, _, _, { contents = constrs}) :: xs_)
                       -> (Constraints.simplify constrs) @
                            (collectConstraints xs_);;
        let rec collectEVars =
          function 
                   | (g_, I.Dot (I.Exp x_, s), xs_)
                       -> collectEVars
                          (g_, s,
                           Abstract.collectEVars (g_, (x_, I.id), xs_))
                   | (g_, I.Shift _, xs_) -> xs_;;
        let rec noConstraints (g_, s) =
          begin
          match collectConstraints (collectEVars (g_, s, []))
          with 
               | [] -> true
               | _ -> false
          end;;
        let rec formatD (g_, d_) =
          (F.Hbox [(F.String "{"); Print.formatDec (g_, d_); (F.String "}")]);;
        let rec formatDList =
          function 
                   | (g_, [], t) -> []
                   | (g_, (d_ :: []), t)
                       -> let d'_ = I.decSub (d_, t) in [formatD (g_, d'_)]
                   | (g_, (d_ :: l_), t)
                       -> let d'_ = I.decSub (d_, t)
                            in (formatD (g_, d'_) :: F.break_
                                :: formatDList
                                   ((I.Decl (g_, d'_)), l_, I.dot1 t));;
        let rec wGoalToString ((g_, l_), Seq (piDecs, t)) =
          F.makestring_fmt
          ((F.HVbox
            [(F.HVbox (formatDList (g_, l_, I.id))); F.break_;
             (F.String "<|"); F.break_;
             (F.HVbox (formatDList (g_, piDecs, t)))]));;
        let rec worldToString (g_, Seq (piDecs, t)) =
          F.makestring_fmt ((F.HVbox (formatDList (g_, piDecs, t))));;
        let rec hypsToString (g_, l_) =
          F.makestring_fmt ((F.HVbox (formatDList (g_, l_, I.id))));;
        let rec mismatchToString (g_, (v1_, s1), (v2_, s2)) =
          F.makestring_fmt
          ((F.HVbox
            [Print.formatExp (g_, (I.EClo (v1_, s1))); F.break_;
             (F.String "<>"); F.break_;
             Print.formatExp (g_, (I.EClo (v2_, s2)))]));;
        module Trace : sig
                       val clause : I.cid -> unit
                       val constraintsRemain : unit -> unit
                       val matchBlock : ((I.dctx * dlist) * reg_) -> unit
                       val unmatched : (I.dctx * dlist) -> unit
                       val missing : (I.dctx * reg_) -> unit
                       val mismatch : (I.dctx * I.eclo * I.eclo) -> unit
                       val success : unit -> unit
                       end
          =
          struct
            let rec clause c =
              print
              (("World checking clause " ^
                  (Names.qidToString (Names.constQid c)))
                 ^ "\n");;
            let rec constraintsRemain () = begin
              if (! Global.chatter) > 7 then
              print
              "Constraints remain after matching hypotheses against context block\n"
              else () end;;
            let rec matchBlock (gl_, r_) = begin
              if (! Global.chatter) > 7 then
              print (("Matching:\n" ^ (wGoalToString (gl_, r_))) ^ "\n") else
              () end;;
            let rec unmatched gl_ = begin
              if (! Global.chatter) > 7 then
              print (("Unmatched hypotheses:\n" ^ (hypsToString gl_)) ^ "\n")
              else () end;;
            let rec missing (g_, r_) = begin
              if (! Global.chatter) > 7 then
              print
              (("Missing hypotheses:\n" ^ (worldToString (g_, r_))) ^ "\n")
              else () end;;
            let rec mismatch (g_, vs1_, vs2_) = begin
              if (! Global.chatter) > 7 then
              print
              (("Mismatch:\n" ^ (mismatchToString (g_, vs1_, vs2_))) ^ "\n")
              else () end;;
            let rec success () = begin
              if (! Global.chatter) > 7 then print "Success\n" else () end;;
            end;;
        let rec decUName (g_, d_) = (I.Decl (g_, Names.decUName (g_, d_)));;
        let rec decEName (g_, d_) = (I.Decl (g_, Names.decEName (g_, d_)));;
        let rec subGoalToDList =
          function 
                   | I.Pi ((d_, _), v_) -> (d_ :: subGoalToDList v_)
                   | I.Root _ -> [];;
        let rec worldsToReg =
          function 
                   | T.Worlds [] -> One
                   | T.Worlds cids -> (Star (worldsToReg' cids))
        and worldsToReg' =
          function 
                   | (cid :: []) -> (Block (I.constBlock cid))
                   | (cid :: cids)
                       -> (Plus
                           ((Block (I.constBlock cid)), worldsToReg' cids));;
        let rec init arg__1 arg__2 =
          begin
          match (arg__1, arg__2)
          with 
               | (b, (_, [])) -> begin
                                   Trace.success ();raise Success
                                   end
               | (b, (g_, (((I.Dec (_, v1_) as d1_) :: l2_) as l_))) -> begin
                   if Subordinate.belowEq (I.targetFam v1_, b) then
                   begin
                     Trace.unmatched (g_, l_);()
                     end
                   else init b (decUName (g_, d1_), l2_) end
          end;;
        let rec accR =
          function 
                   | (gl_, One, b, k) -> k gl_
                   | (((g_, l_) as gl_), Block (someDecs, piDecs), b, k)
                       -> let t = createEVarSub (g_, someDecs)
                            in let _ =
                                 Trace.matchBlock (gl_, (Seq (piDecs, t)))
                                 in let k' =
                                      function 
                                               | gl'_ -> begin
                                                   if noConstraints (g_, t)
                                                   then k gl'_ else
                                                   begin
                                                     Trace.constraintsRemain
                                                     ();()
                                                     end
                                                   end
                                      in accR (gl_, (Seq (piDecs, t)), b, k')
                   | ((g_, (((I.Dec (_, v1_) as d_) :: l2_) as l_)),
                      (Seq (((I.Dec (_, v1'_) :: l2'_) as b'_), t) as l'_),
                      b, k) -> begin
                       if Unify.unifiable (g_, (v1_, I.id), (v1'_, t)) then
                       accR
                       ((decUName (g_, d_), l2_), (Seq (l2'_, I.dot1 t)), b,
                        k)
                       else begin
                       if Subordinate.belowEq (I.targetFam v1_, b) then
                       begin
                         Trace.mismatch (g_, (v1_, I.id), (v1'_, t));()
                         end
                       else
                       accR
                       ((decUName (g_, d_), l2_),
                        (Seq (b'_, I.comp (t, I.shift))), b, k)
                       end end
                   | (gl_, Seq ([], t), b, k) -> k gl_
                   | (((g_, []) as gl_), (Seq (l'_, t) as r_), b, k)
                       -> begin
                            Trace.missing (g_, r_);()
                            end
                   | (gl_, Plus (r1, r2), b, k)
                       -> begin
                            CSManager.trail
                            (function 
                                      | () -> accR (gl_, r1, b, k));
                            accR (gl_, r2, b, k)
                            end
                   | (gl_, Star One, b, k) -> k gl_
                   | (gl_, (Star r' as r), b, k)
                       -> begin
                            CSManager.trail (function 
                                                      | () -> k gl_);
                            accR
                            (gl_, r', b,
                             function 
                                      | gl'_ -> accR (gl'_, r, b, k))
                            
                            end;;
        let rec checkSubsumedBlock (g_, l'_, rb_, b) =
          try begin
                accR ((g_, l'_), rb_, b, init b);
                raise
                ((Error
                  (F.makestring_fmt
                   (formatSubsump
                    "World subsumption failure"
                    (g_, l'_, rb_, b)))))
                
                end
          with 
               | Success -> ();;
        let rec checkSubsumedWorlds =
          function 
                   | ([], rb_, b) -> ()
                   | ((cid :: cids), rb_, b)
                       -> let (someDecs, piDecs) = I.constBlock cid
                            in begin
                                 checkSubsumedBlock
                                 (Names.ctxName someDecs, piDecs, rb_, b);
                                 checkSubsumedWorlds (cids, rb_, b)
                                 end;;
        let rec checkBlocks (T.Worlds cids) (g_, v_, occ) =
          try let b = I.targetFam v_
                in let wb_ =
                     try getWorlds b
                     with 
                          | Error msg -> raise ((Error' (occ, msg)))
                     in let rb_ = worldsToReg wb_
                          in let _ = begin
                               if subsumedLookup b then () else
                               try begin
                                     checkSubsumedWorlds (cids, rb_, b);
                                     subsumedInsert b
                                     end
                               with 
                                    | Error msg
                                        -> raise ((Error' (occ, msg)))
                               end
                               in let l_ = subGoalToDList v_
                                    in begin
                                         accR ((g_, l_), rb_, b, init b);
                                         raise
                                         ((Error'
                                           (occ,
                                            F.makestring_fmt
                                            (formatSubsump
                                             "World violation"
                                             (g_, l_, rb_, b)))))
                                         
                                         end
          with 
               | Success -> ();;
        let rec checkClause =
          function 
                   | (g_, I.Root (a, s_), w_, occ) -> ()
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), w_,
                      occ)
                       -> begin
                            checkClause
                            (decEName (g_, d_), v2_, w_, P.body occ);
                            checkGoal (g_, v1_, w_, P.label occ)
                            end
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), w_, occ)
                       -> begin
                            checkBlocks w_ (g_, v1_, P.label occ);
                            begin
                              checkClause
                              (decEName (g_, d_), v2_, w_, P.body occ);
                              checkGoal (g_, v1_, w_, P.label occ)
                              end
                            
                            end
        and checkGoal =
          function 
                   | (g_, I.Root (a, s_), w_, occ) -> ()
                   | (g_, I.Pi (((I.Dec (_, v1_) as d_), _), v2_), w_, occ)
                       -> begin
                            checkGoal
                            (decUName (g_, d_), v2_, w_, P.body occ);
                            checkClause (g_, v1_, w_, P.label occ)
                            end;;
        let rec worldcheck w_ a =
          let _ = begin
            if (! Global.chatter) > 3 then
            print
            (("World checking family " ^
                (Names.qidToString (Names.constQid a)))
               ^ ":\n")
            else () end
            in let _ = subsumedReset ()
                 in let rec checkAll =
                      function 
                               | [] -> ()
                               | (I.Const c :: clist)
                                   -> begin
                                        begin
                                        if (! Global.chatter) = 4 then
                                        print
                                        ((Names.qidToString
                                          (Names.constQid c)) ^ " ")
                                        else () end;
                                        begin
                                          begin
                                          if (! Global.chatter) > 4 then
                                          Trace.clause c else () end;
                                          begin
                                            try checkClause
                                                (I.null_, I.constType c, w_,
                                                 P.top)
                                            with 
                                                 | Error' (occ, msg)
                                                     -> raise
                                                        ((Error
                                                          (wrapMsg
                                                           (c, occ, msg))));
                                            checkAll clist
                                            end
                                          
                                          end
                                        
                                        end
                               | (I.Def d :: clist)
                                   -> begin
                                        begin
                                        if (! Global.chatter) = 4 then
                                        print
                                        ((Names.qidToString
                                          (Names.constQid d)) ^ " ")
                                        else () end;
                                        begin
                                          begin
                                          if (! Global.chatter) > 4 then
                                          Trace.clause d else () end;
                                          begin
                                            try checkClause
                                                (I.null_, I.constType d, w_,
                                                 P.top)
                                            with 
                                                 | Error' (occ, msg)
                                                     -> raise
                                                        ((Error
                                                          (wrapMsg
                                                           (d, occ, msg))));
                                            checkAll clist
                                            end
                                          
                                          end
                                        
                                        end
                      in let _ = checkAll (Index.lookup a)
                           in let _ = begin
                                if (! Global.chatter) = 4 then print "\n"
                                else () end in ();;
        let rec ctxAppend =
          function 
                   | (g_, null_) -> g_
                   | (g_, I.Decl (g'_, d_))
                       -> (I.Decl (ctxAppend (g_, g'_), d_));;
        let rec checkSubordBlock (g_, g'_, l_) =
          checkSubordBlock' (ctxAppend (g_, g'_), l_)
        and checkSubordBlock' =
          function 
                   | (g_, ((I.Dec (_, v_) as d_) :: l'_))
                       -> begin
                            Subordinate.respectsN (g_, v_);
                            checkSubordBlock' ((I.Decl (g_, d_)), l'_)
                            end
                   | (g_, []) -> ();;
        let rec conDecBlock =
          function 
                   | I.BlockDec (_, _, gsome_, lpi_) -> (gsome_, lpi_)
                   | Condec_
                       -> raise
                          ((Error
                            (("Identifier " ^ (I.conDecName Condec_)) ^
                               " is not a block label")));;
        let rec constBlock cid = conDecBlock (I.sgnLookup cid);;
        let rec checkSubordWorlds =
          function 
                   | [] -> ()
                   | (cid :: cids)
                       -> let (someDecs, piDecs) = constBlock cid
                            in begin
                                 checkSubordBlock (I.null_, someDecs, piDecs);
                                 checkSubordWorlds cids
                                 end;;
        let rec install (a, (T.Worlds cids as w_)) =
          begin
            try checkSubordWorlds cids
            with 
                 | Subordinate.Error msg -> raise ((Error msg));
            insert (a, w_)
            end;;
        let rec uninstall a =
          begin
          match Table.lookup worldsTable a
          with 
               | None -> false
               | Some _ -> begin
                             Table.delete worldsTable a;true
                             end
          end;;
        let rec lookup a = getWorlds a;;
        let rec ctxToList gin_ =
          let rec ctxToList' =
            function 
                     | (null_, g_) -> g_
                     | (I.Decl (g_, d_), g'_) -> ctxToList' (g_, (d_ :: g'_))
            in ctxToList' (gin_, []);;
        let rec isSubsumed (T.Worlds cids) b =
          let wb_ = getWorlds b
            in let rb_ = worldsToReg wb_ in begin
                 if subsumedLookup b then () else
                 begin
                   checkSubsumedWorlds (cids, rb_, b);subsumedInsert b
                   end
                 end;;
        end;;
    (* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *);;
    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *);;
    (* Regular world expressions  *);;
    (* R ::= LD                   *);;
    (*     | (D1,...,Dn)[s]       *);;
    (*     | R*                   *);;
    (*     | R1 + R2              *);;
    (*     | 1                    *);;
    (* signals worldcheck success *);;
    (* Format a regular world *);;
    (* Is this correct? - gaw *);;
    (* Fixed June 3, 2009 -fp,cs *);;
    (* Format a subsumption failure judgment
       msg: Prefix for the message
       dl : declaration list
       Rb : regular world
       b : family
       Displays:

         msg for family b:
         G |- dl </: Rb
     *);;
    (*
            F.HVbox ([F.String ((Names.qidToString (Names.constQid b)) ^ "":"")])
        *);;
    (* F.Newline (), *);;
    (* Do not print some-variables; reenable if necessary *);;
    (* June 3, 2009 -fp,cs *);;
    (* Print.formatCtx(I.Null, G), F.Break, F.String ""|-"", F.Space, *);;
    (* createEVarSub G G' = s

       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *);;
    (* from cover.fun *);;
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are ""hard""
    *);;
    (* constrs <> nil *);;
    (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *);;
    (* other cases impossible by invariants since s is EVarSubst *);;
    (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *);;
    (* end from cover.fun *);;
    (************);;
    (* Printing *);;
    (************);;
    (* Declarations *);;
    (* Declaration lists *);;
    (* Names.decUName (G, I.decSub(D, t)) *);;
    (* Names.decUName (G, I.decSub (D, t)) *);;
    (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *);;
    (* Hypotheses and declaration lists *);;
    (* Declaration list *);;
    (* Hypotheses *);;
    (* Mismatch between hypothesis and world declaration *);;
    (***********);;
    (* Tracing *);;
    (***********);;
    (* R = (D1,...,Dn)[t] *);;
    (* R = (D1,...,Dn)[t] *);;
    (**************************************);;
    (* Matching hypotheses against worlds *);;
    (**************************************);;
    (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression
       with non-empty contextblocks as leaves
    *);;
    (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *);;
    (* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *);;
    (* G |- t : someDecs *);;
    (* if block matches, check for remaining constraints *);;
    (* relevant to family b, fail *);;
    (* not relevant to family b, skip in L *);;
    (* fixed bug in previous line; was: t instead of t o ^ *);;
    (* Mon May 7 2007 -fp *);;
    (* L is missing *);;
    (* only possibility for non-termination in next rule *);;
    (* r' does not accept empty declaration list *);;
    (* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *);;
    (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *);;
    (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *);;
    (******************************);;
    (* Checking clauses and goals *);;
    (******************************);;
    (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *);;
    (* checkGoal (G, V, W, occ) = ()
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

        Invariant: G |- V : type, V nf
     *);;
    (* Question: should dependent Pi's really be checked recursively? *);;
    (* Thu Mar 29 09:38:20 2001 -fp *);;
    (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *);;
    (* initialize table of subsumed families *);;
    (**************************);;
    (* Checking Subordination *);;
    (**************************);;
    (*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *);;
    (* checkSubordBlock (G, G', L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME G'. PI L'
       Invariants: G |- SOME G'. PI L' block
    *);;
    (* is V nf?  Assume here: yes! *);;
    (* conDecBlock (condec) = (Gsome, Lpi)
       if condec is a block declaration
       raise Error (msg) otherwise
    *);;
    (* constBlock cid = (someDecs, piDecs)
       if cid is defined as a context block
       Effect: raise Error (msg) otherwise
    *);;
    (* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *);;
    (* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W does not respect subordination
    *);;
    (* lookup (a) = SOME W if worlds declared for a, NONE otherwise *);;
    (* ctxToList G = L

       Invariant:
       G = L  (G is left associative, L is right associative)
    *);;
    (* isSubsumed (W, b) = ()
       holds if the worlds associated with b are subsumed by W
       Effect: raises Error'(occ, msg) otherwise

       Invariants: G |- V : type, V nf
    *);;
    let reset = reset;;
    let install = install;;
    let lookup = lookup;;
    let uninstall = uninstall;;
    let worldcheck = worldcheck;;
    let ctxToList = ctxToList;;
    let isSubsumed = isSubsumed;;
    let getWorlds = getWorlds;;
    end;;
(* functor WorldSyn *);;