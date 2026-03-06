open! Basis;;
(* Indexing for table *);;
(* Author: Brigitte Pientka *);;
module TableIndex(TableIndex__0: sig
                                 module Global : GLOBAL
                                 module Queue : QUEUE
                                 (*! structure IntSyn' : INTSYN !*)
                                 (*! structure CompSyn': COMPSYN !*)
                                 (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                                 module Subordinate : SUBORDINATE
                                 (*! sharing Subordinate.IntSyn = IntSyn'                   !*)
                                 module Conv : CONV
                                 (*! sharing Conv.IntSyn = IntSyn' !*)
                                 module Unify : UNIFY
                                 (*! sharing Unify.IntSyn = IntSyn' !*)
                                 module AbstractTabled : ABSTRACTTABLED
                                 (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
                                 module Whnf : WHNF
                                 (*! sharing Whnf.IntSyn = IntSyn' !*)
                                 module Print : PRINT
                                 (*! sharing Print.IntSyn = IntSyn' !*)
                                 module CPrint : CPRINT
                                 (*! sharing CPrint.IntSyn = IntSyn' !*)
                                 (*! sharing CPrint.CompSyn = CompSyn' !*)
                                 module Names : NAMES
                                 (*! sharing Names.IntSyn = IntSyn' !*)
                                 module TypeCheck : TYPECHECK
                                 end) : TABLEINDEX
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure CompSyn = CompSyn' !*);;
    module Conv = Conv;;
    (* TABLE

   table entry : D, G  |- u

   Answer substitution:

                 Dk, G  |- sk : D, G

   Answer :
                 Dk, G |- u[sk]
   *);;
    (* solution: (Dk, sk)

   * lookup  : pointer to the i-th element in solution list
   *);;
    type nonrec __0 = {
      solutions: ((IntSyn.dctx * IntSyn.sub_) * CompSyn.pskeleton) list ;
      lookup: int };;
    type nonrec answer = __0;;
    (* entry = (((i, G, D, U), A)) where i is the access counter
   *);;
    type nonrec entry =
      (int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.exp_) * answer;;
    type nonrec entries = entry list;;
    type nonrec index = entry list;;
    type answState = | New 
                     | Repeated ;;
    type strategy_ = | Variant 
                     | Subsumption ;;
    let added = ref false;;
    (* ---------------------------------------------------------------------- *);;
    (* global search parameters *);;
    let strategy = ref Variant;;
    (* Subsumption *);;
    (* Variant *);;
    (* term abstraction after term depth is greater than 5 *);;
    let termDepth = (ref None : int option ref);;
    let ctxDepth = (ref None : int option ref);;
    let ctxLength = (ref None : int option ref);;
    (*   val termDepth = ref (!globalTermDepth); *);;
    (*   val ctxDepth = ref (!globalCtxDepth);   *);;
    (*   val ctxLength = ref (!globalCtxLength); *);;
    (* apply strengthening during abstraction *);;
    let strengthen = AbstractTabled.strengthen;;
    (* original query *);;
    let Query_
      : (IntSyn.dctx *
         IntSyn.dctx *
         IntSyn.exp_ *
         IntSyn.sub_ *
         (CompSyn.pskeleton -> unit))
      option ref = ref None;;
    (* ---------------------------------------------------------------------- *);;
    open!
      struct
        module I = IntSyn;;
        module C = CompSyn;;
        module A = AbstractTabled;;
        let table : index ref = ref [];;
        let rec concat =
          function 
                   | (null_, g'_) -> g'_
                   | (I.Decl (g_, d_), g'_)
                       -> (I.Decl (concat (g_, g'_), d_));;
        let rec reverse =
          function 
                   | (null_, g'_) -> g'_
                   | (I.Decl (g_, d_), g'_)
                       -> reverse (g_, (I.Decl (g'_, d_)));;
        let rec printTable () =
          let rec proofTerms =
            function 
                     | (g_, d_, u_, []) -> print ""
                     | (g_, d_, u_, (((d'_, s'), _) :: s_))
                         -> begin
                              try print
                                  (Print.expToString
                                   (I.null_,
                                    A.raiseType
                                    (Names.ctxName d'_,
                                     (I.EClo
                                      (A.raiseType (Names.ctxName g_, u_),
                                       s')))))
                              with 
                                   | _ -> print "EXCEPTION";
                              begin
                                print ", \n\t";proofTerms (g_, d_, u_, s_)
                                end
                              
                              end
            in let rec printT =
                 function 
                          | [] -> ()
                          | (((k, g_, d_, u_), { solutions = s_; lookup = i})
                             :: T)
                              -> begin
                                 match s_
                                 with 
                                      | []
                                          -> begin
                                               printT T;
                                               print
                                               ((Print.expToString
                                                 (I.null_,
                                                  A.raiseType
                                                  (concat (g_, d_), u_))) ^
                                                  ", NONE\n")
                                               
                                               end
                                      | (a :: answ)
                                          -> begin
                                               printT T;
                                               begin
                                                 print
                                                 ((Print.expToString
                                                   (I.null_,
                                                    A.raiseType
                                                    (concat (g_, d_), u_))) ^
                                                    ", [\n\t");
                                                 begin
                                                   proofTerms
                                                   (g_, d_, u_, rev s_);
                                                   print
                                                   ((" ] -- lookup : " ^
                                                       (Int.toString i))
                                                      ^ "\n\n")
                                                   
                                                   end
                                                 
                                                 end
                                               
                                               end
                                 end
                 in begin
                      print "Table: \n";
                      begin
                        printT (! table);
                        begin
                          print "End Table \n";
                          print
                          (("Number of table entries   : " ^
                              (Int.toString (length (! table))))
                             ^ "\n")
                          
                          end
                        
                        end
                      
                      end;;
        let rec printTableEntries () =
          let rec printT =
            function 
                     | [] -> ()
                     | (((k, g_, d_, u_), { solutions = s_; lookup = i})
                        :: T)
                         -> begin
                              printT T;
                              print
                              ((((Print.expToString
                                  (I.null_,
                                   A.raiseType (concat (g_, d_), u_))) ^
                                   "\n Access Counter : ")
                                  ^ (Int.toString (! k)))
                                 ^ " \n")
                              
                              end
            in begin
                 print "TableEntries: \n";
                 begin
                   printT (! table);
                   begin
                     print "End TableEntries \n";
                     print
                     (("Number of table entries   : " ^
                         (Int.toString (length (! table))))
                        ^ "\n")
                     
                     end
                   
                   end
                 
                 end;;
        let rec lengthSpine =
          function 
                   | nil_ -> 0
                   | I.SClo (s_, s') -> 1 + (lengthSpine s_);;
        let rec exceedsTermDepth i =
          begin match ! termDepth with 
                                       | None -> false
                                       | Some n -> i > n end;;
        let rec exceedsCtxDepth i =
          begin
          match ! ctxDepth
          with 
               | None -> false
               | Some n
                   -> begin
                        print
                        (((("\n exceedsCtxDepth " ^ (Int.toString i)) ^ " > ")
                            ^ (Int.toString n))
                           ^ " ? ");
                        i > n
                        end
          end;;
        let rec exceedsCtxLength i =
          begin match ! ctxLength with 
                                       | None -> false
                                       | Some n -> i > n end;;
        let rec max (x, y) = begin if x > y then x else y end;;
        let rec oroption =
          function 
                   | (None, None, None) -> false
                   | (Some k, _, _) -> true
                   | (_, Some n, _) -> true
                   | (_, _, Some n) -> true;;
        let rec abstractionSet () =
          oroption (! termDepth, ! ctxDepth, ! ctxLength);;
        let rec exceeds u_ = countDecl (0, 0, u_)
        and countDecl =
          function 
                   | (ctrType, ctrLength, I.Pi ((d_, _), v_))
                       -> let ctrType' = countDec (0, d_) in begin
                            if ctrType' > ctrType then
                            countDecl (ctrType', ctrLength + 1, v_) else
                            countDecl (ctrType, ctrLength + 1, v_) end
                   | (ctrType, ctrLength, u_)
                       -> let ctrTerm = count (0, u_)
                            in (exceedsCtxDepth ctrType) ||
                                 ((exceedsCtxLength ctrLength) ||
                                    (exceedsTermDepth (count (0, u_))))
        and countDec =
          function 
                   | (ctr, I.Dec (_, u_)) -> count (ctr, u_)
                   | (ctr, I.BDec (_, s)) -> 0
        and count =
          function 
                   | (ctr, (I.Uni l_ as u_)) -> ctr
                   | (ctr, I.Pi ((d_, _), v_))
                       -> let ctrTerm = count (ctr, v_)
                            in let ctrType = countDec (ctr, d_)
                                 in max (ctrType, ctrTerm)
                   | (ctr, I.Root (f_, s_))
                       -> let ctrDepth = countSpine (1, s_)
                            in (ctrDepth + 1) + ctr
                   | (ctr, I.Redex (u_, s_))
                       -> let ctrDepth = count (0, u_)
                            in let ctrDepth' = countSpine (ctrDepth, s_)
                                 in (max (ctrDepth', ctrDepth)) + ctr
                   | (ctr, I.Lam (d_, u_)) -> count (ctr + 1, u_)
                   | (ctr, (I.EVar _ as x_)) -> ctr
                   | (ctr, I.EClo (e_, s)) -> count (ctr, e_)
                   | (ctr, (I.FgnExp (cs, ops) as f_)) -> ctr
        and countSpine =
          function 
                   | (ctrDepth, nil_) -> ctrDepth
                   | (ctr, I.SClo (s_, s')) -> countSpine (ctr, s_)
                   | (ctrDepth, I.App (u_, s_))
                       -> let ctrDepth' = count (0, u_)
                            in countSpine (max (ctrDepth', ctrDepth), s_);;
        let rec reinstSub =
          function 
                   | (g_, null_, s) -> s
                   | (g_, I.Decl (d_, I.Dec (_, a_)), s)
                       -> let x_ = I.newEVar (I.null_, a_)
                            in (I.Dot ((I.Exp x_), reinstSub (g_, d_, s)));;
        let rec variant (us_, us'_) = Conv.conv (us_, us'_);;
        let rec subsumes ((g_, d_, u_), (g'_, d'_, u'_)) =
          let upi_ = A.raiseType (g_, u_)
            in let upi'_ = A.raiseType (g'_, u'_)
                 in let s' = reinstSub (g'_, d'_, I.id)
                      in CSManager.trail
                         (function 
                                   | ()
                                       -> Unify.unifiable
                                          (d_, (upi'_, s'), (upi_, I.id)));;
        let rec equalSub =
          function 
                   | (I.Shift k, I.Shift k') -> k = k'
                   | (I.Dot (f_, s_), I.Dot (f'_, s'_))
                       -> (equalFront (f_, f'_)) && (equalSub (s_, s'_))
                   | (I.Dot (f_, s_), I.Shift k) -> false
                   | (I.Shift k, I.Dot (f_, s_)) -> false
        and equalFront =
          function 
                   | (I.Idx n, I.Idx n') -> n = n'
                   | (I.Exp u_, I.Exp v_)
                       -> Conv.conv ((u_, I.id), (v_, I.id))
                   | (undef_, undef_) -> true;;
        let rec equalSub1 (I.Dot (ms, s), I.Dot (ms', s')) = equalSub (s, s');;
        let rec equalCtx =
          function 
                   | (null_, null_) -> true
                   | (I.Decl (dk_, I.Dec (_, a_)), I.Decl
                      (d1_, I.Dec (_, a1_)))
                       -> (Conv.conv ((a_, I.id), (a1_, I.id))) &&
                            (equalCtx (dk_, d1_));;
        let rec callCheckVariant (g_, d_, u_) =
          let upi_ = A.raiseType (concat (g_, d_), u_)
            in let rec lookup =
                 function 
                          | ((g_, d_, u_), [])
                              -> begin
                                   table :=
                                     ((((ref 1, g_, d_, u_),
                                        { solutions = []; lookup = 0} )
                                       :: ! table));
                                   begin
                                     begin
                                     if (! Global.chatter) >= 5 then
                                     begin
                                       print "\n \n Added ";
                                       print
                                       ((Print.expToString (I.null_, upi_)) ^
                                          "\n to Table \n")
                                       
                                       end
                                     else () end;
                                     begin
                                       added := true;begin
                                       if abstractionSet () then begin
                                       if exceeds (A.raiseType (g_, u_)) then
                                       begin
                                         begin
                                         if (! Global.chatter) >= 5 then
                                         print
                                         (("\n term " ^
                                             (Print.expToString
                                              (I.null_, upi_)))
                                            ^ " exceeds depth or length \n")
                                         else () end;(Some [])
                                         end
                                       else None end else None end
                                       end
                                     
                                     end
                                   
                                   end
                          | ((g_, d_, u_),
                             ((((k, g'_, d'_, u'_), answ) as h_) :: T))
                              -> begin
                              if
                              variant
                              ((upi_, I.id),
                               (A.raiseType (concat (g'_, d'_), u'_), I.id))
                              then
                              begin
                                k := ((! k) + 1);
                                begin
                                  begin
                                  if (! Global.chatter) >= 5 then
                                  print
                                  (("call " ^
                                      (Print.expToString (I.null_, upi_)))
                                     ^ " found in table \n ")
                                  else () end;
                                  (Some [((g'_, d'_, u'_), answ)])
                                  end
                                
                                end
                              else lookup ((g_, d_, u_), T) end
                 in lookup ((g_, d_, u_), ! table);;
        let rec callCheckSubsumes (g_, d_, u_) =
          let rec lookup =
            function 
                     | ((g_, d_, u_), [])
                         -> begin
                              table :=
                                ((((ref 1, g_, d_, u_),
                                   { solutions = []; lookup = 0} )
                                  :: ! table));
                              begin
                                begin
                                if (! Global.chatter) >= 5 then
                                print
                                (("Added " ^
                                    (Print.expToString
                                     (I.null_,
                                      A.raiseType (concat (g_, d_), u_))))
                                   ^ " to Table \n")
                                else () end;
                                begin
                                  added := true;begin
                                  if exceeds (A.raiseType (g_, u_)) then
                                  begin
                                    begin
                                    if (! Global.chatter) >= 4 then
                                    print
                                    (("\n term " ^
                                        (Print.expToString
                                         (I.null_,
                                          A.raiseType (concat (g_, d_), u_))))
                                       ^ " exceeds depth or length \n")
                                    else () end;(Some [])
                                    end
                                  else None end
                                  end
                                
                                end
                              
                              end
                     | ((g_, d_, u_), (((k, g'_, d'_, u'_), answ) :: T))
                         -> begin
                         if subsumes ((g_, d_, u_), (g'_, d'_, u'_)) then
                         begin
                           begin
                           if (! Global.chatter) >= 5 then
                           print
                           (("call " ^
                               (Print.expToString
                                (I.null_, A.raiseType (concat (g_, d_), u_))))
                              ^ "found in table \n ")
                           else () end;
                           begin
                             k := ((! k) + 1);
                             (Some [((g'_, d'_, u'_), answ)])
                             end
                           
                           end
                         else lookup ((g_, d_, u_), T) end
            in lookup ((g_, d_, u_), ! table);;
        let rec member =
          function 
                   | ((dk_, sk), []) -> false
                   | ((dk_, sk), (((d1_, s1), _) :: s_)) -> begin
                       if (equalSub (sk, s1)) && (equalCtx (dk_, d1_)) then
                       true else member ((dk_, sk), s_) end;;
        let rec answCheckVariant (g_, d_, u_, s, o_) =
          let upi_ = A.raiseType (concat (g_, d_), u_)
            in let _ = begin
                 if (! Global.chatter) >= 5 then
                 begin
                   print "\n AnswCheckInsert: ";
                   begin
                     print
                     ((Print.expToString
                       (I.null_, (I.EClo (A.raiseType (g_, u_), s)))) ^ "\n");
                     begin
                       print "\n Table Index : ";
                       print ((Print.expToString (I.null_, upi_)) ^ "\n")
                       end
                     
                     end
                   
                   end
                 else () end
                 in let rec lookup arg__1 arg__2 arg__3 =
                      begin
                      match (arg__1, arg__2, arg__3)
                      with 
                           | ((g_, d_, u_, s), [], T)
                               -> begin
                                    print
                                    ((Print.expToString
                                      (I.null_,
                                       (I.EClo (A.raiseType (g_, u_), s)))) ^
                                       " call should always be already in the table !\n");
                                    Repeated
                                    end
                           | ((g_, d_, u_, s),
                              ((((k, g'_, d'_, u'_),
                                 { solutions = s_; lookup = i}) as h_)
                               :: T),
                              t'_) -> begin
                               if
                               variant
                               ((upi_, I.id),
                                (A.raiseType (concat (g'_, d'_), u'_), I.id))
                               then
                               let (dk_, sk) = A.abstractAnswSub s in begin
                                 if member ((dk_, sk), s_) then Repeated else
                                 begin
                                   table :=
                                     ((rev t'_) @
                                        ((((k, g'_, d'_, u'_),
                                           {
                                           solutions
                                           = (((dk_, sk), o_) :: s_);
                                           lookup = i}
                                           )
                                          :: T)));
                                   begin
                                     begin
                                     if (! Global.chatter) >= 5 then
                                     begin
                                       print "\n Add solution  -- ";
                                       begin
                                         print
                                         (Print.expToString
                                          (I.null_,
                                           (I.EClo
                                            (A.raiseType (g'_, u'_), s))));
                                         begin
                                           print "\n solution added  -- ";
                                           print
                                           (Print.expToString
                                            (I.null_,
                                             A.raiseType
                                             (Names.ctxName dk_,
                                              (I.EClo
                                               (A.raiseType (g'_, u'_), sk)))))
                                           
                                           end
                                         
                                         end
                                       
                                       end
                                     else () end;New
                                     end
                                   
                                   end
                                 end
                               else lookup (g_, d_, u_, s) T ((h_ :: t'_))
                               end
                      end in lookup (g_, d_, u_, s) (! table) [];;
        let rec memberSubsumes =
          function 
                   | ((g_, d_, u_, s), (g'_, u'_, [])) -> false
                   | ((g_, d_, u_, s), (g'_, u'_, (((d1_, s1), _) :: a_)))
                       -> let upi_ = A.raiseType (g_, u_)
                            in let upi'_ = A.raiseType (g'_, u'_)
                                 in let s1' = reinstSub (g'_, d1_, I.id)
                                      in let vpis_ =
                                           ((I.EClo (upi'_, s1)), s1')
                                           in let b =
                                                CSManager.trail
                                                (function 
                                                          | ()
                                                              -> Unify.unifiable
                                                                 (d_,
                                                                  (upi_, s),
                                                                  vpis_))
                                                in begin
                                                if b then
                                                begin
                                                  begin
                                                  if (! Global.chatter) >= 5
                                                  then
                                                  print
                                                  "\n answer in table subsumes answer \n "
                                                  else () end;true
                                                  end
                                                else
                                                memberSubsumes
                                                ((g_, d_, u_, s),
                                                 (g'_, u'_, a_))
                                                end;;
        let rec shift =
          function 
                   | (0, s) -> s
                   | (n, s) -> shift (n - 1, I.dot1 s);;
        let rec answCheckSubsumes (g_, d_, u_, s, o_) =
          let upi_ = A.raiseType (g_, u_)
            in let _ = begin
                 if (! Global.chatter) >= 4 then
                 begin
                   print "\n AnswCheckInsert (subsumes): ";
                   print
                   ((Print.expToString (I.null_, (I.EClo (upi_, s)))) ^ "\n")
                   end
                 else () end
                 in let rec lookup =
                      function 
                               | ((g_, d_, u_, s), [], T)
                                   -> begin
                                        print
                                        ((Print.expToString
                                          (concat (g_, d_), (I.EClo (u_, s))))
                                           ^
                                           " call should always be already in the table !\n");
                                        Repeated
                                        end
                               | ((g_, d_, u_, s),
                                  (((k, g'_, d'_, u'_),
                                    { solutions = a_; lookup = i})
                                   :: T),
                                  t'_) -> begin
                                   if
                                   subsumes ((g_, d_, u_), (g'_, d'_, u'_))
                                   then
                                   let (dk_, sk) = A.abstractAnswSub s
                                     in begin
                                     if
                                     memberSubsumes
                                     ((g_, dk_, u_, sk), (g'_, u'_, a_)) then
                                     Repeated else
                                     let s' = reinstSub (g'_, d'_, I.id)
                                       in let _ = begin
                                            if (! Global.chatter) >= 4 then
                                            begin
                                              print
                                              "\n new answer to be added to Index \n";
                                              begin
                                                print
                                                ((Print.expToString
                                                  (I.null_,
                                                   A.raiseType
                                                   (concat (g'_, d'_), u'_)))
                                                   ^ "\n");
                                                begin
                                                  print "\n answer added \n";
                                                  print
                                                  ((Print.expToString
                                                    (I.null_,
                                                     A.raiseType
                                                     (dk_,
                                                      (I.EClo
                                                       (A.raiseType (g_, u_),
                                                        sk)))))
                                                     ^ "\n")
                                                  
                                                  end
                                                
                                                end
                                              
                                              end
                                            else () end
                                            in let _ = begin
                                                 if
                                                 Unify.unifiable
                                                 (dk_,
                                                  (A.raiseType (g_, u_), sk),
                                                  (A.raiseType (g'_, u'_),
                                                   s'))
                                                 then begin
                                                 if (! Global.chatter) >= 4
                                                 then
                                                 begin
                                                   print
                                                   "\n1 unification successful !\n";
                                                   print
                                                   ((Print.expToString
                                                     (I.null_,
                                                      A.raiseType
                                                      (dk_,
                                                       (I.EClo
                                                        (A.raiseType
                                                         (g'_, u'_), s')))))
                                                      ^ "\n")
                                                   
                                                   end
                                                 else () end else
                                                 print
                                                 "\n1 unification failed! -- should never happen ?"
                                                 end
                                                 in let (dk'_, sk') =
                                                      A.abstractAnsw
                                                      (dk_, s')
                                                      in let rs =
                                                           reinstSub
                                                           (g'_, dk'_, I.id)
                                                           in begin
                                                                begin
                                                                match 
                                                                ! Query_
                                                                with 
                                                                
                                                                | None -> ()
                                                                | Some
                                                                    (g1_,
                                                                    d1_, u1_,
                                                                    s1, sc1)
                                                                    -> 
                                                                    begin
                                                                    begin
                                                                    if
                                                                    (!
                                                                    Global.chatter)
                                                                    >= 4 then
                                                                    begin
                                                                    print
                                                                    "Generate answers for: ";
                                                                    begin
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g1_,
                                                                    u1_), s1))))
                                                                    ^ " \n");
                                                                    begin
                                                                    print
                                                                    "Answer in table: ";
                                                                    begin
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    A.raiseType
                                                                    (dk_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g'_,
                                                                    u'_), s')))))
                                                                    ^ " : \n");
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (dk_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g'_,
                                                                    u'_),
                                                                    sk'))),
                                                                    rs)))) ^
                                                                    " : \n")
                                                                    end
                                                                    end
                                                                    end
                                                                    end else
                                                                    () end;
                                                                    begin
                                                                    if
                                                                    subsumes
                                                                    ((g1_,
                                                                    d1_, u1_),
                                                                    (g'_,
                                                                    d'_, u'_))
                                                                    then
                                                                    CSManager.trail
                                                                    (function 
                                                                    | ()
                                                                    -> begin
                                                                    if
                                                                    Unify.unifiable
                                                                    (d1_,
                                                                    (A.raiseType
                                                                    (g1_,
                                                                    u1_), s1),
                                                                    ((I.EClo
                                                                    (A.raiseType
                                                                    (g'_,
                                                                    u'_),
                                                                    sk')),
                                                                    rs)) then
                                                                    let w =
                                                                    begin
                                                                    if
                                                                    !
                                                                    strengthen
                                                                    then
                                                                    Subordinate.weaken
                                                                    (I.null_,
                                                                    IntSyn.targetFam
                                                                    ((I.EClo
                                                                    (u1_, s1))))
                                                                    else I.id
                                                                    end
                                                                    in 
                                                                    sc1 o_
                                                                    else ()
                                                                    end) else
                                                                    () end
                                                                    end
                                                                end;
                                                                begin
                                                                  table :=
                                                                    ((rev t'_)
                                                                    @
                                                                    ((((k,
                                                                    g'_, d'_,
                                                                    u'_),
                                                                    {
                                                                    solutions
                                                                    = 
                                                                    (((dk'_,
                                                                    sk'), o_)
                                                                    :: a_);
                                                                    lookup
                                                                    = i}
                                                                    ) :: T)));
                                                                  begin
                                                                    begin
                                                                    if
                                                                    (!
                                                                    Global.chatter)
                                                                    >= 5 then
                                                                    begin
                                                                    print
                                                                    "\n \n solution (original) was: \n";
                                                                    begin
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g_, u_),
                                                                    s)))) ^
                                                                    "\n");
                                                                    begin
                                                                    print
                                                                    "\n \n solution (deref) was: \n";
                                                                    begin
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    A.raiseType
                                                                    (dk_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g_, u_),
                                                                    sk))))) ^
                                                                    "\n");
                                                                    begin
                                                                    print
                                                                    "\n solution added  --- ";
                                                                    begin
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    A.raiseType
                                                                    (dk'_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g'_,
                                                                    u'_), s')))))
                                                                    ^ "\n");
                                                                    begin
                                                                    print
                                                                    "\n solution added (dereferenced) --- ";
                                                                    print
                                                                    ((Print.expToString
                                                                    (I.null_,
                                                                    A.raiseType
                                                                    (dk'_,
                                                                    (I.EClo
                                                                    (A.raiseType
                                                                    (g'_,
                                                                    u'_),
                                                                    sk')))))
                                                                    ^ "\n")
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end else
                                                                    () end;
                                                                    New
                                                                    end
                                                                  
                                                                  end
                                                                
                                                                end
                                     end
                                   else
                                   lookup
                                   ((g_, d_, u_, s), T,
                                    (((k, g'_, d'_, u'_),
                                      { solutions = a_; lookup = i} )
                                     :: t'_))
                                   end
                      in lookup ((g_, d_, u_, s), ! table, []);;
        let rec reset () = table := [];;
        let rec solutions { solutions = s_; lookup = i} = s_;;
        let rec lookup { solutions = s_; lookup = i} = i;;
        let rec noAnswers =
          function 
                   | [] -> true
                   | ((((g'_, d'_, u'_), answ) as h_) :: l'_)
                       -> begin
                          match List.take (solutions answ, lookup answ)
                          with 
                               | [] -> noAnswers l'_
                               | l_ -> false
                          end;;
        let rec callCheck (g_, d_, u_) =
          begin
          match ! strategy
          with 
               | Variant -> callCheckVariant (g_, d_, u_)
               | Subsumption -> callCheckSubsumes (g_, d_, u_)
          end;;
        let rec answCheck (g_, d_, u_, s, o_) =
          begin
          match ! strategy
          with 
               | Variant -> answCheckVariant (g_, d_, u_, s, o_)
               | Subsumption -> answCheckSubsumes (g_, d_, u_, s, o_)
          end;;
        let rec updateTable () =
          let rec update arg__4 arg__5 arg__6 =
            begin
            match (arg__4, arg__5, arg__6)
            with 
                 | ([], T, flag_) -> (flag_, T)
                 | ((((k, g_, d_, u_), { solutions = s_; lookup = i}) :: T),
                    t'_, flag_)
                     -> let l = length s_ in begin
                          if l = i then
                          update
                          T
                          ((((k, g_, d_, u_),
                             { solutions = s_; lookup = List.length s_} )
                            :: t'_))
                          flag_ else
                          update
                          T
                          ((((k, g_, d_, u_),
                             { solutions = s_; lookup = List.length s_} )
                            :: t'_))
                          true end
            end
            in let (flag_, T) = update (! table) [] false
                 in let r = flag_ || (! added)
                      in begin
                           added := false;begin
                                            table := (rev T);r
                                            end
                           end;;
        end;;
    (* Global Table *);;
    (* concat(Gdp, G) = G''
     *
     * if Gdp = ym...y1
     *    G   = xn...x1
     * then
     *    Gdp, G = G''
     *    ym...y1, xn...x1
     *
     *);;
    (* ---------------------------------------------------------------------- *);;
    (* printTable () = () *);;
    (* (print (Print.expToString (I.Null,  *);;
    (*              A.raiseType(Names.ctxName(concat(G,D')), I.EClo(U, s')))) *);;
    (* do not print pskeletons *);;
    (* printTableEntries () = () *);;
    (* ---------------------------------------------------------------------- *);;
    (* Term Abstraction *);;
    (* countDepth U =
         ctr = (ctrTerm, ctrDecl, ctrLength)
         ctrTerm : max term depth
         ctrDecl : max type depth in decl
         ctrLength : length of decl

    *);;
    (*         val _ = print (""\n ctrType' = "" ^ Int.toString ctrType')  *);;
    (*         val _ = print (""\n 1 ctrTerm = "" ^ Int.toString ctrTerm)
           val _ = print (""\n 1 ctxLength = "" ^ Int.toString ctrLength)
           val _ = print (""\n 1 ctxDepth = "" ^ Int.toString ctrType)
*);;
    (*         val _ = print (""\n ctrTerm = "" ^ Int.toString ctrTerm)
           val _ = print (""\n ctrType = "" ^ Int.toString ctrType)
*);;
    (* to revise ?*);;
    (*         val _ = print (""\n spineDepth = "" ^ Int.toString ctrDepth)
           val _ = print (""\n RootF = "" ^ Int.toString(ctrDepth + ctr))
*);;
    (*         (ctrLength + ctr) *);;
    (*         val _ = print (""\n SpindeDepth = "" ^ Int.toString ctrDepth)
           val _ = print (""\n Redex = "" ^ Int.toString(max(ctrDepth',ctrDepth) + ctr))*);;
    (* shouldn't happen *);;
    (* shouldn't happen *);;
    (* count max depth of term in S + length of S *);;
    (* ? *);;
    (* ---------------------------------------------------------------------- *);;
    (* reinstSub (G, D, s) = s'
    *
    * If D', G |- s : D, G
    * then  G |- s' : D, G
    *);;
    (* ---------------------------------------------------------------------- *);;
    (* variant (U,s) (U',s')) = bool   *);;
    (* subsumes ((G, D, U), (G', D', U')) = bool
     *
     * if
     *    D, G   |- U
     *    D', G' |- U'
     * then
     *      G' |- s' : D', G'
     *    return true if D, G |- U is an instance of G' |- U'[s']
     *    otherwise false
     *
     *);;
    (* ---------------------------------------------------------------------- *);;
    (* Call check and insert *);;
    (* callCheck (G, D, U) = callState

       check whether D, G |- U is in the table

     returns NONE,
        if D, G |- U is not already in the table
          Sideeffect: add D, G |- U to table

     returns SOME(A)
        if D, G |- U is in table and
          A is an entry in the table together with its answer list

    Variant:
    if it succeeds there is exactly one table entry which is a variant to U
    Subsumption:
    if it succeeds it will return the most general table entry of which U is
    an instance of (by invariant now, the most general table entry will be found first,
    any entry found later, will be an instance of this entry)
    *);;
    (* if termdepth(U) > n then force the tabled engine to suspend
               * and treat it like it is already in the table, but no answ available *);;
    (* print (""\n term "" ^ Print.expToString (I.Null, Upi) ^
                  "" exceeds depth or length ? \n""); *);;
    (* Subsumption:

       Assumes: Table is in order [tn, ...., t1]
       i.e. tn is added to the table later than t1
            this implies that tn is more general than ti (i < n)

       if we find a tn s.t M is an instance of it, then return tn
       and do not search further

    *);;
    (* ---------------------------------------------------------------------- *);;
    (* do we really need to compare Gus and Gs1 ?  *);;
    (* answer check and insert

      if     G |- U[s]
          D, G |- U
             G |- s : D, G

      answerCheck (G, D, (U,s)) = repeated
         if s already occurs in answer list for U
      answerCheck (G, D, (U,s)) = new
         if s did not occur in answer list for U
         Sideeffect: update answer list for U

        Dk, G |- sk : D, G
        Dk, G |- U[sk]

        sk is the abstraction of s and Dk contains all ""free"" vars

     *);;
    (* cannot happen ! *);;
    (* answer check *);;
    (* memberSubsumes ((G, Dk, U, sk), (G', U', A)) = bool

   If Dk, G |- U[sk]

      A = ((Dn, sn), On), ....., ((D1, s1), O1)

      for all i in [1, ..., n]
          Di, G' |- U'[si]
              G' |- si' : Di, G'
   then
     exists an i in [1,...,n]  s.t.
         Dk, G |- U[sk] is an instance of G' |- U'[si']
   *);;
    (* assume G' and G are the same for now *);;
    (* cannot happen ! *);;
    (*  higher-order matching *);;
    (* reinstantiate us' *);;
    (* nothing to do *);;
    (* original query is an instance of the entry we are adding answ to *);;
    (* (I.EClo(N1, I.comp(shift(I.ctxLength(Gdp1),s1), w))) *);;
    (*                    print(Print.expToString(I.Null, I.EClo(A.raiseType(concat(G, Dk), U), sk)) *);;
    (* ---------------------------------------------------------------------- *);;
    (* TOP LEVEL *);;
    (* needs to take into account previous size of table *);;
    (* no new solutions were added in the previous stage *);;
    (* new solutions were added *);;
    (* in each stage incrementally increase termDepth *);;
    (*          termDepth := (!termDepth +1); *);;
    (*  val termDepth = termDepth
    val ctxDepth = ctxDepth
    val ctxLength = ctxLength
*);;
    let table = table;;
    let solutions = solutions;;
    let lookup = lookup;;
    let noAnswers = noAnswers;;
    let reset = reset;;
    let printTable = printTable;;
    let printTableEntries = printTableEntries;;
    let callCheck = callCheck;;
    let answerCheck = answCheck;;
    let updateTable = updateTable;;
    end;;
(*! sharing TypeCheck.IntSyn = IntSyn' !*);;
(* local *);;
(* functor TableIndex *);;