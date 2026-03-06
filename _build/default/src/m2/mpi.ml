# 1 "src/m2/mpi.sig.ml"
open! Basis;;
(* Meta Prover Interface *);;
(* Author: Carsten Schuermann *);;
module type MPI = sig
                  module MetaSyn : METASYN
                  exception Error of string 
                  val init : (int * string list) -> unit
                  val select : int -> unit
                  val print : unit -> unit
                  val next : unit -> unit
                  val auto : unit -> unit
                  val solve : unit -> unit
                  val lemma : string -> unit
                  val reset : unit -> unit
                  val extract : unit -> MetaSyn.sgn_
                  val show : unit -> unit
                  val undo : unit -> unit
                  end;;
(* signature MPI *);;
# 1 "src/m2/mpi.fun.ml"
open! Strategy;;
open! Splitting;;
open! Recursion;;
open! Qed;;
open! Lemma;;
open! Init;;
open! Filling;;
open! Basis;;
(* Meta Prover Interface *);;
(* Author: Carsten Schuermann *);;
module Mpi(Mpi__0: sig
                   module MetaGlobal : METAGLOBAL
                   module MetaSyn' : METASYN
                   module Init : INIT
                   module Filling : FILLING
                   module Splitting : SPLITTING
                   module Recursion : RECURSION
                   module Lemma : LEMMA
                   module Strategy : STRATEGY
                   module Qed : QED
                   module MetaPrint : METAPRINT
                   module Names : NAMES
                   (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                   module Timers : TIMERS
                   module Ring : RING
                   end) : MPI
  =
  struct
    module MetaSyn = MetaSyn';;
    exception Error of string ;;
    open!
      struct
        module M = MetaSyn;;
        module I = IntSyn;;
        type menuItem_ =
          | Filling of Filling.operator 
          | Recursion of Recursion.operator 
          | Splitting of Splitting.operator ;;
        let Open : MetaSyn.state_ Ring.ring ref = ref (Ring.init []);;
        let Solved : MetaSyn.state_ Ring.ring ref = ref (Ring.init []);;
        let history_ : (MetaSyn.state_ Ring.ring * MetaSyn.state_ Ring.ring)
          list ref = ref [];;
        let menu_ : menuItem_ list option ref = ref None;;
        let rec initOpen () = Open := (Ring.init []);;
        let rec initSolved () = Solved := (Ring.init []);;
        let rec empty () = Ring.empty (! Open);;
        let rec current () = Ring.current (! Open);;
        let rec delete () = Open := (Ring.delete (! Open));;
        let rec insertOpen s_ = Open := (Ring.insert (! Open, s_));;
        let rec insertSolved s_ = Solved := (Ring.insert (! Solved, s_));;
        let rec insert s_ = begin
          if Qed.subgoal s_ then
          begin
            insertSolved s_;
            begin
              print (MetaPrint.stateToString s_);
              begin
                print "\n[Subgoal finished]\n";print "\n"
                end
              
              end
            
            end
          else insertOpen s_ end;;
        let rec collectOpen () = Ring.foldr ( :: ) [] (! Open);;
        let rec collectSolved () = Ring.foldr ( :: ) [] (! Solved);;
        let rec nextOpen () = Open := (Ring.next (! Open));;
        let rec pushHistory () =
          history_ := (((! Open, ! Solved) :: ! history_));;
        let rec popHistory () =
          begin
          match ! history_
          with 
               | [] -> raise ((Error "History stack empty"))
               | ((open'_, solved'_) :: history'_)
                   -> begin
                        history_ := history'_;
                        begin
                          Open := open'_;Solved := solved'_
                          end
                        
                        end
          end;;
        let rec abort s = begin
                            print ("* " ^ s);raise ((Error s))
                            end;;
        let rec reset () =
          begin
            initOpen ();
            begin
              initSolved ();begin
                              history_ := [];menu_ := None
                              end
              end
            
            end;;
        let rec cLToString =
          function 
                   | [] -> ""
                   | (c :: []) -> I.conDecName (I.sgnLookup c)
                   | (c :: l_)
                       -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^
                            (cLToString l_);;
        let rec splittingToMenu_ =
          function 
                   | ([], a_) -> a_
                   | ((o_ :: l_), a_)
                       -> splittingToMenu_ (l_, ((Splitting o_) :: a_));;
        let rec fillingToMenu_ =
          function 
                   | ([], a_) -> a_
                   | ((o_ :: l_), a_)
                       -> fillingToMenu_ (l_, ((Filling o_) :: a_));;
        let rec recursionToMenu_ =
          function 
                   | ([], a_) -> a_
                   | ((o_ :: l_), a_)
                       -> recursionToMenu_ (l_, ((Recursion o_) :: a_));;
        let rec menu () = begin
          if empty () then menu_ := None else
          let s_ = current ()
            in let splitO_ = Splitting.expand s_
                 in let recO_ = Recursion.expandEager s_
                      in let (fillO_, fillC_) = Filling.expand s_
                           in menu_ :=
                                ((Some
                                  (fillingToMenu_
                                   ([fillC_],
                                    fillingToMenu_
                                    (fillO_,
                                     recursionToMenu_
                                     (recO_, splittingToMenu_ (splitO_, [])))))))
          end;;
        let rec format k = begin
          if k < 10 then (Int.toString k) ^ ".  " else
          (Int.toString k) ^ ". " end;;
        let rec menuToString () =
          let rec menuToString' =
            function 
                     | (k, []) -> ""
                     | (k, (Splitting o_ :: m_))
                         -> (((menuToString' (k + 1, m_)) ^ "\n") ^
                               (format k))
                              ^ (Splitting.menu o_)
                     | (k, (Filling o_ :: m_))
                         -> (((menuToString' (k + 1, m_)) ^ "\n") ^
                               (format k))
                              ^ (Filling.menu o_)
                     | (k, (Recursion o_ :: m_))
                         -> (((menuToString' (k + 1, m_)) ^ "\n") ^
                               (format k))
                              ^ (Recursion.menu o_)
            in begin
               match ! menu_
               with 
                    | None -> raise ((Error "Menu is empty"))
                    | Some m_ -> menuToString' (1, m_)
               end;;
        let rec makeConDec (M.State (name, M.Prefix (g_, m_, b_), v_)) =
          let rec makeConDec' =
            function 
                     | (null_, v_, k)
                         -> (I.ConDec
                             (name, None, k, I.normal_, v_, I.type_))
                     | (I.Decl (g_, d_), v_, k)
                         -> makeConDec'
                            (g_, (I.Pi ((d_, I.maybe_), v_)), k + 1)
            in makeConDec' (g_, v_, 0);;
        let rec makeSignature =
          function 
                   | [] -> M.sgnEmpty_
                   | (s_ :: sl_)
                       -> (M.ConDec (makeConDec s_, makeSignature sl_));;
        let rec extract () = begin
          if empty () then makeSignature (collectSolved ()) else
          begin
            print "[Error: Proof not completed yet]\n";M.sgnEmpty_
            end
          end;;
        let rec show () = print ((MetaPrint.sgnToString (extract ())) ^ "\n");;
        let rec printMenu () = begin
          if empty () then begin
                             show ();print "[QED]\n"
                             end
          else
          let s_ = current ()
            in begin
                 print "\n";
                 begin
                   print (MetaPrint.stateToString s_);
                   begin
                     print "\nSelect from the following menu:\n";
                     begin
                       print (menuToString ());print "\n"
                       end
                     
                     end
                   
                   end
                 
                 end
          end;;
        let rec contains =
          function 
                   | ([], _) -> true
                   | ((x :: l_), l'_)
                       -> (List.exists (function 
                                                 | x' -> x = x') l'_)
                            && (contains (l_, l'_));;
        let rec equiv (l1_, l2_) =
          (contains (l1_, l2_)) && (contains (l2_, l1_));;
        let rec init' (k, ((c :: _) as cL)) =
          let _ = MetaGlobal.maxFill := k
            in let _ = reset ()
                 in let cL' = try Order.closure c with 
                                                       | Order.Error _ -> cL
                      in begin
                      if equiv (cL, cL') then
                      map (function 
                                    | s_ -> insert s_) (Init.init cL)
                      else
                      raise
                      ((Error
                        (("Theorem by simultaneous induction not correctly stated:"
                            ^ "\n            expected: ")
                           ^ (cLToString cL'))))
                      end;;
        let rec init (k, nL) =
          let rec cids =
            function 
                     | [] -> []
                     | (name :: nL)
                         -> begin
                            match Names.stringToQid name
                            with 
                                 | None
                                     -> raise
                                        ((Error
                                          ("Malformed qualified identifier "
                                             ^ name)))
                                 | Some qid
                                     -> begin
                                        match Names.constLookup qid
                                        with 
                                             | None
                                                 -> raise
                                                    ((Error
                                                      (("Type family " ^
                                                          (Names.qidToString
                                                           qid))
                                                         ^ " not defined")))
                                             | Some cid -> (cid :: cids nL)
                                        end
                            end
            in try begin
                     init' (k, cids nL);begin
                                          menu ();printMenu ()
                                          end
                     end
               with 
                    | Splitting.Error s -> abort ("Splitting Error: " ^ s)
                    | Filling.Error s -> abort ("Filling Error: " ^ s)
                    | Recursion.Error s -> abort ("Recursion Error: " ^ s)
                    | Error s -> abort ("Mpi Error: " ^ s);;
        let rec select k =
          let rec select' =
            function 
                     | (k, []) -> abort "No such menu item"
                     | (1, (Splitting o_ :: _))
                         -> let s'_ =
                              Timers.time Timers.splitting Splitting.apply o_
                              in let _ = pushHistory ()
                                   in let _ = delete ()
                                        in let _ = map insert s'_
                                             in begin
                                                  menu ();printMenu ()
                                                  end
                     | (1, (Recursion o_ :: _))
                         -> let s'_ =
                              Timers.time Timers.recursion Recursion.apply o_
                              in let _ = pushHistory ()
                                   in let _ = delete ()
                                        in let _ = insert s'_
                                             in begin
                                                  menu ();printMenu ()
                                                  end
                     | (1, (Filling o_ :: _))
                         -> let _ =
                              begin
                              match Timers.time
                                    Timers.filling
                                    Filling.apply
                                    o_
                              with 
                                   | []
                                       -> abort
                                          "Filling unsuccessful: no object found"
                                   | (s_ :: _)
                                       -> begin
                                            delete ();
                                            begin
                                              insert s_;pushHistory ()
                                              end
                                            
                                            end
                              end in begin
                                       menu ();printMenu ()
                                       end
                     | (k, (_ :: m_)) -> select' (k - 1, m_)
            in try begin
                   match ! menu_
                   with 
                        | None -> raise ((Error "No menu defined"))
                        | Some m_ -> select' (k, m_)
                   end
               with 
                    | Splitting.Error s -> abort ("Splitting Error: " ^ s)
                    | Filling.Error s -> abort ("Filling Error: " ^ s)
                    | Recursion.Error s -> abort ("Recursion Error: " ^ s)
                    | Error s -> abort ("Mpi Error: " ^ s);;
        let rec lemma name = begin
          if empty () then raise ((Error "Nothing to prove")) else
          let s_ = current ()
            in let s'_ =
                 try Lemma.apply
                     (s_,
                      valOf
                      (Names.constLookup (valOf (Names.stringToQid name))))
                 with 
                      | Splitting.Error s -> abort ("Splitting Error: " ^ s)
                      | Filling.Error s -> abort ("Filling Error: " ^ s)
                      | Recursion.Error s -> abort ("Recursion Error: " ^ s)
                      | Error s -> abort ("Mpi Error: " ^ s)
                 in let _ = pushHistory ()
                      in let _ = delete ()
                           in let _ = insert s'_
                                in begin
                                     menu ();printMenu ()
                                     end
          end;;
        let rec solve () = begin
          if empty () then raise ((Error "Nothing to prove")) else
          let s_ = current ()
            in let (open'_, solved'_) =
                 try Strategy.run [s_]
                 with 
                      | Splitting.Error s -> abort ("Splitting Error: " ^ s)
                      | Filling.Error s -> abort ("Filling Error: " ^ s)
                      | Recursion.Error s -> abort ("Recursion Error: " ^ s)
                      | Error s -> abort ("Mpi Error: " ^ s)
                 in let _ = pushHistory ()
                      in let _ = delete ()
                           in let _ = map insertOpen open'_
                                in let _ = map insertSolved solved'_
                                     in begin
                                          menu ();printMenu ()
                                          end
          end;;
        let rec auto () =
          let (open'_, solved'_) =
            try Strategy.run (collectOpen ())
            with 
                 | Splitting.Error s -> abort ("Splitting Error: " ^ s)
                 | Filling.Error s -> abort ("Filling Error: " ^ s)
                 | Recursion.Error s -> abort ("Recursion Error: " ^ s)
                 | Error s -> abort ("Mpi Error: " ^ s)
            in let _ = pushHistory ()
                 in let _ = initOpen ()
                      in let _ = map insertOpen open'_
                           in let _ = map insertSolved solved'_
                                in begin
                                     menu ();printMenu ()
                                     end;;
        let rec next () =
          begin
            nextOpen ();begin
                          menu ();printMenu ()
                          end
            end;;
        let rec undo () =
          begin
            popHistory ();begin
                            menu ();printMenu ()
                            end
            end;;
        end;;
    (* if no termination ordering given! *);;
    let init = init;;
    let select = select;;
    let print = printMenu;;
    let next = next;;
    let lemma = lemma;;
    let reset = reset;;
    let Solve_ = Solve_;;
    let auto = auto;;
    let extract = extract;;
    let show = show;;
    let undo = undo;;
    end;;
(* local *);;
(* functor MPI *);;
# 1 "src/m2/mpi.sml.ml"
