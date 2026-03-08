open! Print
open! Inference
open! Global
open! Basis

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
module MTPi (MTPi__0 : sig
  module MTPGlobal : MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module RelFun : RELFUN

  (*! sharing RelFun.FunSyn = FunSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunTypeCheck : FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module MTPData : MTPDATA
  module MTPInit : MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn' !*)
  module MTPFilling : MTPFILLING

  (*! sharing MTPFilling.FunSyn = FunSyn' !*)
  module Inference : INFERENCE

  (*! sharing Inference.FunSyn = FunSyn' !*)
  module MTPSplitting : MTPSPLITTING
  module MTPRecursion : MTPRECURSION
  module MTPStrategy : MTPSTRATEGY
  module MTPrint : MTPRINT
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Timers : TIMERS
  module Ring : RING
end) : MTPI = struct
  exception Error of string

  (*! structure FunSyn = FunSyn' !*)
  module StateSyn = StateSyn'

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter

    type menuItem_ =
      | Filling of MTPFilling.operator
      | Recursion of MTPRecursion.operator
      | Splitting of MTPSplitting.operator
      | Inference of Inference.operator

    let Open : StateSyn.state_ Ring.ring ref = ref (Ring.init [])
    let Solved : StateSyn.state_ Ring.ring ref = ref (Ring.init [])

    let history_ :
        (StateSyn.state_ Ring.ring * StateSyn.state_ Ring.ring) list ref =
      ref []

    let menu_ : menuItem_ list option ref = ref None
    let rec initOpen () = Open := Ring.init []
    let rec initSolved () = Solved := Ring.init []
    let rec empty () = Ring.empty !Open
    let rec current () = Ring.current !Open
    let rec delete () = Open := Ring.delete !Open
    let rec insertOpen s_ = Open := Ring.insert (!Open, s_)
    let rec insertSolved s_ = Solved := Ring.insert (!Solved, s_)
    let rec insert s_ = insertOpen s_
    let rec collectOpen () = Ring.foldr ( :: ) [] !Open
    let rec collectSolved () = Ring.foldr ( :: ) [] !Solved
    let rec nextOpen () = Open := Ring.next !Open
    let rec pushHistory () = history_ := (!Open, !Solved) :: !history_

    let rec popHistory () =
      begin match !history_ with
      | [] -> raise (Error "History stack empty")
      | (open'_, solved'_) :: history'_ -> begin
          history_ := history'_;
          begin
            Open := open'_;
            Solved := solved'_
          end
        end
      end

    let rec abort s =
      begin
        print ("* " ^ s);
        raise (Error s)
      end

    let rec reset () =
      begin
        initOpen ();
        begin
          initSolved ();
          begin
            history_ := [];
            menu_ := None
          end
        end
      end

    let rec cLToString = function
      | [] -> ""
      | c :: [] -> I.conDecName (I.sgnLookup c)
      | c :: l_ -> (I.conDecName (I.sgnLookup c) ^ ", ") ^ cLToString l_

    let rec printFillResult (_, p_) =
      let rec formatTuple (g_, p_) =
        let rec formatTuple' = function
          | unit_ -> []
          | F.Inx (m_, unit_) -> [ Print.formatExp (g_, m_) ]
          | F.Inx (m_, p'_) ->
              Print.formatExp (g_, m_)
              :: Fmt.String "," :: Fmt.break_ :: formatTuple' p'_
        in
        begin match p_ with
        | F.Inx (_, unit_) -> Fmt.Hbox (formatTuple' p_)
        | _ ->
            Fmt.HVbox0
              (1, 1, 1, (Fmt.String "(" :: formatTuple' p_) @ [ Fmt.String ")" ])
        end
      in
      let (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_)) = current () in
      TextIO.print
        (("Filling successful with proof term:\n"
         ^ Formatter.makestring_fmt (formatTuple (g_, p_)))
        ^ "\n")

    let rec splittingToMenu_ = function
      | [], a_ -> a_
      | o_ :: l_, a_ -> splittingToMenu_ (l_, Splitting o_ :: a_)

    let rec fillingToMenu_ (o_, a_) = Filling o_ :: a_
    let rec recursionToMenu_ (o_, a_) = Recursion o_ :: a_
    let rec inferenceToMenu_ (o_, a_) = Inference o_ :: a_

    let rec menu () =
      begin if empty () then menu_ := None
      else
        let s_ = current () in
        let splitO_ = MTPSplitting.expand s_ in
        let infO_ = Inference.expand s_ in
        let recO_ = MTPRecursion.expand s_ in
        let fillO_ = MTPFilling.expand s_ in
        menu_ :=
          Some
            (fillingToMenu_
               ( fillO_,
                 recursionToMenu_
                   ( recO_,
                     inferenceToMenu_ (infO_, splittingToMenu_ (splitO_, [])) )
               ))
      end

    let rec format k =
      begin if k < 10 then Int.toString k ^ ".  " else Int.toString k ^ ". "
      end

    let rec menuToString () =
      let rec menuToString' = function
        | k, [], (None, _) -> (Some k, "")
        | k, [], ((Some _ as kopt'), _) -> (kopt', "")
        | k, Splitting o_ :: m_, ((None, None) as kOopt') ->
            let kOopt'' =
              begin if MTPSplitting.applicable o_ then (Some k, Some o_)
              else kOopt'
              end
            in
            let (Some k'' as kopt), s = menuToString' (k + 1, m_, kOopt'') in
            ( kopt,
              begin if k = k'' then
                ((s ^ "\n* ") ^ format k) ^ MTPSplitting.menu o_
              else ((s ^ "\n  ") ^ format k) ^ MTPSplitting.menu o_
              end )
        | k, Splitting o_ :: m_, ((Some k', Some o'_) as kOopt') ->
            let kOopt'' =
              begin if MTPSplitting.applicable o_ then begin
                match MTPSplitting.compare (o_, o'_) with
                | Less -> (Some k, Some o_)
                | _ -> kOopt'
              end
              else kOopt'
              end
            in
            let (Some k'' as kopt), s = menuToString' (k + 1, m_, kOopt'') in
            ( kopt,
              begin if k = k'' then
                ((s ^ "\n* ") ^ format k) ^ MTPSplitting.menu o_
              else ((s ^ "\n  ") ^ format k) ^ MTPSplitting.menu o_
              end )
        | k, Filling o_ :: m_, kOopt ->
            let kopt, s = menuToString' (k + 1, m_, kOopt) in
            (kopt, ((s ^ "\n  ") ^ format k) ^ MTPFilling.menu o_)
        | k, Recursion o_ :: m_, kOopt ->
            let kopt, s = menuToString' (k + 1, m_, kOopt) in
            (kopt, ((s ^ "\n  ") ^ format k) ^ MTPRecursion.menu o_)
        | k, Inference o_ :: m_, kOopt ->
            let kopt, s = menuToString' (k + 1, m_, kOopt) in
            (kopt, ((s ^ "\n  ") ^ format k) ^ Inference.menu o_)
      in
      begin match !menu_ with
      | None -> raise (Error "Menu is empty")
      | Some m_ ->
          let kopt, s = menuToString' (1, m_, (None, None)) in
          s
      end

    let rec printMenu () =
      begin if empty () then begin
        print "[QED]\n";
        print
          (("Statistics: required Twelf.Prover.maxFill := "
           ^ Int.toString !MTPData.maxFill)
          ^ "\n")
      end
      else
        let s_ = current () in
        let _ =
          begin if !Global.doubleCheck then FunTypeCheck.isState s_ else ()
          end
        in
        begin
          print "\n";
          begin
            print (MTPrint.stateToString s_);
            begin
              print "\nSelect from the following menu:\n";
              begin
                print (menuToString ());
                print "\n"
              end
            end
          end
        end
      end

    let rec contains = function
      | [], _ -> true
      | x :: l_, l'_ ->
          List.exists (function x' -> x = x') l'_ && contains (l_, l'_)

    let rec equiv (l1_, l2_) = contains (l1_, l2_) && contains (l2_, l1_)

    let rec transformOrder' = function
      | g_, Order.Arg k ->
          let k' = I.ctxLength g_ - k + 1 in
          let (I.Dec (_, v_)) = I.ctxDec (g_, k') in
          S.Arg ((I.Root (I.BVar k', I.nil_), I.id), (v_, I.id))
      | g_, Order.Lex os_ ->
          S.Lex (map (function o_ -> transformOrder' (g_, o_)) os_)
      | g_, Order.Simul os_ ->
          S.Simul (map (function o_ -> transformOrder' (g_, o_)) os_)

    let rec transformOrder = function
      | g_, F.All (F.Prim d_, f_), os_ ->
          S.All (d_, transformOrder (I.Decl (g_, d_), f_, os_))
      | g_, F.And (f1_, f2_), o_ :: os_ ->
          S.And (transformOrder (g_, f1_, [ o_ ]), transformOrder (g_, f2_, os_))
      | g_, F.Ex _, o_ :: [] -> transformOrder' (g_, o_)

    let rec select c = try Order.selLookup c with _ -> Order.Lex []

    let rec init (k, names) =
      let cL =
        map
          (function
            | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names
      in
      let _ = MTPGlobal.maxFill := k in
      let _ = reset () in
      let f_ = RelFun.convertFor cL in
      let o_ = transformOrder (I.null_, f_, map select cL) in
      let slist_ = MTPInit.init (f_, o_) in
      let _ =
        begin if List.length slist_ = 0 then raise Domain else ()
        end
      in
      try
        begin
          map (function s_ -> insert (MTPrint.nameState s_)) slist_;
          begin
            menu ();
            printMenu ()
          end
        end
      with
      | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
      | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
      | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
      | Inference.Error s -> abort ("Inference Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)

    let rec select k =
      let rec select' = function
        | k, [] -> abort "No such menu item"
        | 1, Splitting o_ :: _ ->
            let s'_ = Timers.time Timers.splitting MTPSplitting.apply o_ in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = map (function s_ -> insert (MTPrint.nameState s_)) s'_ in
            begin
              menu ();
              printMenu ()
            end
        | 1, Recursion o_ :: _ ->
            let s'_ = Timers.time Timers.recursion MTPRecursion.apply o_ in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert (MTPrint.nameState s'_) in
            begin
              menu ();
              printMenu ()
            end
        | 1, Inference o_ :: _ ->
            let s'_ = Timers.time Timers.recursion Inference.apply o_ in
            let _ = pushHistory () in
            let _ = delete () in
            let _ = insert (MTPrint.nameState s'_) in
            begin
              menu ();
              printMenu ()
            end
        | 1, Filling o_ :: _ ->
            let p_ =
              try Timers.time Timers.filling MTPFilling.apply o_
              with MTPFilling.Error _ ->
                abort "Filling unsuccessful: no object found"
            in
            let _ = printFillResult p_ in
            let _ = delete () in
            let _ = print "\n[Subgoal finished]\n" in
            let _ = print "\n" in
            begin
              menu ();
              printMenu ()
            end
        | k, _ :: m_ -> select' (k - 1, m_)
      in
      try
        begin match !menu_ with
        | None -> raise (Error "No menu defined")
        | Some m_ -> select' (k, m_)
        end
      with
      | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
      | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
      | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
      | Inference.Error s -> abort ("Inference Errror: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)

    let rec solve () =
      begin if empty () then raise (Error "Nothing to prove")
      else
        let s_ = current () in
        let open'_, solved'_ =
          try MTPStrategy.run [ s_ ] with
          | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
          | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
          | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
          | Inference.Error s -> abort ("Inference Errror: " ^ s)
          | Error s -> abort ("Mpi Error: " ^ s)
        in
        let _ = pushHistory () in
        let _ = delete () in
        let _ = map insertOpen open'_ in
        let _ = map insertSolved solved'_ in
        begin
          menu ();
          printMenu ()
        end
      end

    let rec check () =
      begin if empty () then raise (Error "Nothing to check")
      else
        let s_ = current () in
        FunTypeCheck.isState s_
      end

    let rec auto () =
      let open'_, solved'_ =
        try MTPStrategy.run (collectOpen ()) with
        | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
        | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
        | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
        | Inference.Error s -> abort ("Inference Errror: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s)
      in
      let _ = pushHistory () in
      let _ = initOpen () in
      let _ = map insertOpen open'_ in
      let _ = map insertSolved solved'_ in
      begin
        menu ();
        printMenu ()
      end

    let rec next () =
      begin
        nextOpen ();
        begin
          menu ();
          printMenu ()
        end
      end

    let rec undo () =
      begin
        popHistory ();
        begin
          menu ();
          printMenu ()
        end
      end
  end

  let init = init
  let select = select
  let print = printMenu
  let next = next
  let reset = reset
  let Solve_ = Solve_
  let auto = auto
  let check = check
  let undo = undo
end
(* local *)
(* functor MPI *)
