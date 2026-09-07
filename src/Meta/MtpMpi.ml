open! Global.Global_
open! Table
open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_
open! Print.Print_
open! Timing

(* # 1 "src/meta/Mpi.sig.ml" *)
open Funsyn
open Statesyn
open MtpGlobal
open Relfun
open Funtypecheck
open MtpData
open MtpInit
open MtpFilling
open Inference
open MtpSplitting
open MtpRecursion
open MtpStrategy
open MtpPrint
open Timers
open Ring

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
include MTPMPI
(* signature MTPI *)

(* # 1 "src/meta/Mpi.fun.ml" *)
open! Basis

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPi (MTPi__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module RelFun : RELFUN.RELFUN

  (*! sharing RelFun.FunSyn = FunSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module MTPData : MTPDATA.MTPDATA
  module MTPInit : MTPINIT.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn' !*)
  module MTPFilling : MTPFILLING.MTPFILLING

  (*! sharing MTPFilling.FunSyn = FunSyn' !*)
  module Inference : INFERENCE.INFERENCE

  (*! sharing Inference.FunSyn = FunSyn' !*)
  module MTPSplitting : MTPSPLITTING.MTPSPLITTING
  module MTPRecursion : MTPRECURSION.MTPRECURSION
  module MTPStrategy : MTPSTRATEGY.MTPSTRATEGY
  module MTPrint : MTPPRINT.MTPRINT
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Timers : TIMERS.TIMERS
  module Ring : RING.RING
end) : MTPI = struct
  open MTPi__0

  exception Error = Error

  (*! structure FunSyn = FunSyn' !*)
  module StateSyn = StateSyn'

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module Fmt = Formatter

    type menuItem =
      | Filling of MTPFilling.operator
      | Recursion of MTPRecursion.operator
      | Splitting of MTPSplitting.operator
      | Inference of Inference.operator

    let open_ : StateSyn.state Ring.ring ref = ref (Ring.init [])
    let solved_ : StateSyn.state Ring.ring ref = ref (Ring.init [])

    let history_ :
        (StateSyn.state Ring.ring * StateSyn.state Ring.ring) list ref =
      ref []

    let menu_ : menuItem list option ref = ref None
    let initOpen () = open_ := Ring.init []
    let initSolved () = solved_ := Ring.init []
    let empty () = Ring.empty !open_
    let current () = Ring.current !open_
    let delete () = open_ := Ring.delete !open_
    let insertOpen s = open_ := Ring.insert (!open_) s
    let insertSolved s = solved_ := Ring.insert (!solved_) s
    let insert s = insertOpen s
    let collectOpen () = Ring.foldr (fun (a, b) -> a :: b) [] !open_
    let collectSolved () = Ring.foldr (fun (a, b) -> a :: b) [] !solved_
    let nextOpen () = open_ := Ring.next !open_
    let pushHistory () = history_ := (!open_, !solved_) :: !history_

    let popHistory () =
      begin match !history_ with
      | [] -> raise (Error "History stack empty")
      | (open', solved') :: history' -> begin
          history_ := history';
          begin
            open_ := open';
            solved_ := solved'
          end
        end
      end

    let abort s =
      begin
        print ("* " ^ s);
        raise (Error s)
      end

    let reset () =
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
      | c :: l -> (I.conDecName (I.sgnLookup c) ^ ", ") ^ cLToString l

    let printFmt (f : Print.Formatter.format) : Fmt.format =
      Fmt.string (Print.Formatter.makestring_fmt f)

    let printFillResult (_, p) =
      let formatTuple (g, p) =
        let rec formatTuple' = function
          | F.Unit -> []
          | F.Inx (m, F.Unit) -> [ printFmt (Print.formatExp g m) ]
          | F.Inx (m, p') ->
              printFmt (Print.formatExp g m)
              :: Fmt.string "," :: Fmt.break_ :: formatTuple' p'
        in
        begin match p with
        | F.Inx (_, F.Unit) -> Fmt.hbox (formatTuple' p)
        | _ ->
            Fmt.hVbox0 1 1 1
              ((Fmt.string "(" :: formatTuple' p) @ [ Fmt.string ")" ])
        end
      in
      let (S.State (n, (g, b), (ih, oh), d, o, h, f)) = current () in
      TextIO.print
        (("Filling successful with proof term:\n"
         ^ Formatter.makestring_fmt (formatTuple (g, p)))
        ^ "\n")

    let rec splittingToMenu (a, a_) = match a with
      | [] -> a_
      | o :: l -> splittingToMenu (l, Splitting o :: a_)

    let fillingToMenu (o, a) = Filling o :: a
    let recursionToMenu (o, a) = Recursion o :: a
    let inferenceToMenu (o, a) = Inference o :: a

    let menu () =
      begin if empty () then menu_ := None
      else
        let s = current () in
        let splitO = MTPSplitting.expand (Obj.magic s) in
        let infO = Inference.expand (Obj.magic s) in
        let recO = MTPRecursion.expand (Obj.magic s) in
        let fillO = MTPFilling.expand (Obj.magic s) in
        menu_ :=
          Some
            (fillingToMenu
               ( fillO,
                 recursionToMenu
                   (recO, inferenceToMenu (infO, splittingToMenu (splitO, [])))
               ))
      end

    let format k =
      begin if k < 10 then Int.toString k ^ ".  " else Int.toString k ^ ". "
      end

    let menuToString () =
      let rec menuToString' (k, a, kOopt) = match a, kOopt with
        | [], (None, _) -> (Some k, "")
        | [], ((Some _ as kopt'), _) -> (kopt', "")
        | Splitting o :: m, ((None, None) as kOopt') ->
            let kOopt'' =
              begin if MTPSplitting.applicable o then (Some k, Some o)
              else kOopt'
              end
            in
            let (Some k'' as kopt), s = menuToString' (k + 1, m, kOopt'') in
            ( kopt,
              begin if k = k'' then
                ((s ^ "\n* ") ^ format k) ^ MTPSplitting.menu o
              else ((s ^ "\n  ") ^ format k) ^ MTPSplitting.menu o
              end )
        | Splitting o :: m, ((Some k', Some o') as kOopt') ->
            let kOopt'' =
              begin if MTPSplitting.applicable o then
                begin match MTPSplitting.compare o o' with
                | Less -> (Some k, Some o)
                | _ -> kOopt'
                end
              else kOopt'
              end
            in
            let (Some k'' as kopt), s = menuToString' (k + 1, m, kOopt'') in
            ( kopt,
              begin if k = k'' then
                ((s ^ "\n* ") ^ format k) ^ MTPSplitting.menu o
              else ((s ^ "\n  ") ^ format k) ^ MTPSplitting.menu o
              end )
        | Filling o :: m, kOopt ->
            let kopt, s = menuToString' (k + 1, m, kOopt) in
            (kopt, ((s ^ "\n  ") ^ format k) ^ MTPFilling.menu o)
        | Recursion o :: m, kOopt ->
            let kopt, s = menuToString' (k + 1, m, kOopt) in
            (kopt, ((s ^ "\n  ") ^ format k) ^ MTPRecursion.menu o)
        | Inference o :: m, kOopt ->
            let kopt, s = menuToString' (k + 1, m, kOopt) in
            (kopt, ((s ^ "\n  ") ^ format k) ^ Inference.menu o)
      in
      begin match !menu_ with
      | None -> raise (Error "Menu is empty")
      | Some m ->
          let kopt, s = menuToString' (1, m, (None, None)) in
          s
      end

    let printMenu () =
      begin if empty () then begin
        print "[QED]\n";
        print
          (("Statistics: required Stelf.Prover.maxFill := "
           ^ Int.toString !MTPData.maxFill)
          ^ "\n")
      end
      else
        let s = current () in
        ignore begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s)
          else ()
          end;
        begin
          print "\n";
          begin
            print (MTPrint.stateToString (Obj.magic s));
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

    let rec contains (a, l') = match a with
      | [] -> true
      | x :: l ->
          List.exists (function x' -> x = x') l' && contains (l, l')

    let equiv l1 l2 = contains (l1, l2) && contains (l2, l1)

    let rec transformOrder' (g, a) = match a with
      | Order.Arg k ->
          let k' = I.ctxLength g - k + 1 in
          let (I.Dec (_, v)) = I.ctxDec g k' in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (v, I.id))
      | Order.Lex os ->
          S.Lex (map (function o -> transformOrder' (g, o)) os)
      | Order.Simul os ->
          S.Simul (map (function o -> transformOrder' (g, o)) os)

    let rec transformOrder (g, a, b) = match a, b with
      | F.All (F.Prim d, f), os ->
          S.All (d, transformOrder (I.Decl (g, d), f, os))
      | F.And (f1, f2), o :: os ->
          S.And (transformOrder (g, f1, [ o ]), transformOrder (g, f2, os))
      | F.Ex _, o :: [] -> transformOrder' (g, o)

    let select c = try Order.selLookup c with _ -> Order.Lex []

    let init k names =
      let cL =
        map
          (function
            | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names
      in
      ignore (MTPGlobal.maxFill := k);
      ignore (reset ());
      let f = RelFun.convertFor cL in
      let o = transformOrder (I.Null, f, map select cL) in
      let slist = MTPInit.init f (Obj.magic o) in
      ignore begin if List.length slist = 0 then raise Domain else ()
        end;
      try
        begin
          ignore
            (map
               (function
                 | s -> insert (Obj.magic (MTPrint.nameState (Obj.magic s))))
               slist);
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

    let select k =
      let rec select' = function
        | k, [] -> abort "No such menu item"
        | 1, Splitting o :: _ ->
            let s' = Timers.time Timers.splitting MTPSplitting.apply o in
            ignore (pushHistory ());
            ignore (delete ());
            ignore (ignore
                (map
                   (function
                     | s ->
                         insert (Obj.magic (MTPrint.nameState (Obj.magic s))))
                   s'));
            begin
              menu ();
              printMenu ()
            end
        | 1, Recursion o :: _ ->
            let s' = Timers.time Timers.recursion MTPRecursion.apply o in
            ignore (pushHistory ());
            ignore (delete ());
            ignore (insert (Obj.magic (MTPrint.nameState (Obj.magic s'))));
            begin
              menu ();
              printMenu ()
            end
        | 1, Inference o :: _ ->
            let s' = Timers.time Timers.recursion Inference.apply o in
            ignore (pushHistory ());
            ignore (delete ());
            ignore (insert (Obj.magic (MTPrint.nameState (Obj.magic s'))));
            begin
              menu ();
              printMenu ()
            end
        | 1, Filling o :: _ ->
            let p =
              try Timers.time Timers.filling MTPFilling.apply o
              with MTPFilling.Error _ ->
                abort "Filling unsuccessful: no object found"
            in
            ignore (printFillResult p);
            ignore (delete ());
            ignore (print "\n[Subgoal finished]\n");
            ignore (print "\n");
            begin
              menu ();
              printMenu ()
            end
        | k, _ :: m -> select' (k - 1, m)
      in
      try
        begin match !menu_ with
        | None -> raise (Error "No menu defined")
        | Some m -> select' (k, m)
        end
      with
      | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
      | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
      | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
      | Inference.Error s -> abort ("Inference Errror: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)

    let solve () =
      begin if empty () then raise (Error "Nothing to prove")
      else
        let s_ = current () in
        let open', solved' =
          try MTPStrategy.run [ Obj.magic s_ ] with
          | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
          | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
          | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
          | Inference.Error s -> abort ("Inference Errror: " ^ s)
          | Error s -> abort ("Mpi Error: " ^ s)
        in
        ignore (pushHistory ());
        ignore (delete ());
        ignore (ignore (map insertOpen (Obj.magic open')));
        ignore (ignore (map insertSolved (Obj.magic solved')));
        begin
          menu ();
          printMenu ()
        end
      end

    let check () =
      begin if empty () then raise (Error "Nothing to check")
      else
        let s = current () in
        FunTypeCheck.isState (Obj.magic s)
      end

    let auto () =
      let open', solved' =
        try MTPStrategy.run (Obj.magic (collectOpen ())) with
        | MTPSplitting.Error s -> abort ("MTPSplitting. Error: " ^ s)
        | MTPFilling.Error s -> abort ("Filling Error: " ^ s)
        | MTPRecursion.Error s -> abort ("Recursion Error: " ^ s)
        | Inference.Error s -> abort ("Inference Errror: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s)
      in
      ignore (pushHistory ());
      ignore (initOpen ());
      ignore (ignore (map insertOpen (Obj.magic open')));
      ignore (ignore (map insertSolved (Obj.magic solved')));
      begin
        menu ();
        printMenu ()
      end

    let next () =
      begin
        nextOpen ();
        begin
          menu ();
          printMenu ()
        end
      end

    let undo () =
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
  let solve = solve
  let auto = auto
  let check = check
  let undo = undo
end
(* local *)
(* functor MPI *)

(* # 1 "src/meta/MtpMpi.sml.ml" *)
