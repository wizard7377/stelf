open! Intsyn.Lambda_
open! Names.Names_
open! Table
open! Timing

(* # 1 "src/m2/Mpi.sig.ml" *)
open Metasyn

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
include MPI
(* signature MPI *)

(* # 1 "src/m2/Mpi.fun.ml" *)
open! Basis
open Metasyn
open MetaGlobal
open MetaPrint
open Timers
open Ring

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Mpi (Mpi__0 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Init : INIT.INIT with module MetaSyn = MetaSyn'
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : LEMMA.LEMMA with module MetaSyn = MetaSyn'
  module Strategy : STRATEGY.STRATEGY with module MetaSyn = MetaSyn'
  module Qed : QED.QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Timers : TIMERS.TIMERS
  module Ring : RING.RING
end) : MPI with module MetaSyn = Mpi__0.MetaSyn' = struct
  open Mpi__0
  module MetaSyn = MetaSyn'

  exception Error = Error

  open! struct
    module M = MetaSyn
    module I = IntSyn

    type menuItem =
      | Filling of Filling.operator
      | Recursion of Recursion.operator
      | Splitting of Splitting.operator

    let openRing : MetaSyn.state Ring.ring ref = ref (Ring.init [])
    let solvedRing : MetaSyn.state Ring.ring ref = ref (Ring.init [])

    let history_ : (MetaSyn.state Ring.ring * MetaSyn.state Ring.ring) list ref
        =
      ref []

    let menu_ : menuItem list option ref = ref None
    let initOpen () = openRing := Ring.init []
    let initSolved () = solvedRing := Ring.init []
    let empty () = Ring.empty !openRing
    let current () = Ring.current !openRing
    let delete () = openRing := Ring.delete !openRing
    let insertOpen s = openRing := Ring.insert (!openRing) s
    let insertSolved s = solvedRing := Ring.insert (!solvedRing) s

    let insert s =
      begin if Qed.subgoal s then begin
        insertSolved s;
        begin
          print (MetaPrint.stateToString s);
          begin
            print "\n[Subgoal finished]\n";
            print "\n"
          end
        end
      end
      else insertOpen s
      end

    let collectOpen () = Ring.foldr (fun (x, acc) -> x :: acc) [] !openRing
    let collectSolved () = Ring.foldr (fun (x, acc) -> x :: acc) [] !solvedRing
    let nextOpen () = openRing := Ring.next !openRing
    let pushHistory () = history_ := (!openRing, !solvedRing) :: !history_

    let popHistory () =
      begin match !history_ with
      | [] -> raise (Error "History stack empty")
      | (open', solved') :: history' -> begin
          history_ := history';
          begin
            openRing := open';
            solvedRing := solved'
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

    let rec splittingToMenu (a, a_) = match a with
      | [] -> a_
      | o :: l -> splittingToMenu (l, Splitting o :: a_)

    let rec fillingToMenu (a, a_) = match a with
      | [] -> a_
      | o :: l -> fillingToMenu (l, Filling o :: a_)

    let rec recursionToMenu (a, a_) = match a with
      | [] -> a_
      | o :: l -> recursionToMenu (l, Recursion o :: a_)

    let menu () =
      begin if empty () then menu_ := None
      else
        let s = current () in
        let splitO = Splitting.expand s in
        let recO = Recursion.expandEager s in
        let fillO, fillC = Filling.expand s in
        menu_ :=
          Some
            (fillingToMenu
               ( [ fillC ],
                 fillingToMenu
                   (fillO, recursionToMenu (recO, splittingToMenu (splitO, [])))
               ))
      end

    let format k =
      begin if k < 10 then Int.toString k ^ ".  " else Int.toString k ^ ". "
      end

    let menuToString () =
      let rec menuToString' (k, a) = match a with
        | [] -> ""
        | Splitting o :: m ->
            ((menuToString' (k + 1, m) ^ "\n") ^ format k) ^ Splitting.menu o
        | Filling o :: m ->
            ((menuToString' (k + 1, m) ^ "\n") ^ format k) ^ Filling.menu o
        | Recursion o :: m ->
            ((menuToString' (k + 1, m) ^ "\n") ^ format k) ^ Recursion.menu o
      in
      begin match !menu_ with
      | None -> raise (Error "Menu is empty")
      | Some m -> menuToString' (1, m)
      end

    let makeConDec (M.State (name, M.Prefix (g, m, b), v)) =
      let rec makeConDec' (a, v, k) = match a with
        | I.Null -> I.ConDec (name, None, k, I.Normal, v, I.Type)
        | I.Decl (g, d) ->
            makeConDec' (g, I.Pi ((d, I.Maybe), v), k + 1)
      in
      makeConDec' (g, v, 0)

    let rec makeSignature = function
      | [] -> M.SgnEmpty
      | s :: sl -> M.ConDec (makeConDec s, makeSignature sl)

    let extract () =
      begin if empty () then makeSignature (collectSolved ())
      else begin
        print "[Error: Proof not completed yet]\n";
        M.SgnEmpty
      end
      end

    let show () = print (MetaPrint.sgnToString (extract ()) ^ "\n")

    let printMenu () =
      begin if empty () then begin
        show ();
        print "[QED]\n"
      end
      else
        let s = current () in
        print "\n";
        begin
          print (MetaPrint.stateToString s);
          begin
            print "\nSelect from the following menu:\n";
            begin
              print (menuToString ());
              print "\n"
            end
          end
        end
      end

    let rec contains (a, l') = match a with
      | [] -> true
      | x :: l ->
          List.exists (function x' -> x = x') l' && contains (l, l')

    let equiv l1 l2 = contains (l1, l2) && contains (l2, l1)

    let init' (k, (c :: _ as cL)) =
      ignore (MetaGlobal.maxFill := k);
      ignore (reset ());
      let cL' = try Order.closure c with Order.Error _ -> cL in
      begin if equiv cL cL' then
        List.app (function s -> insert s) (Init.init cL)
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:"
             ^ "\n            expected: ")
             ^ cLToString cL'))
      end

    let init k nL =
      let rec cids = function
        | [] -> []
        | name :: nL ->
            begin match Names.stringToQid name with
            | None -> raise (Error ("Malformed qualified identifier " ^ name))
            | Some qid ->
                begin match Names.constLookup qid with
                | None ->
                    raise
                      (Error
                         (("Type family " ^ Names.qidToString qid)
                         ^ " not defined"))
                | Some cid -> cid :: cids nL
                end
            end
      in
      try
        begin
          init' (k, cids nL);
          begin
            menu ();
            printMenu ()
          end
        end
      with
      | Splitting.Error s -> abort ("Splitting Error: " ^ s)
      | Filling.Error s -> abort ("Filling Error: " ^ s)
      | Recursion.Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)

    let select k =
      let rec select' = function
        | k, [] -> abort "No such menu item"
        | 1, Splitting o :: _ ->
            let s' = Timers.time Timers.splitting Splitting.apply o in
            ignore (pushHistory ());
            ignore (delete ());
            ignore (map insert s');
            begin
              menu ();
              printMenu ()
            end
        | 1, Recursion o :: _ ->
            let s' = Timers.time Timers.recursion Recursion.apply o in
            ignore (pushHistory ());
            ignore (delete ());
            ignore (insert s');
            begin
              menu ();
              printMenu ()
            end
        | 1, Filling o :: _ ->
            ignore begin match Timers.time Timers.filling Filling.apply o with
              | [] -> abort "Filling unsuccessful: no object found"
              | s :: _ -> begin
                  delete ();
                  begin
                    insert s;
                    pushHistory ()
                  end
                end
              end;
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
      | Splitting.Error s -> abort ("Splitting Error: " ^ s)
      | Filling.Error s -> abort ("Filling Error: " ^ s)
      | Recursion.Error s -> abort ("Recursion Error: " ^ s)
      | Error s -> abort ("Mpi Error: " ^ s)

    let lemma name =
      begin if empty () then raise (Error "Nothing to prove")
      else
        let s_ = current () in
        let s' =
          try
            Lemma.apply
              s_ (valOf (Names.constLookup (valOf (Names.stringToQid name))))
          with
          | Splitting.Error s -> abort ("Splitting Error: " ^ s)
          | Filling.Error s -> abort ("Filling Error: " ^ s)
          | Recursion.Error s -> abort ("Recursion Error: " ^ s)
          | Error s -> abort ("Mpi Error: " ^ s)
        in
        ignore (pushHistory ());
        ignore (delete ());
        ignore (insert s');
        begin
          menu ();
          printMenu ()
        end
      end

    let solve () =
      begin if empty () then raise (Error "Nothing to prove")
      else
        let s_ = current () in
        let open', solved' =
          try Strategy.run [ s_ ] with
          | Splitting.Error s -> abort ("Splitting Error: " ^ s)
          | Filling.Error s -> abort ("Filling Error: " ^ s)
          | Recursion.Error s -> abort ("Recursion Error: " ^ s)
          | Error s -> abort ("Mpi Error: " ^ s)
        in
        ignore (pushHistory ());
        ignore (delete ());
        ignore (map insertOpen open');
        ignore (map insertSolved solved');
        begin
          menu ();
          printMenu ()
        end
      end

    let auto () =
      let open', solved' =
        try Strategy.run (collectOpen ()) with
        | Splitting.Error s -> abort ("Splitting Error: " ^ s)
        | Filling.Error s -> abort ("Filling Error: " ^ s)
        | Recursion.Error s -> abort ("Recursion Error: " ^ s)
        | Error s -> abort ("Mpi Error: " ^ s)
      in
      ignore (pushHistory ());
      ignore (initOpen ());
      ignore (map insertOpen open');
      ignore (map insertSolved solved');
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

  (* if no termination ordering given! *)
  let init = init
  let select = select
  let print = printMenu
  let next = next
  let lemma = lemma
  let reset = reset
  let solve = solve
  let auto = auto
  let extract = extract
  let show = show
  let undo = undo
end
(* local *)
(* functor MPI *)

(* # 1 "src/m2/Mpi.sml.ml" *)
