open! Tomega_lib.Tomega_
open! Intsyn.Lambda_
open! Global.Global_
open! Names.Names_
open! Print.Print_
open! Modes.Modes_
open! Table
open! Trail.Trail_
open! Worldcheck.Worldcheck_
open! Formatter__Formatter_
open! Timing

(* # 1 "src/prover/Interactive.sig.ml" *)

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
include INTERACTIVE

(*  val undo   : unit -> unit *)
(* signature Interactive *)

(* # 1 "src/prover/Interactive.fun.ml" *)
open! Pweaken
open! Split
open! Introduce
open! Fill
open! Elim
open! Basis

module Interactive (Interactive__0 : sig
  (* Meta Prover Interface *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Formatter : FORMATTER
  module Trail : TRAIL
  module Ring : Ring.RING
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Weaken : WEAKEN

  (*! sharing Weaken.IntSyn = IntSyn' !*)
  (* structure ModeSyn : MODESYN *)
  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module WorldSyn : WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn' !*)
  (*! sharing WorldSyn.Tomega = Tomega' !*)
  module Introduce : INTRODUCE with module State = State'

  (*! sharing Introduce.IntSyn = IntSyn' !*)
  (*! sharing Introduce.Tomega = Tomega' !*)
  module Elim : ELIM with module State = State'

  (*! sharing Elim.IntSyn = IntSyn' !*)
  (*! sharing Elim.Tomega = Tomega' !*)
  module Split : SPLIT with module State = State'

  (*! sharing Split.IntSyn = IntSyn' !*)
  (*! sharing Split.Tomega = Tomega' !*)
  module FixedPoint : Fixedpoint.FIXEDPOINT with module State = State'

  (*! sharing FixedPoint.IntSyn = IntSyn' !*)
  (*! sharing FixedPoint.Tomega = Tomega' !*)
  module Fill : FILL with module State = State'
end) : INTERACTIVE = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = Interactive__0.State'
  module Weaken = Interactive__0.Weaken
  module Introduce = Interactive__0.Introduce
  module Elim = Interactive__0.Elim
  module Split = Interactive__0.Split
  module FixedPoint = Interactive__0.FixedPoint
  module Fill = Interactive__0.Fill
  module Timers = Timers.Timers

  exception Error = Interactive__0.State'.Error

  open! struct
    module I = IntSyn
    module T = Tomega
    module S = State
    module M = Modes.Modesyn.ModeSyn
    module W = WorldSyn

    let abort s =
      begin
        print (("* " ^ s) ^ "\n");
        raise (Error s)
      end

    let convertOneFor cid =
      let v =
        begin match I.sgnLookup cid with
        | I.ConDec (name, _, _, _, v, I.Kind) -> v
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let mS =
        begin match ModeTable.modeLookup cid with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let rec convertFor' = function
        | I.Pi ((d, _), v), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n ->
            let f', f'' =
              convertFor' (v, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
            in
            ( (function
              | f ->
                  T.All
                    ( (T.UDec (Weaken.strengthenDec d w1), T.Explicit),
                      f' f )),
              f'' )
        | I.Pi ((d, _), v), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n ->
            let f', f'' =
              convertFor' (v, mS, I.comp w1 I.shift, I.dot1 w2, n + 1)
            in
            (f', T.Ex ((I.decSub d w2, T.Explicit), f''))
        | I.Uni I.Type, M.Mnil, _, _, _ -> ((function f -> f), T.True)
        | _ -> raise (Error "type family must be +/- moded")
      in
      let shiftPlus mS =
        let rec shiftPlus' (a, n) = match a with
          | M.Mnil -> n
          | M.Mapp (M.Marg (M.Plus, _), mS') -> shiftPlus' (mS', n + 1)
          | M.Mapp (M.Marg (M.Minus, _), mS') -> shiftPlus' (mS', n)
        in
        shiftPlus' (mS, 0)
      in
      let n = shiftPlus mS in
      let f, f' = convertFor' (v, mS, I.id, I.Shift n, n) in
      f f'

    let rec convertFor = function
      | [] -> raise (Error "Empty theorem")
      | a :: [] -> convertOneFor a
      | a :: l -> T.And (convertOneFor a, convertFor l)

    type menuItem =
      | Split of Split.operator
      | Fill of Fill.operator
      | Introduce of Introduce.operator
      | Fix of FixedPoint.operator
      | Elim of Elim.operator

    let focus_ : S.state list ref = ref []
    let menu_ : menuItem list option ref = ref None
    let splittingToMenu (o, a) = Split o :: a
    let initFocus () = focus_ := []

    let normalize () =
      begin match !focus_ with
      | S.State (w, psi, p, f) :: rest ->
          focus_ := S.State (w, psi, T.derefPrg p, f) :: rest
      | _ -> ()
      end

    let reset () =
      begin
        initFocus ();
        menu_ := None
      end

    let format k =
      begin if k < 10 then Int.toString k ^ ".  " else Int.toString k ^ ". "
      end

    let menuToString () =
      let rec menuToString' (k, a) = match a with
        | [] -> ""
        | Split o :: m ->
            let s = menuToString' (k + 1, m) in
            ((s ^ "\n  ") ^ format k) ^ Split.menu o
        | Introduce o :: m ->
            let s = menuToString' (k + 1, m) in
            ((s ^ "\n  ") ^ format k) ^ Introduce.menu o
        | Fill o :: m ->
            let s = menuToString' (k + 1, m) in
            ((s ^ "\n  ") ^ format k) ^ Fill.menu o
        | Fix o :: m ->
            let s = menuToString' (k + 1, m) in
            ((s ^ "\n  ") ^ format k) ^ FixedPoint.menu o
        | Elim o :: m ->
            let s = menuToString' (k + 1, m) in
            ((s ^ "\n  ") ^ format k) ^ Elim.menu o
      in
      begin match !menu_ with
      | None -> raise (Error "Menu is empty")
      | Some m -> menuToString' (1, m)
      end

    let printStats () =
      let nopen = 0 in
      let nsolved = 0 in
      print "Statistics:\n\n";
      begin
        print (("Number of goals : " ^ Int.toString (nopen + nsolved)) ^ "\n");
        begin
          print (("     open goals : " ^ Int.toString nopen) ^ "\n");
          print (("   solved goals : " ^ Int.toString nsolved) ^ "\n")
        end
      end

    let printmenu () =
      begin match !focus_ with
      | [] -> abort "QED"
      | S.State (w, psi, p, f) :: r -> begin
          print "\n=======================";
          begin
            print "\n= META THEOREM PROVER =\n";
            begin
              print (TomegaPrint.ctxToString psi);
              begin
                print "\n-----------------------\n";
                begin
                  print (TomegaPrint.forToString psi f);
                  begin
                    print "\n-----------------------\n";
                    begin
                      print (TomegaPrint.prgToString psi p);
                      begin
                        print "\n-----------------------";
                        begin
                          print (menuToString ());
                          print "\n=======================\n"
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      | S.StateLF (I.EVar (r, g, v, cs) as x) :: r_ -> begin
          print "\n=======================";
          begin
            print "\n=== THEOREM PROVER ====\n";
            begin
              print (Print.ctxToString I.Null g);
              begin
                print "\n-----------------------\n";
                begin
                  print (Print.expToString g v);
                  begin
                    print "\n-----------------------\n";
                    begin
                      print (Print.expToString g x);
                      begin
                        print "\n-----------------------";
                        begin
                          print (menuToString ());
                          print "\n=======================\n"
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end

    let menu () =
      begin match !focus_ with
      | [] -> print "Please initialize first\n"
      | S.State (w, psi, p, f) :: _ ->
          let xs = S.collectT p in
          let f1 =
            map
              (function
                | T.EVar (psi, r, f, tc, tCs, x) -> begin
                    Names.varReset I.Null;
                    S.Focus
                      (T.EVar (TomegaPrint.nameCtx psi, r, f, tc, tCs, x), w)
                  end)
              xs
          in
          let ys = S.collectLF p in
          let f2 = map (function y -> S.FocusLF y) ys in
          let rec splitMenu = function
            | [] -> []
            | operators :: l ->
                map (function o -> Split o) operators @ splitMenu l
          in
          ignore (Global.doubleCheck := true);
          let rec introMenu = function
            | [] -> []
            | Some oper :: l -> Introduce oper :: introMenu l
            | None :: l -> introMenu l
          in
          let intro = introMenu (map Introduce.expand f1) in
          let fill =
            foldr
              (function
                | s, l -> l @ map (function o -> Fill o) (Fill.expand s))
              [] f2
          in
          let rec elimMenu = function
            | [] -> []
            | operators :: l ->
                map (function o -> Elim o) operators @ elimMenu l
          in
          let elim = elimMenu (map Elim.expand f1) in
          let split = splitMenu (map Split.expand f1) in
          menu_ := Some (intro @ split @ fill @ elim)
      | S.StateLF y :: _ ->
          let ys = Abstract.collectEVars I.Null (y, I.id) [] in
          let f2 = map (function y -> S.FocusLF y) ys in
          let fill =
            foldr
              (function
                | s, l -> l @ map (function o -> Fill o) (Fill.expand s))
              [] f2
          in
          menu_ := Some fill
      end

    let select k =
      let rec select' = function
        | k, [] -> abort "No such menu item"
        | 1, Split o :: _ -> Timers.time Timers.splitting Split.apply o
        | 1, Introduce o :: _ -> Introduce.apply o
        | 1, Elim o :: _ -> Elim.apply o
        | 1, Fill o :: _ -> Timers.time Timers.filling Fill.apply o
        | k, _ :: m -> select' (k - 1, m)
      in
      begin match !menu_ with
      | None -> raise (Error "No menu defined")
      | Some m -> (
          try
            begin
              select' (k, m);
              begin
                normalize ();
                begin
                  menu ();
                  printmenu ()
                end
              end
            end
          with S.Error s -> ())
      end

    let init names =
      ignore (TomegaPrint.evarReset ());
      let cL =
        map
          (function
            | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names
      in
      let f_ = convertFor cL in
      let ws = map W.lookup cL in
      let select c =
        try Intsyn.Order.selLookup c with _ -> Intsyn.Order.Lex []
      in
      let tc = Tomega.transformTC I.Null f_ (map select cL) in
      let (w :: _) = ws in
      ignore (focus_ := [ S.init f_ w ]);
      let p =
        begin match !focus_ with
        | [] -> abort "Initialization of proof goal failed\n"
        | S.State (w, psi, p, f) :: _ -> p
        end
      in
      let xs = S.collectT p in
      let f_ =
        map
          (function
            | T.EVar (psi, r, f, tc, tCs, x) -> begin
                Names.varReset I.Null;
                S.Focus
                  (T.EVar (TomegaPrint.nameCtx psi, r, f, tc, tCs, x), w)
              end)
          xs
      in
      let (ofix :: []) = map (function f -> FixedPoint.expand f tc) f_ in
      ignore (FixedPoint.apply ofix);
      ignore (normalize ());
      ignore (menu ());
      ignore (printmenu ());
      ()

    let focus n =
      begin match !focus_ with
      | [] -> print "Please initialize first\n"
      | S.State (w, psi, p, f) :: _ ->
          let rec findIEVar = function
            | [] -> raise (Error ("cannot focus on " ^ n))
            | y :: ys ->
                begin if Names.evarName (T.coerceCtx psi) y = n then begin
                  focus_ := S.StateLF y :: !focus_;
                  begin
                    normalize ();
                    begin
                      menu ();
                      printmenu ()
                    end
                  end
                end
                else findIEVar ys
                end
          in
          let rec findTEVar = function
            | [] -> findIEVar (S.collectLF p)
            | (T.EVar (psi, r, f, tc, tCs, y) as x) :: xs ->
                begin if Names.evarName (T.coerceCtx psi) y = n then begin
                  focus_ :=
                    S.State (w, TomegaPrint.nameCtx psi, x, f) :: !focus_;
                  begin
                    normalize ();
                    begin
                      menu ();
                      printmenu ()
                    end
                  end
                end
                else findTEVar xs
                end
          in
          findTEVar (S.collectT p)
      | S.StateLF u :: _ ->
          begin match Names.getEVarOpt n with
          | None -> raise (Error ("cannot focus on " ^ n))
          | Some y -> begin
              focus_ := S.StateLF y :: !focus_;
              begin
                normalize ();
                begin
                  menu ();
                  printmenu ()
                end
              end
            end
          end
      end

    let return () =
      begin match !focus_ with
      | s :: [] ->
          begin if S.close s then print "[Q.E.D.]\n" else ()
          end
      | s :: rest -> begin
          focus_ := rest;
          begin
            normalize ();
            begin
              menu ();
              printmenu ()
            end
          end
        end
      end
  end

  (* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
  (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
  (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
  (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
  (* here ends the preliminary stuff *)
  (*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ ""\n  "" ^ (format k) ^ (Inference.menu O))
              end
*)
  (* no timer yet -- cs *)
  (* no timer yet -- cs *)
  (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
  (* focus n = ()

       Invariant:
       Let n be a string.
       Side effect: Focus on selected subgoal.
    *)
  (* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *)
  let init = init
  let select = select
  let print = printmenu
  let stats = printStats
  let reset = reset
  let focus = focus
  let return = return
end
(*! sharing Fill.IntSyn = IntSyn' !*)
(*! sharing Fill.Tomega = Tomega' !*)
(* functor Interactive *)

(* # 1 "src/prover/Interactive.sml.ml" *)
