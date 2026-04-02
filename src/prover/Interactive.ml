(* # 1 "src/prover/Interactive.sig.ml" *)
open! Basis

(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)
include Interactive_intf
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

    let rec abort s =
      begin
        print (("* " ^ s) ^ "\n");
        raise (Error s)
      end

    let rec convertOneFor cid =
      let v_ =
        begin match I.sgnLookup cid with
        | I.ConDec (name, _, _, _, v_, I.Kind) -> v_
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
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
            in
            ( (function
              | f_ ->
                  T.All
                    ( (T.UDec (Weaken.strengthenDec (d_, w1)), T.Explicit),
                      f'_ f_ )),
              f''_ )
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.comp (w1, I.shift), I.dot1 w2, n + 1)
            in
            (f'_, T.Ex ((I.decSub (d_, w2), T.Explicit), f''_))
        | I.Uni I.Type, M.Mnil, _, _, _ -> ((function f_ -> f_), T.True)
        | _ -> raise (Error "type family must be +/- moded")
      in
      let rec shiftPlus mS =
        let rec shiftPlus' = function
          | M.Mnil, n -> n
          | M.Mapp (M.Marg (M.Plus, _), mS'), n -> shiftPlus' (mS', n + 1)
          | M.Mapp (M.Marg (M.Minus, _), mS'), n -> shiftPlus' (mS', n)
        in
        shiftPlus' (mS, 0)
      in
      let n = shiftPlus mS in
      let f_, f'_ = convertFor' (v_, mS, I.id, I.Shift n, n) in
      f_ f'_

    let rec convertFor = function
      | [] -> raise (Error "Empty theorem")
      | a :: [] -> convertOneFor a
      | a :: l_ -> T.And (convertOneFor a, convertFor l_)

    type menuItem =
      | Split of Split.operator
      | Fill of Fill.operator
      | Introduce of Introduce.operator
      | Fix of FixedPoint.operator
      | Elim of Elim.operator

    let focus_ : S.state list ref = ref []
    let menu_ : menuItem list option ref = ref None
    let rec splittingToMenu_ (o_, a_) = Split o_ :: a_
    let rec initFocus () = focus_ := []

    let rec normalize () =
      begin match !focus_ with
      | S.State (w_, psi_, p_, f_) :: rest_ ->
          focus_ := S.State (w_, psi_, T.derefPrg p_, f_) :: rest_
      | _ -> ()
      end

    let rec reset () =
      begin
        initFocus ();
        menu_ := None
      end

    let rec format k =
      begin if k < 10 then Int.toString k ^ ".  " else Int.toString k ^ ". "
      end

    let rec menuToString () =
      let rec menuToString' = function
        | k, [] -> ""
        | k, Split o_ :: m_ ->
            let s = menuToString' (k + 1, m_) in
            ((s ^ "\n  ") ^ format k) ^ Split.menu o_
        | k, Introduce o_ :: m_ ->
            let s = menuToString' (k + 1, m_) in
            ((s ^ "\n  ") ^ format k) ^ Introduce.menu o_
        | k, Fill o_ :: m_ ->
            let s = menuToString' (k + 1, m_) in
            ((s ^ "\n  ") ^ format k) ^ Fill.menu o_
        | k, Fix o_ :: m_ ->
            let s = menuToString' (k + 1, m_) in
            ((s ^ "\n  ") ^ format k) ^ FixedPoint.menu o_
        | k, Elim o_ :: m_ ->
            let s = menuToString' (k + 1, m_) in
            ((s ^ "\n  ") ^ format k) ^ Elim.menu o_
      in
      begin match !menu_ with
      | None -> raise (Error "Menu is empty")
      | Some m_ -> menuToString' (1, m_)
      end

    let rec printStats () =
      let nopen = 0 in
      let nsolved = 0 in
      begin
        print "Statistics:\n\n";
        begin
          print (("Number of goals : " ^ Int.toString (nopen + nsolved)) ^ "\n");
          begin
            print (("     open goals : " ^ Int.toString nopen) ^ "\n");
            print (("   solved goals : " ^ Int.toString nsolved) ^ "\n")
          end
        end
      end

    let rec printmenu () =
      begin match !focus_ with
      | [] -> abort "QED"
      | S.State (w_, psi_, p_, f_) :: r_ -> begin
          print "\n=======================";
          begin
            print "\n= META THEOREM PROVER =\n";
            begin
              print (TomegaPrint.ctxToString psi_);
              begin
                print "\n-----------------------\n";
                begin
                  print (TomegaPrint.forToString (psi_, f_));
                  begin
                    print "\n-----------------------\n";
                    begin
                      print (TomegaPrint.prgToString (psi_, p_));
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
      | S.StateLF (I.EVar (r, g_, v_, cs_) as x_) :: r_ -> begin
          print "\n=======================";
          begin
            print "\n=== THEOREM PROVER ====\n";
            begin
              print (Print.ctxToString (I.Null, g_));
              begin
                print "\n-----------------------\n";
                begin
                  print (Print.expToString (g_, v_));
                  begin
                    print "\n-----------------------\n";
                    begin
                      print (Print.expToString (g_, x_));
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

    let rec menu () =
      begin match !focus_ with
      | [] -> print "Please initialize first\n"
      | S.State (w_, psi_, p_, f_) :: _ ->
          let xs_ = S.collectT p_ in
          let f1_ =
            map
              (function
                | T.EVar (psi_, r, f_, tc_, tCs_, x_) -> begin
                    Names.varReset I.Null;
                    S.Focus
                      ( T.EVar (TomegaPrint.nameCtx psi_, r, f_, tc_, tCs_, x_),
                        w_ )
                  end)
              xs_
          in
          let ys_ = S.collectLF p_ in
          let f2_ = map (function y_ -> S.FocusLF y_) ys_ in
          let rec splitMenu = function
            | [] -> []
            | operators :: l ->
                map (function o_ -> Split o_) operators @ splitMenu l
          in
          let _ = Global.doubleCheck := true in
          let rec introMenu = function
            | [] -> []
            | Some oper :: l -> Introduce oper :: introMenu l
            | None :: l -> introMenu l
          in
          let intro = introMenu (map Introduce.expand f1_) in
          let fill =
            foldr
              (function
                | s_, l -> l @ map (function o_ -> Fill o_) (Fill.expand s_))
              [] f2_
          in
          let rec elimMenu = function
            | [] -> []
            | operators :: l ->
                map (function o_ -> Elim o_) operators @ elimMenu l
          in
          let elim = elimMenu (map Elim.expand f1_) in
          let split = splitMenu (map Split.expand f1_) in
          menu_ := Some (intro @ split @ fill @ elim)
      | S.StateLF y_ :: _ ->
          let ys_ = Abstract.collectEVars (I.Null, (y_, I.id), []) in
          let f2_ = map (function y_ -> S.FocusLF y_) ys_ in
          let fill =
            foldr
              (function
                | s_, l -> l @ map (function o_ -> Fill o_) (Fill.expand s_))
              [] f2_
          in
          menu_ := Some fill
      end

    let rec select k =
      let rec select' = function
        | k, [] -> abort "No such menu item"
        | 1, Split o_ :: _ -> Timers.time Timers.splitting Split.apply o_
        | 1, Introduce o_ :: _ -> Introduce.apply o_
        | 1, Elim o_ :: _ -> Elim.apply o_
        | 1, Fill o_ :: _ -> Timers.time Timers.filling Fill.apply o_
        | k, _ :: m_ -> select' (k - 1, m_)
      in
      begin match !menu_ with
      | None -> raise (Error "No menu defined")
      | Some m_ -> (
          try
            begin
              select' (k, m_);
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

    let rec init names =
      let _ = TomegaPrint.evarReset () in
      let cL =
        map
          (function
            | x -> valOf (Names.constLookup (valOf (Names.stringToQid x))))
          names
      in
      let f_ = convertFor cL in
      let ws_ = map W.lookup cL in
      let rec select c = try Lambda.Order.selLookup c with _ -> Lambda.Order.Lex [] in
      let tc_ = Tomega.transformTC (I.Null, f_, map select cL) in
      let (w_ :: _) = ws_ in
      let _ = focus_ := [ S.init (f_, w_) ] in
      let p_ =
        begin match !focus_ with
        | [] -> abort "Initialization of proof goal failed\n"
        | S.State (w_, psi_, p_, f_) :: _ -> p_
        end
      in
      let xs_ = S.collectT p_ in
      let f_ =
        map
          (function
            | T.EVar (psi_, r, f_, tc_, tCs_, x_) -> begin
                Names.varReset I.Null;
                S.Focus
                  (T.EVar (TomegaPrint.nameCtx psi_, r, f_, tc_, tCs_, x_), w_)
              end)
          xs_
      in
      let (ofix_ :: []) = map (function f -> FixedPoint.expand (f, tc_)) f_ in
      let _ = FixedPoint.apply ofix_ in
      let _ = normalize () in
      let _ = menu () in
      let _ = printmenu () in
      ()

    let rec focus n =
      begin match !focus_ with
      | [] -> print "Please initialize first\n"
      | S.State (w_, psi_, p_, f_) :: _ ->
          let rec findIEVar = function
            | [] -> raise (Error ("cannot focus on " ^ n))
            | y_ :: ys_ -> begin
                if Names.evarName (T.coerceCtx psi_, y_) = n then begin
                  focus_ := S.StateLF y_ :: !focus_;
                  begin
                    normalize ();
                    begin
                      menu ();
                      printmenu ()
                    end
                  end
                end
                else findIEVar ys_
              end
          in
          let rec findTEVar = function
            | [] -> findIEVar (S.collectLF p_)
            | (T.EVar (psi_, r, f_, tc_, tCs_, y_) as x_) :: xs_ -> begin
                if Names.evarName (T.coerceCtx psi_, y_) = n then begin
                  focus_ :=
                    S.State (w_, TomegaPrint.nameCtx psi_, x_, f_) :: !focus_;
                  begin
                    normalize ();
                    begin
                      menu ();
                      printmenu ()
                    end
                  end
                end
                else findTEVar xs_
              end
          in
          findTEVar (S.collectT p_)
      | S.StateLF u_ :: _ -> begin
          match Names.getEVarOpt n with
          | None -> raise (Error ("cannot focus on " ^ n))
          | Some y_ -> begin
              focus_ := S.StateLF y_ :: !focus_;
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

    let rec return () =
      begin match !focus_ with
      | s_ :: [] -> begin if S.close s_ then print "[Q.E.D.]\n" else () end
      | s_ :: rest_ -> begin
          focus_ := rest_;
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
