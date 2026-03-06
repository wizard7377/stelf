open! Basis;;
(* Meta Theorem Prover Version 1.3 *);;
(* Author: Carsten Schuermann *);;
module MTProver(MTProver__0: sig
                             module MTPGlobal : MTPGLOBAL
                             (*! structure IntSyn' : INTSYN !*)
                             (*! structure FunSyn : FUNSYN !*)
                             (*! sharing FunSyn.IntSyn = IntSyn' !*)
                             module StateSyn : STATESYN
                             (*! sharing IntSyn = IntSyn' !*)
                             (*! sharing StateSyn.FunSyn = FunSyn !*)
                             module Order : ORDER
                             (*! sharing Order.IntSyn = IntSyn' !*)
                             module MTPInit : MTPINIT
                             (*! sharing MTPInit.FunSyn = FunSyn !*)
                             module MTPStrategy : MTPSTRATEGY
                             module RelFun : RELFUN
                             end) : PROVER
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module F = FunSyn;;
        module S = StateSyn;;
        let openStates : S.state_ list ref = ref [];;
        let solvedStates : S.state_ list ref = ref [];;
        let rec transformOrder' =
          function 
                   | (g_, Order.Arg k)
                       -> let k' = ((I.ctxLength g_) - k) + 1
                            in let I.Dec (_, v_) = I.ctxDec (g_, k')
                                 in (S.Arg
                                     (((I.Root ((I.BVar k'), I.nil_)), I.id),
                                      (v_, I.id)))
                   | (g_, Order.Lex os_)
                       -> (S.Lex
                           (map
                            (function 
                                      | o_ -> transformOrder' (g_, o_))
                            os_))
                   | (g_, Order.Simul os_)
                       -> (S.Simul
                           (map
                            (function 
                                      | o_ -> transformOrder' (g_, o_))
                            os_));;
        let rec transformOrder =
          function 
                   | (g_, F.All (F.Prim d_, f_), os_)
                       -> (S.All
                           (d_, transformOrder ((I.Decl (g_, d_)), f_, os_)))
                   | (g_, F.And (f1_, f2_), (o_ :: os_))
                       -> (S.And
                           (transformOrder (g_, f1_, [o_]),
                            transformOrder (g_, f2_, os_)))
                   | (g_, F.Ex _, (o_ :: [])) -> transformOrder' (g_, o_)
                   | (g_, true_, (o_ :: [])) -> transformOrder' (g_, o_);;
        let rec select c = try Order.selLookup c with 
                                                      | _ -> (Order.Lex []);;
        let rec error s = raise ((Error s));;
        let rec reset () = begin
                             openStates := [];solvedStates := []
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
        let rec insertState s_ = openStates := ((s_ :: ! openStates));;
        let rec cLToString =
          function 
                   | [] -> ""
                   | (c :: []) -> I.conDecName (I.sgnLookup c)
                   | (c :: l_)
                       -> ((I.conDecName (I.sgnLookup c)) ^ ", ") ^
                            (cLToString l_);;
        let rec init (k, ((c :: _) as cL)) =
          let _ = MTPGlobal.maxFill := k
            in let _ = reset ()
                 in let cL' = try Order.closure c with 
                                                       | Order.Error _ -> cL
                      in let f_ = RelFun.convertFor cL
                           in let o_ =
                                transformOrder (I.null_, f_, map select cL)
                                in begin
                                if equiv (cL, cL') then
                                List.app
                                (function 
                                          | s_ -> insertState s_)
                                (MTPInit.init (f_, o_)) else
                                raise
                                ((Error
                                  (("Theorem by simultaneous induction not correctly stated:"
                                      ^ "\n            expected: ")
                                     ^ (cLToString cL'))))
                                end;;
        let rec auto () =
          let (Open, solvedStates') =
            try MTPStrategy.run (! openStates)
            with 
                 | Splitting.Error s -> error ("Splitting Error: " ^ s)
                 | Filling.Error s -> error ("Filling Error: " ^ s)
                 | Recursion.Error s -> error ("Recursion Error: " ^ s)
                 | timeOut_
                     -> error
                        "A proof could not be found -- Exceeding Time Limit\n"
            in let _ = openStates := Open
                 in let _ =
                      solvedStates := ((! solvedStates) @ solvedStates')
                      in begin
                      if (List.length (! openStates)) > 0 then
                      raise ((Error "A proof could not be found")) else ()
                      end;;
        let rec print () = ();;
        let rec install _ = ();;
        end;;
    (* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Twelf  (see also functor below) *);;
    (* List of open states *);;
    (* List of solved states *);;
    (* last case: no existentials---order must be trivial *);;
    (* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *);;
    (* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *);;
    (* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *);;
    (* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *);;
    (* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *);;
    (* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *);;
    (* if no termination ordering given! *);;
    (* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *);;
    let init = init;;
    let auto = auto;;
    let print = print;;
    let install = install;;
    end;;
(*! sharing RelFun.FunSyn = FunSyn !*);;
(* local *);;
(* functor MTProver *);;
module CombiProver(CombiProver__1: sig
                                   module MTPGlobal : MTPGLOBAL
                                   (*! structure IntSyn' : INTSYN !*)
                                   module ProverOld : PROVER
                                   (*! sharing ProverOld.IntSyn = IntSyn' !*)
                                   module ProverNew : PROVER
                                   end) : PROVER
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    exception Error of string ;;
    let rec he f =
      try f ()
      with 
           | ProverNew.Error s -> raise ((Error s))
           | ProverOld.Error s -> raise ((Error s));;
    open!
      struct
        let rec init args_ =
          he
          (function 
                    | ()
                        -> begin
                           match ! MTPGlobal.prover
                           with 
                                | new_ -> ProverNew.init args_
                                | old_ -> ProverOld.init args_
                           end);;
        let rec auto args_ =
          he
          (function 
                    | ()
                        -> begin
                           match ! MTPGlobal.prover
                           with 
                                | new_ -> ProverNew.auto args_
                                | old_ -> ProverOld.auto args_
                           end);;
        let rec print args_ =
          he
          (function 
                    | ()
                        -> begin
                           match ! MTPGlobal.prover
                           with 
                                | new_ -> ProverNew.print args_
                                | old_ -> ProverOld.print args_
                           end);;
        let rec install args_ =
          he
          (function 
                    | ()
                        -> begin
                           match ! MTPGlobal.prover
                           with 
                                | new_ -> ProverNew.install args_
                                | old_ -> ProverOld.install args_
                           end);;
        end;;
    let init = init;;
    let auto = auto;;
    let print = print;;
    let install = install;;
    end;;
(*! sharing ProverNew.IntSyn = IntSyn' !*);;
(* functor CombiProver *);;