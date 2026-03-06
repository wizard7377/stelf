open! Basis;;
(* fquery: Executing logic programs via functional interpretation *);;
(* Author: Carsten Schuermann *);;
module Fquery(Fquery__0: sig
                         module Global : GLOBAL
                         module Names : NAMES
                         module ReconQuery : RECON_QUERY
                         module Timers : TIMERS
                         module Print : PRINT
                         end) : FQUERY
  =
  struct
    module ExtQuery = ReconQuery;;
    exception AbortQuery of string ;;
    module I = IntSyn;;
    module T = Tomega;;
    module W = WorldSyn;;
    module P = Paths;;
    (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *);;
    let rec evarInstToString xs_ = begin
      if (! Global.chatter) >= 3 then Print.evarInstToString xs_ else "" end;;
    (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *);;
    let rec expToString gu_ = begin
      if (! Global.chatter) >= 3 then Print.expToString gu_ else "" end;;
    let rec lower =
      function 
               | (0, g_, v_) -> (g_, v_)
               | (n, g_, I.Pi ((d_, _), v_))
                   -> lower (n - 1, (I.Decl (g_, d_)), v_);;
    let rec run (quy, Paths.Loc (fileName, r)) =
      let (v_, optName, xs_) =
        ReconQuery.queryToQuery (quy, (Paths.Loc (fileName, r)))
        in let _ = begin
             if (! Global.chatter) >= 3 then print "%fquery" else () end
             in let _ = begin
                  if (! Global.chatter) >= 3 then print " " else () end
                  in let _ = begin
                       if (! Global.chatter) >= 3 then
                       print
                       ((Timers.time
                         Timers.printing
                         expToString
                         (IntSyn.null_, v_)) ^ ".\n")
                       else () end
                       in let (k, v1_) = Abstract.abstractDecImp v_
                            in let (g_, v2_) = lower (k, I.null_, v1_)
                                 in let a = I.targetFam v2_
                                      in let w_ = W.lookup a
                                           in let v3_ =
                                                Worldify.worldifyGoal
                                                (g_, v2_)
                                                in let _ =
                                                     TypeCheck.typeCheck
                                                     (g_,
                                                      (v3_, (I.Uni I.type_)))
                                                     in let p_ =
                                                          Converter.convertGoal
                                                          (T.embedCtx g_,
                                                           v3_)
                                                          in let v_ =
                                                               Timers.time
                                                               Timers.delphin
                                                               Opsem.evalPrg
                                                               p_
                                                               in print
                                                                  (("Delphin: "
                                                                    ^
                                                                    (TomegaPrint.prgToString
                                                                    (I.null_,
                                                                    v_))) ^
                                                                    "\n")
                                                               (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)(* times itself *)(* G |- V'' : type *);;
    end;;
(* functor Solve *);;