# 1 "src/m2/skolem.sig.ml"
open! Basis;;
(* Skolem administration *);;
(* Author: Carsten Schuermann *);;
module type SKOLEM = sig
                     (*! structure IntSyn : INTSYN !*)
                     val install : IntSyn.cid list -> unit
                     end;;
(* signature SKOLEM *);;
# 1 "src/m2/skolem.fun.ml"
open! Basis;;
module Skolem(Skolem__0: sig
                         (* Skolem constant administration *)
                         (* Author: Carsten Schuermann *)
                         module Global : GLOBAL
                         (*! structure IntSyn' : INTSYN !*)
                         module Whnf : WHNF
                         (*! sharing Whnf.IntSyn = IntSyn' !*)
                         module Abstract : ABSTRACT
                         (*! sharing Abstract.IntSyn = IntSyn' !*)
                         module IndexSkolem : INDEX
                         (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
                         module ModeTable : MODETABLE
                         (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                         module Print : PRINT
                         (*! sharing Print.IntSyn = IntSyn' !*)
                         module Compile : COMPILE
                         (*! sharing Compile.IntSyn = IntSyn' !*)
                         module Timers : TIMERS
                         module Names : NAMES
                         end) : SKOLEM
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module M = ModeSyn;;
        let rec installSkolem (name, imp, (v_, mS), l_) =
          let rec spine =
            function 
                     | 0 -> I.nil_
                     | n
                         -> (I.App
                             ((I.Root ((I.BVar n), I.nil_)), spine (n - 1)))
            in let rec installSkolem' =
                 function 
                          | (d, (I.Pi ((d_, dp_), v_), mS), s, k)
                              -> begin
                                 match mS
                                 with 
                                      | M.Mapp (M.Marg (plus_, _), mS')
                                          -> installSkolem'
                                             (d + 1, (v_, mS'), I.dot1 s,
                                              function 
                                                       | v_
                                                           -> k
                                                              (Abstract.piDepend
                                                               ((Whnf.normalizeDec
                                                                 (d_, s),
                                                                 I.meta_),
                                                                v_)))
                                      | M.Mapp (M.Marg (minus_, _), mS')
                                          -> let I.Dec (_, v'_) = d_
                                               in let v''_ =
                                                    k
                                                    (Whnf.normalize (v'_, s))
                                                    in let name' =
                                                         Names.skonstName
                                                         (name ^ "#")
                                                         in let sd_ =
                                                              (I.SkoDec
                                                               (name', None,
                                                                imp, v''_,
                                                                l_))
                                                              in let sk =
                                                                   I.sgnAdd
                                                                   sd_
                                                                   in 
                                                                   let h_ =
                                                                    (I.Skonst
                                                                    sk)
                                                                    in 
                                                                    let _ =
                                                                    IndexSkolem.install
                                                                    I.ordinary_
                                                                    h_
                                                                    in 
                                                                    let _ =
                                                                    Names.installConstName
                                                                    sk
                                                                    in 
                                                                    let _ =
                                                                    Timers.time
                                                                    Timers.compiling
                                                                    Compile.install
                                                                    I.ordinary_
                                                                    sk
                                                                    in 
                                                                    let s_ =
                                                                    spine d
                                                                    in 
                                                                    let _ =
                                                                    begin
                                                                    if
                                                                    (!
                                                                    Global.chatter)
                                                                    >= 3 then
                                                                    TextIO.print
                                                                    ((Print.conDecToString
                                                                    sd_) ^
                                                                    "\n")
                                                                    else ()
                                                                    end
                                                                    in 
                                                                    installSkolem'
                                                                    (d,
                                                                    (v_, mS'),
                                                                    (I.Dot
                                                                    ((I.Exp
                                                                    ((I.Root
                                                                    (h_, s_)))),
                                                                    s)), k)
                                 end
                          | (_, (I.Uni _, mnil_), _, _) -> ()
                 in installSkolem' (0, (v_, mS), I.id, function 
                                                                | v_ -> v_);;
        let rec install =
          function 
                   | [] -> ()
                   | (a :: aL)
                       -> let I.ConDec (name, _, imp, _, v_, l_) =
                            I.sgnLookup a
                            in let Some mS = ModeTable.modeLookup a
                                 in let _ =
                                      installSkolem
                                      (name, imp, (v_, mS), I.type_)
                                      in install aL;;
        end;;
    (*! structure CompSyn = Compile.CompSyn !*);;
    (* installSkolem (name, k, (V, mS), L) =

       Invariant:
            name is the name of a theorem
       and  imp is the number of implicit arguments
       and  V is its term together with the mode assignment mS
       and  L is the level of the declaration

       Effects: New Skolem constants are generated, named, and indexed
    *);;
    (* spine n = S'

           Invariant:
           S' = n; n-1; ... 1; Nil
        *);;
    (* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *);;
    (*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *);;
    (*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *);;
    (* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for all theorems are generated, named, and indexed
    *);;
    let install = install;;
    end;;
(*! sharing Names.IntSyn = IntSyn' !*);;
(* local *);;
(* functor Skolem *);;
# 1 "src/m2/skolem.sml.ml"
