open! Weaken;;
open! Basis;;
(* Weakening substitutions for meta substitutions *);;
(* Author: Carsten Schuermann *);;
module FunWeaken(FunWeaken__0: sig module Weaken : WEAKEN end) : FUNWEAKEN =
  struct
    (*! structure FunSyn = FunSyn' !*);;
    open!
      struct
        module F = FunSyn;;
        module I = IntSyn;;
        let rec strengthenPsi =
          function 
                   | (null_, s) -> (I.null_, s)
                   | (I.Decl (psi_, F.Prim d_), s)
                       -> let (psi'_, s') = strengthenPsi (psi_, s)
                            in ((I.Decl
                                 (psi'_,
                                  (F.Prim (Weaken.strengthenDec (d_, s'))))),
                                I.dot1 s')
                   | (I.Decl (psi_, F.Block (F.CtxBlock (l, g_))), s)
                       -> let (psi'_, s') = strengthenPsi (psi_, s)
                            in let (g''_, s'') =
                                 Weaken.strengthenCtx (g_, s')
                                 in ((I.Decl
                                      (psi'_,
                                       (F.Block ((F.CtxBlock (l, g''_)))))),
                                     s'');;
        let rec strengthenPsi' =
          function 
                   | ([], s) -> ([], s)
                   | ((F.Prim d_ :: psi_), s)
                       -> let d'_ = Weaken.strengthenDec (d_, s)
                            in let s' = I.dot1 s
                                 in let (psi''_, s'') =
                                      strengthenPsi' (psi_, s')
                                      in (((F.Prim d'_) :: psi''_), s'')
                   | ((F.Block (F.CtxBlock (l, g_)) :: psi_), s)
                       -> let (g'_, s') = Weaken.strengthenCtx (g_, s)
                            in let (psi''_, s'') = strengthenPsi' (psi_, s')
                                 in (((F.Block ((F.CtxBlock (l, g'_))))
                                      :: psi''_),
                                     s'');;
        end;;
    (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *);;
    (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *);;
    let strengthenPsi = strengthenPsi;;
    let strengthenPsi' = strengthenPsi';;
    end;;
(*! structure FunSyn' : FUNSYN !*);;
(*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*);;
(* functor FunWeaken *);;