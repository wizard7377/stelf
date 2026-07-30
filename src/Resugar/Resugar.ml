(** Resugaring: internal syntax back to concrete syntax. See {!RESUGAR}. *)

module type RESUGAR = RESUGAR.RESUGAR

module Options = Options
module Term = Term
module Decl = Decl
module ConDec = ConDec

(** Assembles the pieces into the full interface.

    A functor over [Cst] only, and concrete on [IntSyn]/[Whnf]/[Names]: there is
    exactly one internal syntax in the program, and neither [Whnf.etaExpandRoot]
    nor [Names.decLUName] has a functor form to abstract over. [Cst] stays a
    parameter because there really are several instances -- the default one,
    [Modern]'s, and [Pal]'s. *)
module Make_Resugar (Cst : Cst.CST) : RESUGAR with module Cst = Cst = struct
  module Cst = Cst
  module Tm = Term.Make (Cst)
  module Dl = Decl.Make (Cst)
  module Cd = ConDec.Make (Cst)

  type cnstr_form = Cd.cnstr_form =
    | Solved
    | Eqn of Cst.term * Cst.term
    | Fgn of Cst.term list

  let exp = Tm.exp
  let exp_sub opts g_ us = Tm.exp_sub opts g_ 0 us
  let spine = Tm.spine
  let dec = Tm.dec
  let dec_sub = Tm.dec_sub
  let dec_list = Tm.dec_list
  let ctx = Dl.ctx
  let con_dec = Cd.con_dec
  let cnstr = Cd.cnstr
  let cnstrs = Cd.cnstrs
  let worlds = Cd.worlds
  let evar_inst = Cd.evar_inst
end
