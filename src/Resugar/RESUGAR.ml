(** Resugaring: internal syntax back to concrete syntax.

    This is the first half of term output. It undoes what elaboration did -- de
    Bruijn indices become names, constant ids become qualified names, implicit
    arguments disappear, under-applied operators are eta-expanded -- and stops
    there. It makes no typographic decisions at all: no parentheses, no
    precedence, no choice of [%pi] versus [{x A}], no line breaks, no identifier
    escaping. Those belong to [Pretty], which shares no code with this module.

    The split is what makes a library mode possible: a caller who wants the
    resugared term as a value rather than as text calls {!RESUGAR.exp} and
    stops.

    Resugaring is {e total}. The parts of the internal syntax that have no STELF
    surface form -- the kind universe, explicit substitutions, block
    projections, the depth and length cutoffs -- come out as internal-tag nodes,
    which print but deliberately do not parse. *)

module I = Intsyn.IntSyn

module type RESUGAR = sig
  module Cst : Cst.CST

  type cnstr_form =
    | Solved  (** A constraint that has already been discharged. *)
    | Eqn of Cst.term * Cst.term  (** [U = V]. *)
    | Fgn of Cst.term list  (** A foreign constraint's component terms. *)

  val exp : Options.t -> I.dctx -> I.exp -> Cst.term
  (** [exp opts g u] resugars [u] in naming context [g]. *)

  val exp_sub : Options.t -> I.dctx -> I.exp * I.sub -> Cst.term
  (** As {!exp}, for a term paired with a pending substitution. *)

  val spine : Options.t -> I.dctx -> I.spine -> Cst.term list

  val dec : Options.t -> I.dctx -> I.dec -> Cst.decl
  (** Resugar one binder. Does {e not} assign it a name: a caller walking into
      the binder's scope must run [Names.decLUName] first, or successive binders
      collide. *)

  val dec_sub : Options.t -> I.dctx -> I.dec * I.sub -> Cst.decl
  val dec_list : Options.t -> I.dctx -> I.dec list -> Cst.decl list
  val ctx : Options.t -> I.dctx -> I.dctx -> Cst.decl list

  val con_dec : Options.t -> hide:bool -> I.conDec -> Cst.cmd
  (** [con_dec opts ~hide d] resugars a signature entry as the command that
      would declare it. [hide:true] suppresses the leading implicit binders.

      The target is [Cst.cmd], not [Cst.conDec]: the latter carries no implicit
      count and no way to tell a [%sort] from a [%term]. *)

  val cnstr : Options.t -> I.cnstr -> cnstr_form
  val cnstrs : Options.t -> I.cnstr list -> cnstr_form list

  val worlds : Options.t -> I.cid list -> Cst.symbol list
  (** Takes the constant ids directly rather than a [Tomega.worlds]: a world is
      a list of block labels, and unwrapping it at the call site keeps
      resugaring independent of the proof-term layer. *)

  val evar_inst : Options.t -> (I.exp * string) list -> (string * Cst.term) list
  (** Resugar an existential-variable instantiation, abstracting each term over
      the context its variable was created in. *)
end
