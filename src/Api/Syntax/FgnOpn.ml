open Basis

module type FGN_OPN = sig
  module Common : Common.COMMON

  type nonrec csid = Common.Cid.t
  type nonrec rep = exn
  type arg
  type result
  type nonrec func = rep -> arg -> result

  val install : csid * func -> unit
  val apply : csid * rep -> arg -> result
end

module FgnOpnTable
    (Common : Common.COMMON)
    (FgnOpnTable__0 : sig
      (* Extensible operation on foreign matter *)
      (* Author: Aleksey Kliger *)
      type arg
      type result
    end) :
  FGN_OPN
    with type arg = FgnOpnTable__0.arg
     and type result = FgnOpnTable__0.result
     and module Common = Common = struct
  open FgnOpnTable__0
  module Common = Common

  type nonrec csid = Common.Cid.t
  type nonrec rep = exn
  type nonrec arg = arg
  type nonrec result = result
  type nonrec func = rep -> arg -> result
  type nonrec table = (csid, func) Hashtbl.t

  exception CSfunNotInstalled of csid

  let initializeTable _tbl = Hashtbl.create 53
  let table : table = initializeTable ()
  let install (csid, f) = Hashtbl.replace table csid f

  let apply (csid, rep) =
    match Hashtbl.find_opt table csid with
    | Some f -> f rep
    | None -> raise (CSfunNotInstalled csid)
end

module type S = sig
  module Common : Common.COMMON
  module Ast : Ast_intf.AST with module Common = Common

  open Ast
  (** Raised when the global signature exceeds its maximum size. *)

  (** Standard operations on foreign expressions.

      Each sub-module is a dispatch table ({!FGN_OPN}): constraint solvers
      register handlers via [install], and the main system invokes them via
      [apply] using the expression's {!csid}. *)
  module FgnExpStd : sig
    (** Convert a foreign expression to an equivalent internal {!exp}. *)
    module ToInternal : FGN_OPN with type arg = unit and type result = exp

    (** Apply a transformation function to all internal subterms of a foreign
        expression, returning the rebuilt expression. *)
    module Map : FGN_OPN with type arg = exp -> exp and type result = exp

    (** Apply an effectful function to all internal subterms of a foreign
        expression (e.g., for occurs-check or trail recording). *)
    module App : FGN_OPN with type arg = exp -> unit and type result = unit

    (** Test whether a foreign expression is equal to a given internal
        expression. *)
    module EqualTo : FGN_OPN with type arg = exp and type result = bool

    (** Attempt to unify a foreign expression with an internal expression in a
        given context. Returns {!fgnUnify} indicating success or failure. *)
    module UnifyWith :
      FGN_OPN with type arg = dec ctx * exp and type result = fgnUnify

    val fold : Ast.csid * fgnExp -> (exp * 'a -> 'a) -> 'a -> 'a
    (** [fold (csid, fe) f init] folds [f] over the internal subterms of foreign
        expression [fe], threading accumulator [init]. *)
  end

  (** Standard operations on foreign constraints.

      Like {!FgnExpStd}, each sub-module dispatches to the appropriate
      constraint solver based on the constraint's {!csid}. *)
  module FgnCnstrStd : sig
    (** Convert a foreign constraint to a list of internal equations [(G, U)]
        representing the constraint's content. *)
    module ToInternal :
      FGN_OPN with type arg = unit and type result = (dec ctx * exp) list

    (** Attempt to wake up (re-activate) a delayed foreign constraint. Returns
        [true] if the constraint can now be solved. *)
    module Awake : FGN_OPN with type arg = unit and type result = bool

    (** Attempt to simplify a foreign constraint. Returns [true] if
        simplification made progress. *)
    module Simplify : FGN_OPN with type arg = unit and type result = bool
  end
end

module FgnOpn
    (Common : Common.COMMON)
    (Ast : Ast_intf.AST with module Common = Common) :
  S with module Common = Common and module Ast = Ast = struct
  open Ast
  module Ast = Ast
  module Common = Common

  (*  exception Error of string              raised if out of space      *)
  module FgnExpStd = struct
    module ToInternal =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = unit
          type nonrec result = Ast.exp
        end)

    module Map =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = Ast.exp -> Ast.exp
          type nonrec result = exp
        end)

    module App =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = Ast.exp -> unit
          type nonrec result = unit
        end)

    module EqualTo =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = Ast.exp
          type nonrec result = bool
        end)

    module UnifyWith =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = dec ctx * exp
          type nonrec result = fgnUnify
        end)

    let fold (csfe : Ast.csid * exn) (f : Ast.exp * 'a -> 'a) (b : 'a) : 'a =
      let r = ref b in
      let g u_ = r := f (u_, !r) in
      App.apply csfe g;
      !r
  end

  module FgnCnstrStd = struct
    module ToInternal =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = unit
          type nonrec result = (dec ctx * exp) list
        end)

    module Awake =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = unit
          type nonrec result = bool
        end)

    module Simplify =
      FgnOpnTable
        (Common)
        (struct
          type nonrec arg = unit
          type nonrec result = bool
        end)
  end
end
