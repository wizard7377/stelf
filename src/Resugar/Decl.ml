(** Declaration lists and contexts.

    Thin wrappers over {!Term}: the recursion that matters is there, because
    [exp] and [dec] are mutually recursive and cannot be split apart. What is
    here is the bookkeeping for sequences of binders, each of which scopes over
    the ones after it. *)

module I = Intsyn.IntSyn

module Make (Cst : Cst.CST) = struct
  module T = Term.Make (Cst)

  let dec_list = T.dec_list
  let dec_list_sub = T.dec_list_sub

  (* [IntSyn.dctx] is snoc-ordered; a declaration list is written outermost
     first, so the context has to be reversed on the way out. *)
  let rec to_dec_list acc = function
    | I.Null -> acc
    | I.Decl (g, d) -> to_dec_list (d :: acc) g

  let ctx (opts : Options.t) (g0 : I.dctx) (g : I.dctx) : Cst.decl list =
    T.dec_list opts g0 (to_dec_list [] g)
end
