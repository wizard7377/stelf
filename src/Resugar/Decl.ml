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
    | I.Decl (g_, d_) -> to_dec_list (d_ :: acc) g_

  let ctx (opts : Options.t) (g0_ : I.dctx) (g_ : I.dctx) : Cst.decl list =
    T.dec_list opts g0_ (to_dec_list [] g_)
end
