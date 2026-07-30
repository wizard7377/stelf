(** Normalising CSTs so two of them can be compared.

    [Cst.equal_term] is structural and locations are constructor fields, so a
    term parsed from [f x] and the same term parsed from [f  x] are unequal.
    Rewriting every location to [ghost] is what makes round-trip comparison
    meaningful at all.

    {!term} does only that, and is the right comparison for terms that came from
    source: printing a parsed term must reproduce it exactly.

    {!denote} additionally collapses the two rewrites the printer is {e obliged}
    to make, and is the right comparison for hand-built trees. Both are
    deliberately separate: using {!denote} everywhere would stop the source
    suite from noticing a printer that reached for [%val] when it did not have
    to. *)

module C = Modern.Modern.Cst
module V = C.View
module T = V.Term

let g : C.loc = V.Loc.review V.Loc.Ghost

(* [denote] folds in the two lossy steps the grammar forces on the printer:

   - a name that cannot be written bare -- one that is namespaced, is in the
     wrong lexical class, or carries a declared fixity it is not being applied
     at -- has to go out as [%val], and [%val] parses to [Qualified]. There is
     no other spelling, so [Lowercase]/[Uppercase]/[Qualified _ Val] are
     identified. [%abs] stays distinct: it resolves differently.
   - [Foreign] is transparent by construction, so it is erased. *)
let rec go ~(denote : bool) (t : C.term) : C.term =
  let self = go ~denote in
  match T.view t with
  | T.Lowercase (_, s) ->
      if denote then T.review (T.Qualified (g, s, C.Val))
      else T.review (T.Lowercase (g, s))
  | T.Uppercase (_, s) ->
      if denote then T.review (T.Qualified (g, s, C.Val))
      else T.review (T.Uppercase (g, s))
  | T.Qualified (_, s, f) -> T.review (T.Qualified (g, s, f))
  | T.Text (_, s) -> T.review (T.Text (g, s))
  | T.ExistVar (_, n) -> T.review (T.ExistVar (g, n))
  | T.FreeVar (_, n) -> T.review (T.FreeVar (g, n))
  | T.Omitted _ -> T.review (T.Omitted g)
  | T.Typ _ -> T.review (T.Typ g)
  | T.MacroParam (_, l, n) -> T.review (T.MacroParam (g, l, n))
  | T.Pi (_, ds, b) -> T.review (T.Pi (g, List.map (decl ~denote) ds, self b))
  | T.Lam (_, ds, b) -> T.review (T.Lam (g, List.map (decl ~denote) ds, self b))
  | T.App (_, h, args) -> T.review (T.App (g, self h, List.map self args))
  | T.HasType (_, tm, ty) -> T.review (T.HasType (g, self tm, self ty))
  | T.Arrow (_, a, b) -> T.review (T.Arrow (g, self a, self b))
  (* [Term.view] never yields [BackArrow] -- [review] folds it into [Arrow]
     with the operands swapped -- but the case has to be here for the match to
     be exhaustive. *)
  | T.BackArrow (_, a, b) -> T.review (T.Arrow (g, self b, self a))
  | T.Local (_, ns, b) -> T.review (T.Local (g, ns, self b))
  | T.Foreign (_, b) ->
      if denote then self b else T.review (T.Foreign (g, self b))
  | T.Internal (_, tag, ks) -> T.review (T.Internal (g, tag, List.map self ks))

and decl ~(denote : bool) (d : C.decl) : C.decl =
  let names, ty =
    match V.Decl.view d with
    | V.Decl.Decl1 (_, names, ty, _) -> (names, ty)
    | V.Decl.Decl0 (_, names, ty) -> (names, ty)
  in
  (* [Decl1]'s fourth field is a view artifact: [Decl.view] always fabricates
     [Omitted ghost] there and [Decl.review] discards it. *)
  V.Decl.review (V.Decl.Decl1 (g, names, go ~denote ty, T.review (T.Omitted g)))

let term (t : C.term) : C.term = go ~denote:false t
let denote (t : C.term) : C.term = go ~denote:true t
let equal (a : C.term) (b : C.term) : bool = C.equal_term (term a) (term b)

let equal_denotation (a : C.term) (b : C.term) : bool =
  C.equal_term (denote a) (denote b)
