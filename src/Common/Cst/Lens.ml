module Make_Lens (L : LENS.S) : LENS.LENS with type t = L.t and type u = L.u =
struct
  type t = L.t
  type u = L.u

  let review = L.review
  let view = L.view
  let ( !> ) = view
  let ( !< ) = review
end
