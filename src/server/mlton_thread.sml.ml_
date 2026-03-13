open! Basis

(* Construct a 20041109-workalike MLton.Thread for previous MLton versions *)
module MLton = struct
  open MLton

  module Thread = struct
    open MLton.Thread

    let rec prepare (f, x) = f
  end
end
