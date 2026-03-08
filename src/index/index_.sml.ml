open! Basis

module Index = MakeIndex (struct
  module Global = Global
  module Queue = Queue
end)
(*! structure IntSyn' = IntSyn !*)
(* IndexSkolem commented out to break cycle with index_skolem *)
(*
module IndexSkolem = (Index_skolem.MakeIndexSkolem)(struct
                                     module Global = Global;;
                                     module Queue = Queue;;
                                     end);;
*)
(*! structure IntSyn' = IntSyn !*)
