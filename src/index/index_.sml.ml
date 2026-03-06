open! Basis;;
module Index = (Index)(struct
                         module Global = Global;;
                         module Queue = Queue;;
                         end);;
(*! structure IntSyn' = IntSyn !*);;
module IndexSkolem = (IndexSkolem)(struct
                                     module Global = Global;;
                                     module Queue = Queue;;
                                     end);;
(*! structure IntSyn' = IntSyn !*);;