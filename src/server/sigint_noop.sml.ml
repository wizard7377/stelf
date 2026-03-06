open! Basis;;
module SigINT : SIGINT =
  struct
    let rec interruptLoop ((loop : unit -> unit)) = loop ();;
    end;;