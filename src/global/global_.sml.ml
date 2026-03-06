open! Basis;;
(* Global parameters *);;
(* Author: Frank Pfenning *);;
module Global : GLOBAL =
  struct
    let chatter = ref 3;;
    let style = ref 0;;
    let maxCid = 19999;;
    let maxMid = 999;;
    let maxCSid = 49;;
    let doubleCheck = ref false;;
    let unsafe = ref false;;
    let autoFreeze = ref true;;
    (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *);;
    let timeLimit = ref ((None : Time.time option));;
    let rec chPrint n s = begin if (! chatter) >= n then print (s ()) else ()
      end;;
    let rec chMessage n s f = begin if (! chatter) >= n then f (s ()) else ()
      end;;
    end;;
(* structure Global *);;