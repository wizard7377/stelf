open! Basis;;
(* Filling *);;
(* Author: Carsten Schuermann *);;
module type FILLING = sig
                      module MetaSyn : METASYN
                      exception Error of string 
                      exception TimeOut 
                      type nonrec operator
                      val expand : MetaSyn.state_ -> operator list * operator
                      (*
    gets a list of operators, which fill in several non index variables
    on one level simultaneously
  *)
                      val apply : operator -> MetaSyn.state_ list
                      (*
    in the case of an induction hypothesis, an operator can transform a
    state into several states. In the case of just filling in the existential
    parameters, there will by only one resulting state (we only need ONE
    witness instantiation of the variables 
  *)
                      val menu : operator -> string
                      end;;