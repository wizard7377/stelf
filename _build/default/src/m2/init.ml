# 1 "src/m2/init.sig.ml"
open! Basis;;
(* Initialization *);;
(* Author: Carsten Schuermann *);;
module type INIT = sig
                   module MetaSyn : METASYN
                   exception Error of string 
                   val init : IntSyn.cid list -> MetaSyn.state_ list
                   end;;
(* signature INIT *);;
# 1 "src/m2/init.fun.ml"
open! Basis;;
(* Initialization *);;
(* Author: Carsten Schuermann *);;
module Init(Init__0: sig
                     module MetaSyn' : METASYN
                     module MetaAbstract : METAABSTRACT
                     end) : INIT
  =
  struct
    module MetaSyn = MetaSyn';;
    exception Error of string ;;
    open!
      struct
        module M = MetaSyn;;
        module I = IntSyn;;
        let rec init' cid =
          let (v_, _) = M.createAtomConst (I.null_, (I.Const cid))
            in MetaAbstract.abstract
               ((M.State
                 (("/" ^ (I.conDecName (I.sgnLookup cid))) ^ "/",
                  (M.Prefix (I.null_, I.null_, I.null_)), v_)));;
        let rec init cidList = map init' cidList;;
        end;;
    (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover state.
    *);;
    (* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover state.
    *);;
    let init = init;;
    end;;
(* local *);;
(* functor Init *);;
# 1 "src/m2/init.sml.ml"
