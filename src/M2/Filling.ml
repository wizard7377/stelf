open! Intsyn.Lambda_
open! Print.Print_

(* # 1 "src/m2/Filling.sig.ml" *)
open Metasyn

(* Filling *)
(* Author: Carsten Schuermann *)
include FILLING

(* # 1 "src/m2/Filling.fun.ml" *)
open! Basis
open MetaAbstract
open Metasyn

(* Filling *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception TimeOut

let () =
  Printexc.register_printer (function TimeOut -> Some "TimeOut" | _ -> None)

module Filling (Filling__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
  module Search : Search.OLDSEARCH with module MetaSyn = MetaSyn'
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT
end) : FILLING with module MetaSyn = Filling__0.MetaSyn' = struct
  open Filling__0
  module MetaSyn = MetaSyn'

  exception Error = Error
  exception TimeOut = TimeOut

  type nonrec operator = (MetaSyn.state * int) * (unit -> MetaSyn.state list)

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let delay search params () =
      try search params with Search.Error s -> raise (Error s)

    let makeAddressInit s k = (s, k)
    let makeAddressCont makeAddress k = makeAddress (k + 1)

    let rec operators (g, ge, vs, abstractAll, abstractEx, makeAddress) =
      operatorsW (g, ge, Whnf.whnf vs, abstractAll, abstractEx, makeAddress)

    and operatorsW (g, ge, a, abstractAll, abstractEx, makeAddress) = match a with
      | ((I.Root (c, s), _) as vs) ->
          ( [],
            (makeAddress 0, delay Search.searchEx (g, ge, vs, abstractEx))
          )
      | (I.Pi (((I.Dec (_, v1) as d), p), v2), s) ->
          let go', o =
            operators
              ( I.Decl (g, I.decSub d s),
                ge,
                (v2, I.dot1 s),
                abstractAll,
                abstractEx,
                makeAddressCont makeAddress )
          in
          ( ( makeAddress 0,
              delay Search.searchAll (g, ge, (v1, s), abstractAll) )
            :: go',
            o )

    let rec createEVars = function
      | M.Prefix (I.Null, I.Null, I.Null) ->
          (M.Prefix (I.Null, I.Null, I.Null), I.id, [])
      | M.Prefix (I.Decl (g, d), I.Decl (m, M.Top), I.Decl (b_, b)) ->
          let M.Prefix (g', m', b'), s', ge' =
            createEVars (M.Prefix (g, m, b_))
          in
          ( M.Prefix
              ( I.Decl (g', I.decSub d s'),
                I.Decl (m', M.Top),
                I.Decl (b', b) ),
            I.dot1 s',
            ge' )
      | M.Prefix (I.Decl (g, I.Dec (_, v)), I.Decl (m, M.Bot), I.Decl (b, _))
        ->
          let M.Prefix (g', m', b'), s', ge' =
            createEVars (M.Prefix (g, m, b))
          in
          let x = I.newEVar g' (I.EClo (v, s')) in
          let x' = Whnf.lowerEVar x in
          (M.Prefix (g', m', b'), I.Dot (I.Exp x, s'), x' :: ge')

    let expand (M.State (name, M.Prefix (g, m, b), v) as s_) =
      let M.Prefix (g', m', b'), s', ge' =
        createEVars (M.Prefix (g, m, b))
      in
      let abstractAll acc =
        try
          MetaAbstract.abstract
            (M.State (name, M.Prefix (g', m', b'), I.EClo (v, s')))
          :: acc
        with MetaAbstract.Error s -> acc
      in
      let abstractEx () =
        MetaAbstract.abstract
          (M.State (name, M.Prefix (g', m', b'), I.EClo (v, s')))
      in
      operators (g', ge', (v, s'), abstractAll, abstractEx, makeAddressInit s_)

    let apply (_, f) = f ()

    let menu ((M.State (name, M.Prefix (g, m, b), v), k), sl) =
      let rec toString (g, a, k) = match a, k with
        | I.Pi ((I.Dec (_, v), _), _), 0 -> Print.expToString g v
        | (I.Root _ as v), 0 -> Print.expToString g v
        | I.Pi ((d, _), v), k -> toString (I.Decl (g, d), v, k - 1)
      in
      "Filling   : " ^ toString (g, v, k)
  end

  (* operators (G, GE, (V, s), abstract, makeAddress) = (OE', OL')

       Invariant:
       If   G |- s : G1   G1 |- V : type
       and  abstract is an abstraction continuation
       and  makeAddress is continuation which calculates the correct
         debruijn index of the variable being filled
       and V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)
  (* createEVars (G, M) = ((G', M'), s', GE')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
       and  GE a list of EVars

    *)
  (* expand' ((G, M), V) = (OE', OL')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V type
       and  V = {V1}...{Vn} V'
       then OE' is an operator list, OL' is a list with one operator
         where the ith O' in OE' corresponds to a function which generates ALL possible
                                      successor states instantiating - non-index variables
                                      with terms (if possible) in Vi
        and OL' is a list containing one operator which instantiates all - non-index variables
          in V' with the smallest possible terms.
    *)
  (* apply (S, f) = S'

       Invariant:
       S is state and f is a function constructing the successor state S'
    *)
  (* no cases for
              toSTring (G, I.Root _, k) for k <> 0
            *)
  let expand = expand
  let apply = apply
  let menu = menu
end
(*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
(* local *)
(* functor Filling *)

(* # 1 "src/m2/Filling.sml.ml" *)
