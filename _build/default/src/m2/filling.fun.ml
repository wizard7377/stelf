open! Search;;
open! Basis;;
(* Filling *);;
(* Author: Carsten Schuermann *);;
module Filling(Filling__0: sig
                           module MetaSyn' : METASYN
                           module MetaAbstract : METAABSTRACT
                           module Search : OLDSEARCH
                           module Whnf : WHNF
                           (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                           module Print : PRINT
                           end) : FILLING
  =
  struct
    module MetaSyn = MetaSyn';;
    exception Error of string ;;
    exception TimeOut ;;
    type nonrec operator =
      (MetaSyn.state_ * int) * (unit -> MetaSyn.state_ list);;
    open!
      struct
        module M = MetaSyn;;
        module I = IntSyn;;
        exception Success of M.state_ ;;
        let rec delay (search, params_) () =
          try search params_ with 
                                  | Search.Error s -> raise ((Error s));;
        let rec makeAddressInit s_ k = (s_, k);;
        let rec makeAddressCont makeAddress k = makeAddress (k + 1);;
        let rec operators
          (g_, ge_, vs_, abstractAll, abstractEx, makeAddress) =
          operatorsW
          (g_, ge_, Whnf.whnf vs_, abstractAll, abstractEx, makeAddress)
        and operatorsW =
          function 
                   | (g_, ge_, ((I.Root (c_, s_), _) as vs_), abstractAll,
                      abstractEx, makeAddress)
                       -> ([],
                           (makeAddress 0,
                            delay
                            (function 
                                      | params_
                                          -> try Search.searchEx params_
                                             with 
                                                  | Success s_ -> [s_],
                             (g_, ge_, vs_, abstractEx))))
                   | (g_, ge_, (I.Pi (((I.Dec (_, v1_) as d_), p_), v2_), s),
                      abstractAll, abstractEx, makeAddress)
                       -> let (go'_, o_) =
                            operators
                            ((I.Decl (g_, I.decSub (d_, s))), ge_,
                             (v2_, I.dot1 s), abstractAll, abstractEx,
                             makeAddressCont makeAddress)
                            in (((makeAddress 0,
                                  delay
                                  (Search.searchAll,
                                   (g_, ge_, (v1_, s), abstractAll)))
                                 :: go'_),
                                o_);;
        let rec createEVars =
          function 
                   | M.Prefix (null_, null_, null_)
                       -> ((M.Prefix (I.null_, I.null_, I.null_)), I.id, [])
                   | M.Prefix
                       (I.Decl (g_, d_), I.Decl (m_, top_), I.Decl (b_, b))
                       -> let (M.Prefix (g'_, m'_, b'_), s', ge'_) =
                            createEVars ((M.Prefix (g_, m_, b_)))
                            in ((M.Prefix
                                 ((I.Decl (g'_, I.decSub (d_, s'))),
                                  (I.Decl (m'_, M.top_)), (I.Decl (b'_, b)))),
                                I.dot1 s', ge'_)
                   | M.Prefix
                       (I.Decl (g_, I.Dec (_, v_)), I.Decl (m_, bot_), I.Decl
                        (b_, _))
                       -> let (M.Prefix (g'_, m'_, b'_), s', ge'_) =
                            createEVars ((M.Prefix (g_, m_, b_)))
                            in let x_ = I.newEVar (g'_, (I.EClo (v_, s')))
                                 in let x'_ = Whnf.lowerEVar x_
                                      in ((M.Prefix (g'_, m'_, b'_)),
                                          (I.Dot ((I.Exp x_), s')),
                                          (x'_ :: ge'_));;
        let rec expand ((M.State (name, M.Prefix (g_, m_, b_), v_) as s_)) =
          let (M.Prefix (g'_, m'_, b'_), s', ge'_) =
            createEVars ((M.Prefix (g_, m_, b_)))
            in let rec abstractAll acc =
                 try (MetaAbstract.abstract
                      ((M.State
                        (name, (M.Prefix (g'_, m'_, b'_)), (I.EClo (v_, s')))))
                      :: acc)
                 with 
                      | MetaAbstract.Error s -> acc
                 in let rec abstractEx () =
                      try raise
                          ((Success
                            (MetaAbstract.abstract
                             ((M.State
                               (name, (M.Prefix (g'_, m'_, b'_)),
                                (I.EClo (v_, s'))))))))
                      with 
                           | MetaAbstract.Error s -> ()
                      in operators
                         (g'_, ge'_, (v_, s'), abstractAll, abstractEx,
                          makeAddressInit s_);;
        let rec apply (_, f) = f ();;
        let rec menu ((M.State (name, M.Prefix (g_, m_, b_), v_), k), sl_) =
          let rec toString =
            function 
                     | (g_, I.Pi ((I.Dec (_, v_), _), _), 0)
                         -> Print.expToString (g_, v_)
                     | (g_, (I.Root _ as v_), 0)
                         -> Print.expToString (g_, v_)
                     | (g_, I.Pi ((d_, _), v_), k)
                         -> toString ((I.Decl (g_, d_)), v_, k - 1)
            in "Filling   : " ^ (toString (g_, v_, k));;
        end;;
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
    *);;
    (* createEVars (G, M) = ((G', M'), s', GE')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- s' : G
       and  GE a list of EVars

    *);;
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
    *);;
    (* apply (S, f) = S'

       Invariant:
       S is state and f is a function constructing the successor state S'
    *);;
    (* no cases for
              toSTring (G, I.Root _, k) for k <> 0
            *);;
    let expand = expand;;
    let apply = apply;;
    let menu = menu;;
    end;;
(*! sharing Print.IntSyn = MetaSyn'.IntSyn !*);;
(* local *);;
(* functor Filling *);;