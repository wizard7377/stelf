open! Basis;;
module Traverse(Traverse__0: sig
                             (*! structure IntSyn' : INTSYN !*)
                             module Whnf : WHNF
                             (*! sharing Whnf.IntSyn = IntSyn' !*)
                             module Names : NAMES
                             (*! sharing Names.IntSyn = IntSyn' !*)
                             module Traverser' : TRAVERSER
                             end) : TRAVERSE
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    module Traverser = Traverser';;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module T = Traverser;;
        let rec inferConW =
          function 
                   | (g_, I.BVar k')
                       -> let I.Dec (_, v_) = I.ctxDec (g_, k')
                            in Whnf.whnf (v_, I.id)
                   | (g_, I.Const c) -> (I.constType c, I.id)
                   | (g_, I.Def d) -> (I.constType d, I.id);;
        let rec fromHead =
          function 
                   | (g_, I.BVar n) -> T.bvar (Names.bvarName (g_, n))
                   | (g_, I.Const cid)
                       -> let Names.Qid (ids, id) = Names.constQid cid
                            in T.const (ids, id)
                   | (g_, I.Def cid)
                       -> let Names.Qid (ids, id) = Names.constQid cid
                            in T.def (ids, id)
                   | _ -> raise ((Error "Head not recognized"));;
        let rec impCon =
          function 
                   | I.Const cid -> I.constImp cid
                   | I.Def cid -> I.constImp cid
                   | _ -> 0;;
        let rec fromTpW =
          function 
                   | (g_, (I.Root (c_, s_), s))
                       -> T.atom
                          (fromHead (g_, c_),
                           fromSpine
                           (impCon c_, g_, (s_, s), inferConW (g_, c_)))
                   | (g_, (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), s))
                       -> T.arrow
                          (fromTp (g_, (v1_, s)),
                           fromTp
                           ((I.Decl (g_, I.decSub (d_, s))), (v2_, I.dot1 s)))
                   | (g_, (I.Pi ((d_, maybe_), v2_), s))
                       -> let d'_ = Names.decUName (g_, d_)
                            in T.pi
                               (fromDec (g_, (d'_, s)),
                                fromTp
                                ((I.Decl (g_, I.decSub (d'_, s))),
                                 (v2_, I.dot1 s)))
                   | _ -> raise ((Error "Type not recognized"))
        and fromTp (g_, vs_) = fromTpW (g_, Whnf.whnf vs_)
        and fromObjW =
          function 
                   | (g_, (I.Root (c_, s_), s), (v_, t))
                       -> T.root
                          (fromHead (g_, c_),
                           fromSpine
                           (impCon c_, g_, (s_, s), inferConW (g_, c_)),
                           fromTp (g_, (v_, t)))
                   | (g_, (I.Lam (d_, u_), s), (I.Pi (_, v_), t))
                       -> let d'_ = Names.decUName (g_, d_)
                            in T.lam
                               (fromDec (g_, (d'_, s)),
                                fromObj
                                ((I.Decl (g_, I.decSub (d'_, s))),
                                 (u_, I.dot1 s), (v_, I.dot1 t)))
                   | _ -> raise ((Error "Object not recognized"))
        and fromObj (g_, us_, vt_) =
          fromObjW (g_, Whnf.whnf us_, Whnf.whnf vt_)
        and fromSpine =
          function 
                   | (i, g_, (nil_, s), vt_) -> T.nils
                   | (i, g_, (I.SClo (s_, s'), s), vt_)
                       -> fromSpine (i, g_, (s_, I.comp (s', s)), vt_)
                   | (i, g_, (I.App (u_, s_), s),
                      (I.Pi ((I.Dec (_, v1_), _), v2_), t)) -> begin
                       if i > 0 then
                       fromSpine
                       (i - 1, g_, (s_, s),
                        Whnf.whnf
                        (v2_, (I.Dot ((I.Exp ((I.EClo (u_, s)))), t))))
                       else
                       T.app
                       (fromObj (g_, (u_, s), (v1_, t)),
                        fromSpine
                        (i, g_, (s_, s),
                         Whnf.whnf
                         (v2_, (I.Dot ((I.Exp ((I.EClo (u_, s)))), t)))))
                       end
        and fromDec (g_, (I.Dec (Some x, v_), s)) =
          T.dec (x, fromTp (g_, (v_, s)));;
        let rec fromConDec =
          function 
                   | I.ConDec (c, parent, i, _, v_, type_)
                       -> (Some (T.objdec (c, fromTp (I.null_, (v_, I.id)))))
                   | _ -> None;;
        end;;
    (* from typecheck.fun *);;
    (* inferCon (G, C) = V'

     Invariant:
     If    G |- C : V
     and  (C  doesn't contain FVars)
     then  G' |- V' : L      (for some level L)
     and   G |- V = V' : L
     else exception Error is raised.
  *);;
    (* no case for FVar, Skonst *);;
    (* | fromHead (G, I.Skonst (cid)) = T.skonst (Names.constName (cid)) *);;
    (* | fromHead (G, FVar (name, _, _)) = T.fvar (name) *);;
    (* see also: print.fun *);;
    (*| imps (I.Skonst (cid)) = I.constImp (cid) *);;
    (* see also: print.fun *);;
    (*
  fun dropImp (0, S) = S
    | dropImp (i, I.App (U, S)) = dropImp (i-1, S)
    | dropImp (i, I.SClo (S, s)) = I.SClo (dropImp (i, S), s)
    | dropImp _ = raise Error (""Missing implicit arguments"")
  *);;
    (* note: no case for EVars right now *);;
    (* drop implicit arg *);;
    (* NONE should not occur because of call to decName *);;
    (*
    | fromDec (G, (I.Dec (NONE, V), s)) =
        T.dec (""_"", fromTp (G, (V, s)))
    *);;
    (* ignore a : K, d : A = M, b : K = A, and skolem constants *);;
    let fromConDec = fromConDec;;
    let rec const name =
      let qid =
        begin
        match Names.stringToQid name
        with 
             | None
                 -> raise
                    ((Error ("Malformed qualified identifier " ^ name)))
             | Some qid -> qid
        end
        in let cidOpt = Names.constLookup qid
             in let rec getConDec =
                  function 
                           | None
                               -> raise
                                  ((Error
                                    ("Undeclared identifier " ^
                                       (Names.qidToString qid))))
                           | Some cid -> IntSyn.sgnLookup cid
                  in let conDec = getConDec cidOpt
                       in let _ = Names.varReset IntSyn.null_
                            in let rec result =
                                 function 
                                          | None
                                              -> raise
                                                 ((Error
                                                   "Wrong kind of declaration"))
                                          | Some r -> r
                                 in result (fromConDec conDec);;
    end;;
(* shares types from Traverser' *);;
(* local ... *);;
(* functor Traverse *);;