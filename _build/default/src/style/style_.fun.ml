open! Basis;;
module StyleCheck(StyleCheck__0: sig
                                 (* Style Checking *)
                                 (* Author: Carsten Schuermann *)
                                 module Whnf : WHNF
                                 module Index : INDEX
                                 module Origins : ORIGINS
                                 end) : STYLECHECK
  =
  struct
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module P = Paths;;
        type polarity = | Plus 
                        | Minus ;;
        type info = | Correct 
                    | Incorrect of string list * string ;;
        let rec toggle = function 
                                  | Plus -> Minus
                                  | Minus -> Plus;;
        let rec wrapMsg (c, occ, msg) err =
          begin
          match Origins.originLookup c
          with 
               | (fileName, None) -> (fileName ^ ":") ^ msg
               | (fileName, Some occDec)
                   -> P.wrapLoc'
                      ((P.Loc (fileName, err occDec occ)),
                       Origins.linesInfoLookup fileName, msg)
          end;;
        let rec denumber =
          function 
                   | [] -> []
                   | (c :: l)
                       -> let x = ord c
                            in let l' = denumber l in begin
                                 if
                                 ((x >= 65) && (x <= 90)) ||
                                   ((x >= 97) && (x <= 122))
                                 then (c :: l') else l' end;;
        let rec options =
          function 
                   | (n :: []) -> n
                   | (n :: l) -> (n ^ ", ") ^ (options l);;
        let rec error c (prefNames, n, occ) err =
          [wrapMsg
           (c, occ,
            ((("Variable naming: expected " ^ (options prefNames)) ^
                " found ")
               ^ n)
              ^ "\n")
           err];;
        let rec checkVariablename (n, prefNames) = begin
          if
          List.exists
          (function 
                    | n' -> (denumber (explode n)) = (denumber (explode n')))
          prefNames then Correct else (Incorrect (prefNames, n)) end;;
        let rec checkVar =
          function 
                   | (I.Dec (Some n, v_), pol)
                       -> begin
                          match Names.getNamePref (I.targetFam v_)
                          with 
                               | None -> Correct
                               | Some (prefENames, prefUNames)
                                   -> begin
                                      match pol
                                      with 
                                           | Plus
                                               -> checkVariablename
                                                  (n, prefENames)
                                           | Minus
                                               -> checkVariablename
                                                  (n, prefUNames)
                                      end
                          end
                   | (I.Dec (None, v_), pol) -> Correct;;
        let rec implicitHead =
          function 
                   | I.BVar k -> 0
                   | I.Const c -> I.constImp c
                   | I.Skonst k -> 0
                   | I.Def d -> I.constImp d
                   | I.NSDef d -> I.constImp d
                   | I.FgnConst _ -> 0;;
        let rec checkExp arg__1 arg__2 arg__3 =
          begin
          match (arg__1, arg__2, arg__3)
          with 
               | (c, ((g_, p_), I.Uni _, occ), err) -> []
               | (c, ((g_, p_), I.Lam (d_, u_), occ), err)
                   -> checkDec
                      c
                      ((g_, p_), d_, Minus, occ)
                      err
                      (function 
                                | ((g'_, p'_), l'_)
                                    -> l'_ @
                                         (checkExp
                                          c
                                          ((g'_, p'_), u_, P.body occ)
                                          err))
               | (c, ((g_, p_), I.Root (h_, s_), occ), err)
                   -> (checkHead c ((g_, p_), h_, P.head occ) err) @
                        (checkSpine
                         c
                         ((g_, p_), 1, implicitHead h_, s_, P.body occ)
                         err)
               | (c, ((g_, p_), I.FgnExp (_, _), occ), err) -> []
          end
        and checkType arg__4 arg__5 arg__6 =
          begin
          match (arg__4, arg__5, arg__6)
          with 
               | (c, ((g_, p_), I.Uni _, pol, occ), err) -> []
               | (c, ((g_, p_), I.Pi ((d_, maybe_), v_), pol, occ), err)
                   -> checkDec
                      c
                      ((g_, p_), d_, pol, occ)
                      err
                      (function 
                                | ((g'_, p'_), l'_)
                                    -> l'_ @
                                         (checkType
                                          c
                                          ((g'_, p'_), v_, pol, P.body occ)
                                          err))
               | (c, ((g_, p_), I.Pi ((d_, no_), v_), pol, occ), err)
                   -> checkDec
                      c
                      ((g_, p_), d_, pol, occ)
                      err
                      (function 
                                | ((g'_, p'_), l'_)
                                    -> l'_ @
                                         (checkType
                                          c
                                          ((g'_, p'_), v_, pol, P.body occ)
                                          err))
               | (c, ((g_, p_), I.Root (h_, s_), pol, occ), err)
                   -> (checkHead c ((g_, p_), h_, P.head occ) err) @
                        (checkSpine
                         c
                         ((g_, p_), 1, implicitHead h_, s_, P.body occ)
                         err)
               | (c, ((g_, p_), I.FgnExp (_, _), pol, occ), err) -> []
          end
        and checkDecImp ((g_, p_), (I.Dec (_, v_) as d_), pol) k =
          let i_ = checkVar (d_, pol)
            in k (((I.Decl (g_, d_)), (I.Decl (p_, i_))), [])
        and checkDec c ((g_, p_), (I.Dec (_, v_) as d_), pol, occ) err k =
          let i_ = checkVar (d_, pol)
            in let e1_ =
                 begin
                 match i_
                 with 
                      | Correct -> []
                      | Incorrect (prefNames, n)
                          -> error c (prefNames, n, occ) err
                 end
                 in let e2_ =
                      checkType c ((g_, p_), v_, toggle pol, P.label occ) err
                      in k
                         (((I.Decl (g_, d_)), (I.Decl (p_, i_))), e1_ @ e2_)
        and checkHead arg__7 arg__8 arg__9 =
          begin
          match (arg__7, arg__8, arg__9)
          with 
               | (c, ((g_, p_), I.BVar k, occ), err)
                   -> begin
                      match I.ctxLookup (p_, k)
                      with 
                           | Correct -> []
                           | Incorrect (prefNames, n)
                               -> error c (prefNames, n, occ) err
                      end
               | (c, ((g_, p_), I.Const _, occ), err) -> []
               | (c, ((g_, p_), I.Skonst k, occ), err) -> []
               | (c, ((g_, p_), I.Def d, occ), err) -> []
               | (c, ((g_, p_), I.NSDef d, occ), err) -> []
               | (c, ((g_, p_), I.FgnConst _, occ), err) -> []
          end
        and checkSpine arg__10 arg__11 arg__12 =
          begin
          match (arg__10, arg__11, arg__12)
          with 
               | (c, ((g_, p_), n, 0, nil_, occ), err) -> []
               | (c, ((g_, p_), n, 0, I.App (u_, s_), occ), err)
                   -> (checkExp c ((g_, p_), u_, P.arg (n, occ)) err) @
                        (checkSpine c ((g_, p_), n + 1, 0, s_, occ) err)
               | (c, ((g_, p_), n, i, I.App (u_, s_), occ), err)
                   -> checkSpine c ((g_, p_), n + 1, i - 1, s_, occ) err
          end;;
        let rec checkType' arg__13 arg__14 arg__15 =
          begin
          match (arg__13, arg__14, arg__15)
          with 
               | (c, ((g_, p_), 0, v_, occ), err)
                   -> checkType c ((g_, p_), v_, Plus, occ) err
               | (c, ((g_, p_), n, I.Pi ((d_, maybe_), v_), occ), err)
                   -> checkDecImp
                      ((g_, p_), d_, Plus)
                      (function 
                                | ((g'_, p'_), l'_)
                                    -> l'_ @
                                         (checkType'
                                          c
                                          ((g'_, p'_), n - 1, v_, P.body occ)
                                          err))
          end;;
        let rec checkExp' arg__16 arg__17 arg__18 =
          begin
          match (arg__16, arg__17, arg__18)
          with 
               | (c, ((g_, p_), I.Lam (d_, u_), occ), err)
                   -> checkDec
                      c
                      ((g_, p_), d_, Plus, occ)
                      err
                      (function 
                                | ((g'_, p'_), l'_)
                                    -> l'_ @
                                         (checkExp'
                                          c
                                          ((g'_, p'_), u_, P.body occ)
                                          err))
               | (c, ((g_, p_), u_, occ), err)
                   -> checkExp c ((g_, p_), u_, occ) err
          end;;
        let rec checkDef arg__19 arg__20 arg__21 =
          begin
          match (arg__19, arg__20, arg__21)
          with 
               | (c, ((g_, p_), 0, u_, occ), err)
                   -> checkExp' c ((g_, p_), u_, occ) err
               | (c, ((g_, p_), n, I.Lam (d_, u_), occ), err)
                   -> checkDecImp
                      ((g_, p_), d_, Plus)
                      (function 
                                | ((g'_, p'_), l'_)
                                    -> l'_ @
                                         (checkDef
                                          c
                                          ((g'_, p'_), n - 1, u_, P.body occ)
                                          err))
          end;;
        let rec checkConDec arg__22 arg__23 =
          begin
          match (arg__22, arg__23)
          with 
               | (c, I.ConDec (_, _, implicit, _, u_, _))
                   -> begin
                        begin
                        if (! Global.chatter) > 3 then
                        print ((Names.qidToString (Names.constQid c)) ^ " ")
                        else () end;
                        checkType'
                        c
                        ((I.null_, I.null_), implicit, u_, P.top)
                        P.occToRegionDec
                        end
               | (c, I.ConDef (_, _, implicit, u_, v_, type_, _))
                   -> begin
                        begin
                        if (! Global.chatter) > 3 then
                        print ((Names.qidToString (Names.constQid c)) ^ " ")
                        else () end;
                        (checkType'
                         c
                         ((I.null_, I.null_), implicit, v_, P.top)
                         P.occToRegionDef2) @
                          (checkDef
                           c
                           ((I.null_, I.null_), implicit, u_, P.top)
                           P.occToRegionDef1)
                        
                        end
               | (c, I.AbbrevDef (_, _, implicit, u_, v_, type_))
                   -> begin
                        begin
                        if (! Global.chatter) > 3 then
                        print ((Names.qidToString (Names.constQid c)) ^ " ")
                        else () end;
                        begin
                          checkType'
                          c
                          ((I.null_, I.null_), implicit, v_, P.top)
                          P.occToRegionDef2;
                          checkDef
                          c
                          ((I.null_, I.null_), implicit, u_, P.top)
                          P.occToRegionDef1
                          end
                        
                        end
               | (c, _) -> []
          end;;
        let rec checkAll (c, n) = begin
          if c <= n then
          (checkConDec c (I.sgnLookup c)) @ (checkAll (c + 1, n)) else [] end;;
        let rec check () =
          let (n, _) = I.sgnSize ()
            in begin
                 map print (checkAll (0, n));()
                 end;;
        end;;
    (* indicates positivity *);;
    (* distinguishes style correct
                                           from - incorrect declarations *);;
    (* wrapMsg (c, occ, msg) err = s

       Invariant:
       Let c be a cid
       occ by an occurrence,
       msg an error message,
       and err a function that computes adequate region information for c
       then s is msg wrapped with location information
    *);;
    (* denumber L = L'

       Invariant:
       L' = L without digits
    *);;
    (* checkVariblename (n, prefNames) = I

       Invariant:
       If n occurs in prefNames then I = Correct otherwise Incorrect
    *);;
    (* checkVar (D, pol) = I

       Invariant:
       If  D's name corresponds to the name choice for pol,
       then I is Correct else Incorrect
    *);;
    (* implicitHead H = k

       Invariant:
       k = # implicit arguments associated with H
    *);;
    (* checkExp c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from U
    *);;
    (* checkType c ((G, P), V, pol, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  V : type
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from V
    *);;
    (* checkDecImp c ((G, P), D, pol) k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed D
       ( checkDecImp does not generate any error messages for D since omitted)
    *);;
    (* checkDec c ((G, P), D, pol, occ) err k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   occ occurrence, err wrapper function
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed from D
    *);;
    (* checkHead c ((G, P), H, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-  H head
       and   occ occurrence, err wrapper function
       then  L is a list of at most one string (error message) computed from H
    *);;
    (* checkSpine c ((G, P), S, n, i, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- S : V1 >> V2  for V1 V2, valid types
       and   n a running number of arguments considered
       and   i the number of remaining implicit arguments
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from S
    *);;
    (* checkType' c ((G, P), n, V, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- V : type
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from V
       (omitted arguments generate error message where they are used not declared)
    *);;
    (* checkExp' c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *);;
    (* checkDef c ((G, P), n, U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *);;
    (* checkConDec c C = L

       Invariant:
       Let   c be a cid
       and   . |- C : V for some type V, constant declaration
       then  L is a list of  strings (error messages) computed from C
    *);;
    (* type level definitions ? *);;
    (* type level abbreviations ? *);;
    (* in all other cases *);;
    (* checkAll (c, n) = L

       Invariant:
       Let   c be a cid
       and   n the max. number of cids
       then  L is a list of  strings (error messages) computed from the signature c<=n
    *);;
    (* checkAll () = L

       Invariant:
       L is a list of  strings (error messages) computed from the entire Twelf signature
    *);;
    let checkConDec =
      function 
               | c -> begin
                        map print (checkConDec c (I.sgnLookup c));()
                        end;;
    let check = check;;
    end;;