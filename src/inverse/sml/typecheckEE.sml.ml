open! Timers;;
open! Basis;;
module TypecheckEE : TYPECHECK =
  struct
    module L = Lib;;
    module S = Syntax;;
    module Sig = S.Signat;;
    module C = Context;;
    module D = Debug;;
    open S;;
    type ret = | RetExp of exp 
               | RetVar of int ;;
    (** check a term (type)  against a type (kind) *);;
    let rec check_exp =
      function 
               | (ctx, Uni Type, Uni Kind) -> ()
               | (ctx, Lam { body = m_}, Pi { var; arg = u_; body = v_})
                   -> check_exp (C.push (ctx, (var, u_)), m_, v_)
               | (ctx, Root (Const con, s_), v_)
                   -> let rec foc exp =
                        let u_ = focus (ctx, s_, exp) in begin
                          if equiv_exp (u_, v_) then () else
                          raise ((Fail "check_exp: exps not equivalent")) end
                        in begin
                           match Sig.lookup con
                           with 
                                | Decl decl -> foc ((fun r -> r.exp) decl)
                                | Def def -> foc ((fun r -> r.exp) def)
                                | Abbrev abbrev
                                    -> raise ((Fail "check_exp: abbrev"))
                           end
                        (* why does this fail?*)(* pull some common code out of the following case *)
               | (ctx, Root (BVar i, s_), v_)
                   -> begin
                      match C.lookup (ctx, i - 1)
                      with 
                           | Some (_, a_)
                               -> let u_ =
                                    focus
                                    (ctx, s_, apply_exp ((Shift i), a_))
                                    in begin
                                    if equiv_exp (u_, v_) then () else
                                    raise
                                    ((Fail_exp2
                                      ("check_exp: Root,BVar", u_, v_)))
                                    end
                           | None
                               -> raise ((Fail "focus: var out of bounds"))
                      end
                   (* DeBruijn indices start at 1 *)
               | (ctx, Pi { var; arg = a1_; body = a2_}, (Uni _ as uni))
                   -> begin
                        check_exp (ctx, a1_, expType);
                        check_exp (C.push (ctx, (var, a1_)), a2_, uni)
                        end
               | _ -> raise ((Fail "check: bad case"))
    and focus =
      function 
               | (ctx, Nil, (Uni Type as ty)) -> ty
               | (ctx, Nil, (Root (Const _, _) as hd)) -> hd
               | (ctx, App (m_, s_), Pi { arg = a1_; body = a2_})
                   -> begin
                        check_exp (ctx, m_, a1_);
                        focus (ctx, s_, apply_exp ((Dot (m_, id_sub)), a2_))
                        end
               | (_, s_, e_)
                   -> raise ((Fail_spine_exp ("focus: bad case", s_, e_)))
    and check e1_ e2_ =
      Timers.time Timers.checking check_exp (C.empty, e1_, e2_)
    and apply_exp =
      function 
               | (_, (Uni _ as uni)) -> uni
               | (sub, Pi { var; arg = u_; depend; body = v_})
                   -> (Pi
                       {
                       var;
                       arg = apply_exp (sub, u_);
                       depend;
                       body = apply_exp (push_sub sub, v_)}
                       )
               | (sub, Lam { var; body = u_})
                   -> (Lam { var; body = apply_exp (push_sub sub, u_)} )
               | (sub, (Root (h_, s_) as exp))
                   -> let s'_ = apply_spine (sub, s_)
                        in begin
                           match h_
                           with 
                                | Const _ -> (Root (h_, s'_))
                                | BVar i
                                    -> begin
                                       match apply_var (sub, i)
                                       with 
                                            | RetVar j
                                                -> (Root ((BVar j), s'_))
                                            | RetExp m_ -> reduce (m_, s'_)
                                       end
                           end
    and apply_spine =
      function 
               | (_, Nil) -> Nil
               | (sub, App (m_, s_))
                   -> (App (apply_exp (sub, m_), apply_spine (sub, s_)))
    and apply_var =
      function 
               | (Dot (m_, sub), i) -> begin
                   if i = 1 then
                   begin
                   match m_
                   with 
                        | Root (BVar j, Nil) -> (RetVar j)
                        | _ -> (RetExp m_)
                   end else apply_var (sub, i - 1) end
               | (Shift n, i) -> (RetVar (i + n))
    and compose =
      function 
               | (Dot (m_, sigma), sigma')
                   -> (Dot (apply_exp (sigma', m_), compose (sigma, sigma')))
               | (Shift n, Shift m) -> (Shift (n + m))
               | (Shift 0, sigma) -> sigma
               | (Shift n, Dot (m_, sigma))
                   -> compose ((Shift (n - 1)), sigma)
    and push_sub s = (Dot (one, compose (s, shift)))
    and reduce =
      function 
               | ((Root (_, _) as exp), Nil) -> exp
               | (Lam { body = m_}, App (m'_, s_))
                   -> reduce (apply_exp ((Dot (m'_, id_sub)), m_), s_)
               | (e_, s_)
                   -> raise
                      ((Fail_exp_spine ("reduce: bad case: head: ", e_, s_)))
    and equiv_exp =
      function 
               | (Uni u1, Uni u2) -> u1 = u2
               | (Pi { arg = u1_; body = v1_}, Pi { arg = u2_; body = v2_})
                   -> (equiv_exp (u1_, u2_)) && (equiv_exp (v1_, v2_))
               | (Lam { body = u_}, Lam { body = u'_}) -> equiv_exp (u_, u'_)
               | (Root (BVar i, s1_), Root (BVar i', s2_))
                   -> (i = i') && (equiv_spine (s1_, s2_))
               | ((Root (Const c, s_) as exp),
                  (Root (Const c', s'_) as exp')) -> begin
                   if c = c' then equiv_spine (s_, s'_) else
                   begin
                   match (Sig.lookup c, Sig.lookup c')
                   with 
                        | (Decl decl, Def def) -> begin
                            if
                            ((fun r -> r.root) def) <> ((fun r -> r.id) decl)
                            then false else
                            equiv_exp
                            (exp, reduce ((fun r -> r.def) def, s'_)) end
                        | (Def def, Decl decl) -> begin
                            if
                            ((fun r -> r.root) def) <> ((fun r -> r.id) decl)
                            then false else
                            equiv_exp
                            (reduce ((fun r -> r.def) def, s_), exp') end
                        | (Abbrev { def}, _)
                            -> equiv_exp (reduce (def, s_), exp')
                        | (_, Abbrev { def})
                            -> equiv_exp (exp, reduce (def, s'_))
                        | (Def { def; height = h; root = rc}, Def
                           { def = def'; height = h'; root = rc'}) -> begin
                            if rc <> rc' then false else begin
                            if h = h' then
                            equiv_exp (reduce (def, s_), reduce (def', s'_))
                            else begin
                            if h > h' then equiv_exp (reduce (def, s_), exp')
                            else equiv_exp (exp, reduce (def', s'_)) end end
                            end
                        | (_, _) -> raise ((Fail "equiv_exp: bad case"))
                   end end
               | _ -> false
    and equiv_spine =
      function 
               | (S.Nil, Nil) -> true
               | (S.App (e_, s_), S.App (e'_, s'_))
                   -> (equiv_exp (e_, e'_)) && (equiv_spine (s_, s'_))
               | _ -> false;;
    (* -------------------------------------------------------------------------- *);;
    (*  Substitutions                                                             *);;
    (* -------------------------------------------------------------------------- *);;
    (* -------------------------------------------------------------------------- *);;
    (*  Beta                                                                      *);;
    (* -------------------------------------------------------------------------- *);;
    (* -------------------------------------------------------------------------- *);;
    (*  Equivalence wrt Definitions                                               *);;
    (* -------------------------------------------------------------------------- *);;
    (* -------------------------------------------------------------------------- *);;
    (*  Signatures                                                                *);;
    (* -------------------------------------------------------------------------- *);;
    let rec check_dec =
      function 
               | (c, Decl { id; name; exp; uni})
                   -> let uni' = (Uni uni)
                        in let exp' = eta_expand (exp, uni')
                             in begin
                                  check exp' uni';
                                  Sig.insert
                                  (id, (Decl { id; name; exp = exp'; uni} ))
                                  end
               | (c, Def { id; name; exp; def; height; root; uni})
                   -> let uni' = (Uni uni)
                        in let exp' = eta_expand (exp, uni')
                             in let def' = eta_expand (def, exp')
                                  in begin
                                       check exp' uni';
                                       begin
                                         check def' exp';
                                         Sig.insert
                                         (id,
                                          (Def
                                           {
                                           id;
                                           name;
                                           exp = exp';
                                           def = def';
                                           height;
                                           root;
                                           uni}
                                           ))
                                         
                                         end
                                       
                                       end
               | (c, Abbrev { id; name; exp; def; uni})
                   -> let uni' = (Uni uni)
                        in let exp' = exp
                             in let def' = def
                                  in begin
                                       check exp' uni';
                                       begin
                                         check def' exp';
                                         Sig.insert
                                         (id,
                                          (Abbrev
                                           {
                                           id;
                                           name;
                                           exp = exp';
                                           def = def';
                                           uni}
                                           ))
                                         
                                         end
                                       
                                       end
                                  (*         val exp' = eta_expand(exp,uni') *)(*         val def' = eta_expand(def,exp') *);;
    let rec check_signat' decs =
      List.app
      (function 
                | ((c, Dec_) as decl) -> check_dec decl
                    (* L.printl (""checking: "" ^ name dec ); *))
      decs;;
    let rec check_signat decs =
      Timers.time Timers.checking check_signat' decs;;
    let rec check_signat_clear decs =
      begin
        Sig.reset ();check_signat decs
        end;;
    end;;