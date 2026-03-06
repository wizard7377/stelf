open! Basis;;
(* Printing of functional proof terms *);;
(* Author: Carsten Schuermann *);;
module TomegaPrint(TomegaPrint__0: sig
                                   (*! structure IntSyn' : INTSYN !*)
                                   (*! structure Tomega' : TOMEGA !*)
                                   (*! sharing Tomega'.IntSyn = IntSyn' !*)
                                   (*   structure Normalize : NORMALIZE *)
                                   (*! sharing Normalize.IntSyn = IntSyn' !*)
                                   (*! sharing Normalize.Tomega = Tomega' !*)
                                   module Formatter : FORMATTER
                                   module Names : NAMES
                                   (*! sharing Names.IntSyn = IntSyn' !*)
                                   module Print : PRINT
                                   end) : TOMEGAPRINT
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure Tomega = Tomega' !*);;
    module Formatter = Formatter;;
    exception Error of string ;;
    (* is just here because we don't have a
     module yet for names. move later
     --cs Tue Apr 27 12:04:45 2004 *);;
    open!
      struct
        module I = IntSyn;;
        module T = Tomega;;
        module Fmt = Formatter;;
        module P = Print;;
        let evarList : T.prg_ list ref = ref [];;
        let rec evarReset () = evarList := [];;
        let rec evarName n =
          let rec evarName' =
            function 
                     | [] -> raise ((Error "not found"))
                     | ((T.EVar (_, _, _, _, _, (I.EVar (_, g_, r, _) as x_))
                          as y_)
                        :: l_) -> begin
                         if (Names.evarName (g_, x_)) = n then y_ else
                         evarName' l_ end
            in evarName' (! evarList);;
        let rec nameEVar
          (T.EVar (_, _, _, _, _, (I.EVar (_, g_, r, _) as x_))) =
          Names.evarName (g_, x_);;
        let rec formatCtxBlock =
          function 
                   | (g_, (null_, s)) -> (g_, s, [])
                   | (g_, (I.Decl (null_, d_), s))
                       -> let d'_ = I.decSub (d_, s)
                            in let fmt = P.formatDec (g_, d'_)
                                 in ((I.Decl (g_, d'_)), I.dot1 s, [fmt])
                   | (g_, (I.Decl (g'_, d_), s))
                       -> let (g''_, s'', fmts) =
                            formatCtxBlock (g_, (g'_, s))
                            in let d''_ = I.decSub (d_, s'')
                                 in let fmt = P.formatDec (g''_, d''_)
                                      in ((I.Decl (g''_, d''_)), I.dot1 s'',
                                          fmts @
                                            [(Fmt.String ","); Fmt.break_;
                                             fmt]);;
        let rec constName c = I.conDecName (I.sgnLookup c);;
        let rec formatWorld =
          function 
                   | [] -> []
                   | (c :: []) -> [(Fmt.String (constName c))]
                   | (c :: cids)
                       -> [(Fmt.String (constName c)); (Fmt.String ",");
                           Fmt.break_] @ (formatWorld cids);;
        let rec formatFor' =
          function 
                   | (psi_, T.All ((d_, explicit_), f_))
                       -> begin
                          match d_
                          with 
                               | T.UDec d_
                                   -> let g_ = T.coerceCtx psi_
                                        in let d'_ = Names.decName (g_, d_)
                                             in [(Fmt.String "all {");
                                                 P.formatDec (g_, d'_);
                                                 (Fmt.String "}");
                                                 Fmt.break_] @
                                                  (formatFor'
                                                   ((I.Decl
                                                     (psi_, (T.UDec d'_))),
                                                    f_))
                          end
                   | (psi_, T.All ((d_, implicit_), f_))
                       -> begin
                          match d_
                          with 
                               | T.UDec d_
                                   -> let g_ = T.coerceCtx psi_
                                        in let d'_ = Names.decName (g_, d_)
                                             in [(Fmt.String "all^ {");
                                                 P.formatDec (g_, d'_);
                                                 (Fmt.String "}");
                                                 Fmt.break_] @
                                                  (formatFor'
                                                   ((I.Decl
                                                     (psi_, (T.UDec d'_))),
                                                    f_))
                          end
                   | (psi_, T.Ex ((d_, explicit_), f_))
                       -> let g_ = T.coerceCtx psi_
                            in let d'_ = Names.decName (g_, d_)
                                 in [(Fmt.String "exists {");
                                     P.formatDec (g_, d'_); (Fmt.String "}");
                                     Fmt.break_] @
                                      (formatFor'
                                       ((I.Decl (psi_, (T.UDec d'_))), f_))
                   | (psi_, T.Ex ((d_, implicit_), f_))
                       -> let g_ = T.coerceCtx psi_
                            in let d'_ = Names.decName (g_, d_)
                                 in [(Fmt.String "exists^ {");
                                     P.formatDec (g_, d'_); (Fmt.String "}");
                                     Fmt.break_] @
                                      (formatFor'
                                       ((I.Decl (psi_, (T.UDec d'_))), f_))
                   | (psi_, T.And (f1_, f2_))
                       -> [(Fmt.String "(");
                           (Fmt.HVbox (formatFor' (psi_, f1_)));
                           (Fmt.String ")"); Fmt.break_; (Fmt.String "/\\");
                           Fmt.space_; (Fmt.String "(");
                           (Fmt.HVbox (formatFor' (psi_, f2_)));
                           (Fmt.String ")")]
                   | (psi_, true_) -> [(Fmt.String "true")]
                   | (psi_, T.World (T.Worlds l_, f_))
                       -> [(Fmt.String "world (");
                           (Fmt.HVbox (formatWorld l_)); (Fmt.String ")");
                           Fmt.break_] @ (formatFor' (psi_, f_));;
        let rec formatFor (g_, f_) =
          (Fmt.HVbox (formatFor' (g_, T.forSub (f_, T.id))));;
        let rec forToString (psi_, f_) =
          Fmt.makestring_fmt (formatFor (psi_, f_));;
        let rec decName =
          function 
                   | (g_, T.UDec d_) -> (T.UDec (Names.decName (g_, d_)))
                   | (g_, T.PDec (None, f_, tc1_, tc2_))
                       -> (T.PDec ((Some "xx"), f_, tc1_, tc2_))
                   | (g_, d_) -> d_;;
        let rec psiName (psi1_, s, psi2_, l) =
          let rec nameDec =
            function 
                     | ((I.Dec (Some _, _) as d_), name) -> d_
                     | (I.Dec (None, v_), name) -> (I.Dec ((Some name), v_))
            in let rec namePsi =
                 function 
                          | (I.Decl (psi_, T.UDec d_), 1, name)
                              -> (I.Decl
                                  (psi_, (T.UDec (nameDec (d_, name)))))
                          | (I.Decl (psi_, (T.UDec d_ as ld_)), n, name)
                              -> (I.Decl (namePsi (psi_, n - 1, name), ld_))
               and nameG =
                 function 
                          | (psi_, null_, n, name, k) -> (k n, I.null_)
                          | (psi_, I.Decl (g_, d_), 1, name, k)
                              -> (psi_, (I.Decl (g_, nameDec (d_, name))))
                          | (psi_, I.Decl (g_, d_), n, name, k)
                              -> let (psi'_, g'_) =
                                   nameG (psi_, g_, n - 1, name, k)
                                   in (psi'_, (I.Decl (g'_, d_)))
                 in let rec ignore =
                      function 
                               | (s, 0) -> s
                               | (T.Dot (_, s), k) -> ignore (s, k - 1)
                               | (T.Shift n, k)
                                   -> ignore
                                      ((T.Dot
                                        ((T.Idx (n + 1)), (T.Shift (n + 1)))),
                                       k - 1)
                      in let rec copyNames arg__1 arg__2 =
                           begin
                           match (arg__1, arg__2)
                           with 
                                | ((T.Shift n, (I.Decl _ as g_)), psi1_)
                                    -> copyNames
                                       ((T.Dot
                                         ((T.Idx (n + 1)), (T.Shift (n + 1)))),
                                        g_)
                                       psi1_
                                | ((T.Dot (T.Exp _, s), I.Decl (g_, _)),
                                   psi1_) -> copyNames (s, g_) psi1_
                                | ((T.Dot (T.Idx k, s), I.Decl
                                    (g_, T.UDec (I.Dec (None, _)))),
                                   psi1_) -> copyNames (s, g_) psi1_
                                | ((T.Dot (T.Idx k, s), I.Decl
                                    (g_, T.UDec (I.Dec (Some name, _)))),
                                   psi1_)
                                    -> let psi1'_ = namePsi (psi1_, k, name)
                                         in copyNames (s, g_) psi1'_
                                | ((T.Dot (T.Prg k, s), I.Decl
                                    (g_, T.PDec (None, _, _, _))),
                                   psi1_) -> copyNames (s, g_) psi1_
                                | ((T.Dot (T.Prg k, s), I.Decl
                                    (g_, T.PDec (Some name, _, _, _))),
                                   psi1_) -> copyNames (s, g_) psi1_
                                | ((T.Shift _, null_), psi1_) -> psi1_
                           end
                           in let rec psiName' =
                                function 
                                         | null_ -> I.null_
                                         | I.Decl (psi_, d_)
                                             -> let psi'_ = psiName' psi_
                                                  in (I.Decl
                                                      (psi'_,
                                                       decName
                                                       (T.coerceCtx psi'_,
                                                        d_)))
                                in psiName' psi1_;;
        let rec fmtSpine arg__3 arg__4 =
          begin
          match (arg__3, arg__4)
          with 
               | (callname, (psi_, nil_)) -> []
               | (callname, (psi_, T.AppExp (u_, s_)))
                   -> ((Fmt.HVbox
                        (Print.formatSpine
                         (T.coerceCtx psi_, (I.App (u_, I.nil_)))))
                       :: fmtSpine' callname (psi_, s_))
               | (callname, (psi_, T.AppPrg (p_, s_)))
                   -> (formatPrg3 callname (psi_, p_)
                       :: fmtSpine' callname (psi_, s_))
          end
        and fmtSpine' arg__5 arg__6 =
          begin
          match (arg__5, arg__6)
          with 
               | (callname, (psi_, nil_)) -> []
               | (callname, (psi_, s_))
                   -> (Fmt.break_ :: fmtSpine callname (psi_, s_))
          end
        and argsToSpine =
          function 
                   | (s, 0, s_) -> s_
                   | (T.Shift n, k, s_)
                       -> argsToSpine
                          ((T.Dot ((T.Idx (n + 1)), (T.Shift (n + 1)))), k,
                           s_)
                   | (T.Dot (T.Idx n, s), k, s_)
                       -> argsToSpine
                          (s, k - 1,
                           (T.AppExp ((I.Root ((I.BVar n), I.nil_)), s_)))
                   | (T.Dot (T.Exp u_, s), k, s_)
                       -> argsToSpine (s, k - 1, (T.AppExp (u_, s_)))
                   | (T.Dot (T.Prg p_, s), k, s_)
                       -> argsToSpine (s, k - 1, (T.AppPrg (p_, s_)))
        and formatTuple (psi_, p_) =
          let rec formatTuple' =
            function 
                     | unit_ -> []
                     | T.PairExp (m_, unit_)
                         -> [Print.formatExp (T.coerceCtx psi_, m_)]
                     | T.PairExp (m_, p'_)
                         -> (Print.formatExp (T.coerceCtx psi_, m_)
                             :: (Fmt.String ",") :: Fmt.break_
                             :: formatTuple' p'_)
            in begin
               match p_
               with 
                    | T.PairExp (_, unit_) -> (Fmt.Hbox (formatTuple' p_))
                    | _
                        -> (Fmt.HVbox0
                            (1, 1, 1,
                             ((Fmt.String "(")
                              :: (formatTuple' p_) @ [(Fmt.String ")")])))
               end
        and formatRedex arg__7 arg__8 =
          begin
          match (arg__7, arg__8)
          with 
               | (callname, (psi_, T.Var k, s_))
                   -> let T.PDec (Some name, _, _, _) = I.ctxLookup (psi_, k)
                        in let fspine_ = fmtSpine callname (psi_, s_)
                             in (Fmt.Hbox
                                 [Fmt.space_;
                                  (Fmt.HVbox
                                   (((Fmt.String name) :: Fmt.break_
                                     :: fspine_)))])
               | (callname, (psi_, T.Const l, s_))
                   -> let T.ValDec (name, _, _) = T.lemmaLookup l
                        in let fspine_ = fmtSpine callname (psi_, s_)
                             in (Fmt.Hbox
                                 [Fmt.space_;
                                  (Fmt.HVbox
                                   (((Fmt.String name) :: Fmt.break_
                                     :: fspine_)))])
               | (callname, (psi_, T.Redex (T.Const l, _), s_))
                   -> let name = callname l
                        in let fspine_ = fmtSpine callname (psi_, s_)
                             in (Fmt.Hbox
                                 [Fmt.space_;
                                  (Fmt.HVbox
                                   (((Fmt.String name) :: Fmt.break_
                                     :: fspine_)))])
          end
        and formatCase callname (max, psi'_, s, psi_) =
          let s_ = argsToSpine (s, (I.ctxLength psi_) - max, T.nil_)
            in let fspine_ = fmtSpine callname (psi'_, s_)
                 in (Fmt.Hbox [(Fmt.HVbox fspine_)])
        and formatCases =
          function 
                   | (max, psi_, [], callname) -> []
                   | (max, psi_, ((psi'_, s, p_) :: []), callname)
                       -> let psi''_ = psiName (psi'_, s, psi_, 0)
                            in let _ = Names.varReset I.null_
                                 in [(Fmt.HVbox0
                                      (1, 5, 1,
                                       [formatCase
                                        callname
                                        (max, psi''_, s, psi_); Fmt.space_;
                                        (Fmt.String "="); Fmt.break_;
                                        formatPrg3 callname (psi''_, p_)]));
                                     Fmt.break_]
                   | (max, psi_, ((psi'_, s, p_) :: o_), callname)
                       -> let psi''_ = psiName (psi'_, s, psi_, 0)
                            in let _ = Names.varReset I.null_
                                 in (formatCases (max, psi_, o_, callname)) @
                                      [(Fmt.HVbox0
                                        (1, 5, 1,
                                         [(Fmt.String "|"); Fmt.space_;
                                          formatCase
                                          callname
                                          (max, psi''_, s, psi_); Fmt.space_;
                                          (Fmt.String "="); Fmt.break_;
                                          formatPrg3 callname (psi''_, p_)]));
                                       Fmt.break_]
        and formatPrg3 arg__9 arg__10 =
          begin
          match (arg__9, arg__10)
          with 
               | (callname, (psi_, unit_)) -> (Fmt.String "<>")
               | (callname, (psi_, T.PairExp (u_, p_)))
                   -> (Fmt.HVbox
                       [(Fmt.String "<");
                        Print.formatExp (T.coerceCtx psi_, u_);
                        (Fmt.String ","); Fmt.break_;
                        formatPrg3 callname (psi_, p_); (Fmt.String ">")])
               | (callname, (psi_, (T.Let _ as p_)))
                   -> formatLet callname (psi_, p_, [])
               | (callname,
                  (psi_, (T.LetPairExp (d1_, d2_, p1_, p2_) as p_)))
                   -> formatLet callname (psi_, p_, [])
               | (callname, (psi_, (T.LetUnit (p1_, p2_) as p_)))
                   -> formatLet callname (psi_, p_, [])
               | (callname,
                  (psi_,
                   (T.New (T.Lam (T.UDec (I.BDec (l, (c, s))), _)) as p_)))
                   -> formatNew callname (psi_, p_, [])
               | (callname, (psi_, T.Redex (p_, s_)))
                   -> formatRedex callname (psi_, p_, s_)
               | (callname, (psi_, T.Lam ((T.UDec d'_ as d_), p_)))
                   -> (Fmt.HVbox
                       [(Fmt.String "lam"); Fmt.space_; (Fmt.String "(");
                        Print.formatDec (T.coerceCtx psi_, d'_);
                        (Fmt.String ")"); Fmt.space_;
                        formatPrg3 callname ((I.Decl (psi_, d_)), p_)])
               | (callname,
                  (psi_, T.Rec
                   ((T.PDec (Some name, f_, None, None) as d_), p_)))
                   -> (Fmt.HVbox
                       [(Fmt.String "fix*"); Fmt.space_; (Fmt.String "(");
                        (Fmt.String name); (Fmt.String ":");
                        formatFor (psi_, f_); (Fmt.String ")"); Fmt.space_;
                        formatPrg3 callname ((I.Decl (psi_, d_)), p_)])
               | (callname,
                  (psi_, T.Rec
                   ((T.PDec (Some name, f_, Some tc1_, Some tc2_) as d_), p_)))
                   -> (Fmt.HVbox
                       [(Fmt.String "fix"); Fmt.space_; (Fmt.String "(");
                        (Fmt.String name); (Fmt.String ":");
                        formatFor (psi_, f_); (Fmt.String ")"); Fmt.space_;
                        formatPrg3 callname ((I.Decl (psi_, d_)), p_)])
               | (callname, (psi_, T.PClo (p_, t)))
                   -> (Fmt.HVbox
                       [formatPrg3 callname (psi_, p_); (Fmt.String "...")])
               | (callname,
                  (psi_,
                   (T.EVar (_, { contents = Some p_}, _, _, _, _) as x_)))
                   -> formatPrg3 callname (psi_, p_)
               | (callname,
                  (psi_, (T.EVar (_, { contents = None}, _, _, _, _) as x_)))
                   -> (Fmt.String (nameEVar x_))
               | (callname, (psi_, T.Case (T.Cases cs_)))
                   -> (Fmt.HVbox
                       (((Fmt.String "case") :: Fmt.break_
                         :: (formatCases (1, psi_, cs_, callname)) @
                              [(Fmt.String ".")])))
               | (callname, (psi_, T.Var n))
                   -> let T.PDec (Some n, _, _, _) = I.ctxLookup (psi_, n)
                        in (Fmt.String n)
               | (callname, _) -> (Fmt.String "missing case")
          end
        and formatNew arg__11 arg__12 =
          begin
          match (arg__11, arg__12)
          with 
               | (callname,
                  (psi_, T.New
                   (T.Lam (T.UDec ((I.BDec (l, (c, s)) as d_)), p_)), fmts))
                   -> let g_ = T.coerceCtx psi_
                        in let d'_ = Names.decName (g_, d_)
                             in formatNew
                                callname
                                ((I.Decl (psi_, (T.UDec d'_))), p_,
                                 (Fmt.break_
                                  :: (Fmt.HVbox [Print.formatDec (g_, d'_)])
                                  :: fmts))
               | (callname, (psi_, p_, fmts))
                   -> (Fmt.Vbox0
                       (0, 1,
                        [(Fmt.String "new"); (Fmt.Vbox0 (0, 1, fmts));
                         Fmt.break_; (Fmt.String "in"); Fmt.break_;
                         (Fmt.Spaces 2); formatPrg3 callname (psi_, p_);
                         Fmt.break_; (Fmt.String "end")]))
          end
        and formatLet arg__13 arg__14 =
          begin
          match (arg__13, arg__14)
          with 
               | (callname,
                  (psi_, T.Let
                   (d_, p1_, T.Case
                    (T.Cases (((psi1_, s1, (T.Let _ as p2_)) :: [])))),
                   fmts))
                   -> let psi1'_ = psiName (psi1_, s1, psi_, 1)
                        in let f1_ =
                             (Fmt.HVbox [formatPrg3 callname (psi_, p1_)])
                             in let s_ = argsToSpine (s1, 1, T.nil_)
                                  in let fspine_ =
                                       fmtSpine callname (psi1_, s_)
                                       in let fpattern_ =
                                            (Fmt.HVbox [(Fmt.Hbox fspine_)])
                                            in let fbody_ = (Fmt.HVbox [f1_])
                                                 in let fmt =
                                                      (Fmt.HVbox
                                                       [(Fmt.HVbox
                                                         [(Fmt.String "val");
                                                          Fmt.space_;
                                                          fpattern_;
                                                          Fmt.space_;
                                                          (Fmt.String "=")]);
                                                        Fmt.break_; fbody_])
                                                      in formatLet
                                                         callname
                                                         (psi1'_, p2_,
                                                          fmts @
                                                            [Fmt.break_; fmt])
               | (callname,
                  (psi_, T.Let
                   (d_, p1_, T.Case (T.Cases (((psi1_, s1, p2_) :: [])))),
                   fmts))
                   -> let psi1'_ = psiName (psi1_, s1, psi_, 1)
                        in let f1_ =
                             (Fmt.HVbox [formatPrg3 callname (psi_, p1_)])
                             in let s_ = argsToSpine (s1, 1, T.nil_)
                                  in let fspine_ =
                                       fmtSpine callname (psi1_, s_)
                                       in let fpattern_ =
                                            (Fmt.HVbox [(Fmt.Hbox fspine_)])
                                            in let fbody_ = (Fmt.HVbox [f1_])
                                                 in let fmt =
                                                      (Fmt.HVbox
                                                       [(Fmt.HVbox
                                                         [(Fmt.String "val");
                                                          Fmt.space_;
                                                          fpattern_;
                                                          Fmt.space_;
                                                          (Fmt.String "=")]);
                                                        Fmt.break_; fbody_])
                                                      in (Fmt.Vbox0
                                                          (0, 1,
                                                           [(Fmt.String
                                                             "let");
                                                            (Fmt.Vbox0
                                                             (2, 1,
                                                              fmts @
                                                                [Fmt.break_;
                                                                 fmt]));
                                                            Fmt.break_;
                                                            (Fmt.String "in");
                                                            Fmt.break_;
                                                            (Fmt.Spaces 2);
                                                            formatPrg3
                                                            callname
                                                            (psi1'_, p2_);
                                                            Fmt.break_;
                                                            (Fmt.String
                                                             "end")]))
               | (callname, (psi_, T.Let (d_, p1_, T.Case (T.Cases l_)), []))
                   -> let rec fmtCaseRest =
                        function 
                                 | [] -> []
                                 | ((psi1_, s1, p2_) :: l_)
                                     -> let psi1'_ =
                                          psiName (psi1_, s1, psi_, 1)
                                          in let s_ =
                                               argsToSpine (s1, 1, T.nil_)
                                               in let fspine_ =
                                                    fmtSpine
                                                    callname
                                                    (psi1_, s_)
                                                    in let fpattern_ =
                                                         (Fmt.HVbox
                                                          [(Fmt.Hbox fspine_)])
                                                         in [(Fmt.HVbox
                                                              [Fmt.space_;
                                                               (Fmt.String
                                                                "|");
                                                               Fmt.space_;
                                                               fpattern_;
                                                               Fmt.space_;
                                                               (Fmt.String
                                                                "-->")]);
                                                             (Fmt.Spaces 2);
                                                             (Fmt.Vbox0
                                                              (0, 1,
                                                               [formatPrg3
                                                                callname
                                                                (psi1'_, p2_)]));
                                                             Fmt.break_] @
                                                              (fmtCaseRest l_)
                        in let rec fmtCase (((psi1_, s1, p2_) :: l_)) =
                             let psi1'_ = psiName (psi1_, s1, psi_, 1)
                               in let s_ = argsToSpine (s1, 1, T.nil_)
                                    in let fspine_ =
                                         fmtSpine callname (psi1_, s_)
                                         in let fpattern_ =
                                              (Fmt.HVbox
                                               [(Fmt.Hbox fspine_)])
                                              in (Fmt.Vbox0
                                                  (0, 1,
                                                   [(Fmt.HVbox
                                                     [(Fmt.String "of");
                                                      Fmt.space_; fpattern_;
                                                      Fmt.space_;
                                                      (Fmt.String "-->")]);
                                                    (Fmt.Spaces 2);
                                                    (Fmt.Vbox0
                                                     (0, 1,
                                                      [formatPrg3
                                                       callname
                                                       (psi1'_, p2_)]));
                                                    Fmt.break_] @
                                                     (fmtCaseRest l_)))
                             in let f1_ =
                                  (Fmt.HVbox
                                   [formatPrg3 callname (psi_, p1_)])
                                  in let fbody_ = (Fmt.HVbox [f1_])
                                       in let fmt = fmtCase l_
                                            in (Fmt.Vbox0
                                                (0, 1,
                                                 [(Fmt.String "case (");
                                                  fbody_; Fmt.space_;
                                                  (Fmt.String ")");
                                                  Fmt.break_; fmt]))
               | (callname,
                  (psi_, (T.Let (d_, p1_, T.Case (T.Cases l_)) as r_), fmts))
                   -> (Fmt.Vbox0
                       (0, 1,
                        [(Fmt.String "let");
                         (Fmt.Vbox0 (0, 1, fmts @ [Fmt.break_])); Fmt.break_;
                         (Fmt.String "in"); Fmt.break_; (Fmt.Spaces 2);
                         formatLet callname (psi_, r_, []); Fmt.break_;
                         (Fmt.String "end")]))
               | (callname,
                  (psi_,
                   (T.Let ((T.PDec (Some name, f_, _, _) as d_), p1_, p2_) as
                     r_),
                   fmts))
                   -> (Fmt.Vbox0
                       (0, 1,
                        [(Fmt.String "let"); Fmt.break_;
                         (Fmt.Vbox0
                          (0, 1,
                           [(Fmt.String name); Fmt.space_; (Fmt.String "=");
                            formatPrg3 callname (psi_, p1_)]));
                         Fmt.break_; (Fmt.String "in"); Fmt.break_;
                         (Fmt.Spaces 2);
                         formatPrg3 callname ((I.Decl (psi_, d_)), p2_);
                         Fmt.break_; (Fmt.String "end")]))
               | (callname,
                  (psi_,
                   (T.LetPairExp
                     ((I.Dec (Some n1, _) as d1_),
                      (T.PDec (Some n2, f_, _, _) as d2_), p1_, p2_)
                     as r_),
                   fmts))
                   -> (Fmt.Vbox0
                       (0, 1,
                        [(Fmt.String "let"); Fmt.break_; (Fmt.Spaces 2);
                         (Fmt.Vbox0
                          (0, 1,
                           [(Fmt.String "("); (Fmt.String n1);
                            (Fmt.String ","); Fmt.space_; (Fmt.String n2);
                            (Fmt.String ")"); Fmt.space_; (Fmt.String "=");
                            Fmt.space_; formatPrg3 callname (psi_, p1_)]));
                         Fmt.break_; (Fmt.String "in"); Fmt.break_;
                         (Fmt.Spaces 2);
                         formatPrg3
                         callname
                         ((I.Decl ((I.Decl (psi_, (T.UDec d1_))), d2_)), p2_);
                         Fmt.break_; (Fmt.String "end")]))
               | (callname, (psi_, (T.LetUnit (p1_, p2_) as r_), fmts))
                   -> (Fmt.Vbox0
                       (0, 1,
                        [(Fmt.String "let"); Fmt.break_; (Fmt.Spaces 2);
                         (Fmt.Vbox0
                          (0, 1,
                           [(Fmt.String "()"); Fmt.space_; (Fmt.String "=");
                            Fmt.space_; formatPrg3 callname (psi_, p1_)]));
                         Fmt.break_; (Fmt.String "in"); Fmt.break_;
                         (Fmt.Spaces 2); formatPrg3 callname (psi_, p2_);
                         Fmt.break_; (Fmt.String "end")]))
          end
        and formatHead callname (name, (max, index), psi'_, s, psi_) =
          let s_ = argsToSpine (s, (I.ctxLength psi_) - max, T.nil_)
            in let fspine_ = fmtSpine callname (psi'_, s_)
                 in (Fmt.Hbox
                     [Fmt.space_;
                      (Fmt.HVbox
                       (((Fmt.String name) :: Fmt.break_ :: fspine_)))]);;
        let rec formatPrg2 =
          function 
                   | (name, (max, index), psi_, [], callname) -> []
                   | (name, (max, index), psi_, ((psi'_, s, p_) :: []),
                      callname)
                       -> let psi''_ = psiName (psi'_, s, psi_, 0)
                            in let fhead = begin
                                 if index = (I.ctxLength psi_) then "fun"
                                 else "and" end
                                 in [(Fmt.HVbox0
                                      (1, 5, 1,
                                       [(Fmt.String fhead);
                                        formatHead
                                        callname
                                        (name, (max, index), psi''_, s, psi_);
                                        Fmt.space_; (Fmt.String "=");
                                        Fmt.break_;
                                        formatPrg3 callname (psi''_, p_)]));
                                     Fmt.break_]
                   | (name, (max, index), psi_, ((psi'_, s, p_) :: o_),
                      callname)
                       -> let psi''_ = psiName (psi'_, s, psi_, 0)
                            in (formatPrg2
                                (name, (max, index), psi_, o_, callname)) @
                                 [(Fmt.HVbox0
                                   (1, 5, 1,
                                    [(Fmt.String "  |");
                                     formatHead
                                     callname
                                     (name, (max, index), psi''_, s, psi_);
                                     Fmt.space_; (Fmt.String "=");
                                     Fmt.break_;
                                     formatPrg3 callname (psi''_, p_)]));
                                  Fmt.break_];;
        let rec formatPrg11 =
          function 
                   | (name, (max, index), psi_, T.Lam (d_, p_), callname)
                       -> formatPrg11
                          (name, (max, index + 1),
                           (I.Decl (psi_, decName (T.coerceCtx psi_, d_))),
                           p_, callname)
                   | (name, (max, index), psi_, T.Case (T.Cases os_),
                      callname)
                       -> formatPrg2
                          (name, (max, index), psi_, os_, callname);;
        let rec formatPrg1 =
          function 
                   | ((name :: names), (max, index), psi_, T.PairPrg
                      (p1_, p2_), callname)
                       -> (formatPrg11
                           (name, (max, index), psi_, p1_, callname)) @
                            (formatPrg1
                             (names, (max, index - 1), psi_, p2_, callname))
                   | ((name :: []), (max, index), psi_, p_, callname)
                       -> formatPrg11
                          (name, (max, index), psi_, p_, callname);;
        let rec lookup ((name :: names), (proj :: projs)) lemma = begin
          if lemma = proj then name else lookup (names, projs) lemma end;;
        let rec formatPrg0
          ((names, projs), T.Rec ((T.PDec (Some _, f_, _, _) as d_), p_)) =
          let max = 1
            in (Fmt.Vbox0
                (0, 1,
                 formatPrg1
                 (names, (max, max), (I.Decl (I.null_, d_)), p_,
                  function 
                           | lemma -> lookup (names, projs) lemma)));;
        let rec formatFun args_ =
          begin
            Names.varReset I.null_;formatPrg0 args_
            end;;
        let rec funToString args_ = Fmt.makestring_fmt (formatFun args_);;
        let rec prgToString args_ =
          Fmt.makestring_fmt (formatPrg3 (function 
                                                   | _ -> "?") args_);;
        let rec nameCtx =
          function 
                   | null_ -> I.null_
                   | I.Decl (psi_, T.UDec d_)
                       -> (I.Decl
                           (nameCtx psi_,
                            (T.UDec (Names.decName (T.coerceCtx psi_, d_)))))
                   | I.Decl (psi_, T.PDec (None, f_, tc1_, tc2_))
                       -> let psi'_ = nameCtx psi_
                            in let I.NDec x =
                                 Names.decName
                                 (T.coerceCtx psi'_, (I.NDec None))
                                 in (I.Decl
                                     (psi'_, (T.PDec (x, f_, tc1_, tc2_))))
                   | I.Decl (psi_, (T.PDec (Some n, f_, _, _) as d_))
                       -> (I.Decl (nameCtx psi_, d_));;
        let rec flag = function 
                                | None -> ""
                                | Some _ -> "*";;
        let rec formatCtx =
          function 
                   | null_ -> []
                   | I.Decl (null_, T.UDec d_) -> begin
                       if (! Global.chatter) >= 4 then
                       [(Fmt.HVbox
                         [Fmt.break_; Print.formatDec (I.null_, d_)])]
                       else [Print.formatDec (I.null_, d_)] end
                   | I.Decl (null_, T.PDec (Some s, f_, tc1_, tc2_)) -> begin
                       if (! Global.chatter) >= 4 then
                       [(Fmt.HVbox
                         [Fmt.break_; (Fmt.String s); Fmt.space_;
                          (Fmt.String ("::" ^ (flag tc1_))); Fmt.space_;
                          formatFor (I.null_, f_)])]
                       else
                       [(Fmt.String s); Fmt.space_;
                        (Fmt.String ("::" ^ (flag tc1_))); Fmt.space_;
                        formatFor (I.null_, f_)]
                       end
                   | I.Decl (psi_, T.UDec d_)
                       -> let g_ = T.coerceCtx psi_ in begin
                            if (! Global.chatter) >= 4 then
                            (formatCtx psi_) @
                              ([(Fmt.String ","); Fmt.break_; Fmt.break_] @
                                 [(Fmt.HVbox
                                   [Fmt.break_; Print.formatDec (g_, d_)])])
                            else
                            (formatCtx psi_) @
                              ([(Fmt.String ","); Fmt.break_] @
                                 [Fmt.break_; Print.formatDec (g_, d_)])
                            end
                   | I.Decl (psi_, T.PDec (Some s, f_, tc1_, tc2_)) -> begin
                       if (! Global.chatter) >= 4 then
                       (formatCtx psi_) @
                         ([(Fmt.String ","); Fmt.break_; Fmt.break_] @
                            [(Fmt.HVbox
                              [Fmt.break_; (Fmt.String s); Fmt.space_;
                               (Fmt.String ("::" ^ (flag tc1_))); Fmt.space_;
                               formatFor (psi_, f_)])])
                       else
                       (formatCtx psi_) @
                         ([(Fmt.String ","); Fmt.break_] @
                            [Fmt.break_; (Fmt.String s); Fmt.space_;
                             (Fmt.String ("::" ^ (flag tc1_))); Fmt.space_;
                             formatFor (psi_, f_)])
                       end;;
        let rec ctxToString psi_ =
          Fmt.makestring_fmt ((Fmt.HVbox (formatCtx psi_)));;
        end;;
    (* Invariant:

       The proof term must satisfy the following conditions:
       * proof term must have the structure
           Rec.     Lam ... Lam Case
                And Lam ... Lam Case
                ...
                And Lam ... Lam Case
         and the body of every case must be of the form
           (Let Decs in Case ...
           or
           Inx ... Inx Unit) *
         where Decs are always of the form
           New ... New App .. App Split .. Split Empty
     *);;
    (* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')

       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1
       and  fmts is a format list of G1[s1]
    *);;
    (* formatFor' (G, (F, s)) = fmts'

       Invariant:
       If   |- G ctx
       and  G |- s : Psi'
       and  Psi' |- F formula
       then fmts' is a list of formats for F
    *);;
    (* formatPrg (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *);;
    (*      fun nameLookup index = List.nth (names, index) *);;
    (* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *);;
    (* needs to be integrated with Names *);;
    (*       numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
        
        fun numberOfSplits Ds =
            let
              fun numberOfSplits' (T.Empty, n) = n
                | numberOfSplits' (T.New (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.App (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Lemma (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Split (_, Ds), n) = numberOfSplits' (Ds, n+1)
                | numberOfSplits' (T.Left (_, Ds), n) = numberOfSplits' (Ds, n)
                | numberOfSplits' (T.Right (_, Ds), n) = numberOfSplits' (Ds, n)
            in
              numberOfSplits' (Ds, 0)
            end
*);;
    (* psiName (Psi1, s, Psi2, l) = Psi1'

           Invariant:
           If   |- Psi1 ctx
           and  |- Psi1' ctx
           and  |- Psi2 ctx
           and  Psi2 = Psi2', Psi2''
           and  Psi1 |- s : Psi2
           and  |Psi2''| = l
           then Psi1' = Psi1 modulo variable naming
           and  for all x in Psi2 s.t. s(x) = x in Psi1'
        *);;
    (* copyNames  (ignore (s, l),  Psi2) *);;
    (*

         merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        
        fun merge (G1, I.Null) = G1
          | merge (G1, I.Decl (G2, D)) =
              I.Decl (merge (G1, G2), D)

         formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        
        fun formatCtx (Psi, G) =
          let
            val G0 = T.makectx Psi

            fun formatCtx' (I.Null) = nil
              | formatCtx' (I.Decl (I.Null, I.Dec (SOME name, V))) =
                  [Fmt.String name, Fmt.String "":"",
                   Print.formatExp (G0, V)]
              | formatCtx' (I.Decl (G, I.Dec (SOME name, V))) =
                  (formatCtx' G) @
                  [Fmt.String "","", Fmt.Break,
                   Fmt.String name, Fmt.String "":"",
                   Print.formatExp (merge (G0, G), V)]
          in
            Fmt.Hbox (Fmt.String ""|"" :: (formatCtx' G @ [Fmt.String ""|""]))
          end

         formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        
        fun formatTuple (Psi, P) =
          let
            fun formatTuple' (T.Unit) = nil
              | formatTuple' (T.Inx (M, T.Unit)) =
              [Print.formatExp (T.makectx Psi, M)]
              | formatTuple' (T.Inx (M, P')) =
              (Print.formatExp (T.makectx Psi, M) ::
               Fmt.String "","" :: Fmt.Break :: formatTuple' P')
          in
            case P
              of (T.Inx (_, T.Unit)) => Fmt.Hbox (formatTuple' P)
              | _ => Fmt.HVbox0 1 1 1
                (Fmt.String ""("" :: (formatTuple' P @ [Fmt.String "")""]))
          end

         formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        
        fun formatSplitArgs (Psi, L) =
          let
            fun formatSplitArgs' (nil) = nil
              | formatSplitArgs' (M :: nil) =
                  [Print.formatExp (T.makectx Psi, M)]
              | formatSplitArgs' (M :: L) =
                  (Print.formatExp (T.makectx Psi, M) ::
                   Fmt.String "","" :: Fmt.Break :: formatSplitArgs' L)
          in
            if List.length L = 1 then Fmt.Hbox (formatSplitArgs' L)
            else Fmt.HVbox0 1 1 1
              (Fmt.String ""("" :: (formatSplitArgs' L @ [Fmt.String "")""]))
          end


         formatDecs1 (Psi, Ds, s, L) = L'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi' = x1:A1 .. xn:An
           and  Psi'' |- s : Psi
           and  for i<=n
                L = (M1 .. Mi)
                s.t   Psi'' |- Mi : Ai
           then L' extends L
           s.t. L = (M1 .. Mn)
                for all i <=n
                Psi'' |- Mi : Ai
                (and Mi is a splitting of a the result of an inductive call)
        
        fun formatDecs1 (Psi, T.Split (xx, Ds), I.Dot (Ft, s1), L) =
              formatDecs1 (Psi, Ds, s1, frontToExp (Ft) :: L)
          | formatDecs1 (Psi, T.Empty, s1, L) = L
          | formatDecs1 (Psi, Ds, I.Shift n, L) =
              formatDecs1 (Psi, Ds, I.Dot (I.Idx (n+1), I.Shift (n+1)), L)


         formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        
        fun formatDecs0 (Psi, T.App ((xx, M), Ds)) =
            let
              val (Ds', S) =
                formatDecs0 (Psi, Ds)
            in
              (Ds', I.App (M, S))
            end
          | formatDecs0 (Psi, Ds) = (Ds, I.Nil)


         formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        
        fun formatDecs (index, Psi, Ds as T.App ((xx, _), P), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val name = nameLookup index
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String ""="", Fmt.Break,
                        Fmt.HVbox (Fmt.String name :: Fmt.Break ::
                                   Print.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.New (B as T.CtxBlock (_, G), Ds),
                        (Psi1, s1)) =
            let
              val B' = ctxBlockName (T.makectx Psi, B)
              val fmt =
                formatDecs (index, I.Decl (Psi, T.Block B'), Ds, (Psi1, s1))
            in
              Fmt.Vbox [formatCtx (Psi, G), Fmt.Break, fmt]
            end
          | formatDecs (index, Psi, T.Lemma (lemma, Ds), (Psi1, s1)) =
            let
              val (Ds', S) = formatDecs0 (Psi, Ds)
              val L' = formatDecs1 (Psi, Ds', s1, nil)
              val (T.LemmaDec (names, _, _)) = T.lemmaLookup lemma
            in
              Fmt.Hbox [formatSplitArgs (Psi1, L'), Fmt.Space,
                        Fmt.String ""="", Fmt.Break,
                        Fmt.HVbox (Fmt.String (List.nth (names, index)) :: Fmt.Break ::
                                   Print.formatSpine callname (T.makectx Psi, S))]
            end
          | formatDecs (index, Psi, T.Left (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index, Psi, Ds, (Psi1, s1))
            in
              fmt
            end
          | formatDecs (index, Psi, T.Right (_, Ds), (Psi1, s1)) =
            let
              val fmt =
                formatDecs (index+1, Psi, Ds, (Psi1, s1))
            in
              fmt
            end


*);;
    (* fmtSpine callname (G, d, l, (S, s)) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
  *);;
    (* Print.formatExp (T.coerceCtx Psi, U) *);;
    (*
         frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        
        and frontToExp (T.Idx k) = I.Root (I.BVar k, I.Nil)
          | frontToExp (T.Exp (U)) = U
          | frontToExp (T.Prg (T.PairExp (U, _))) = U     this is a patch -cs
                                                            works only with one exists quantifier
                                                            we cannot use LF spines, we need to
                                                            use tomega spines.

                                                            Next step program printer for tomega spines
                                                            Then change this code. 
*);;
    (* argsToSpine (Psi1, s, S) = S'

           Invariant:
           If   Psi1 |- s = M1 . M2 .. Mn. ^|Psi1|: Psi2
           and  Psi1 |- S : V1 > {Psi2} V2
           then Psi1 |- S' : V1 > V2
           and S' = S, M1 .. Mn
           where
           then Fmts is a list of arguments
        *);;
    (* Idx will always be expanded into Expressions and never into programs
                 is this a problem? -- cs *);;
    (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *);;
    (* no mutual recursion, recursive call *);;
    (* lemma application *);;
    (* mutual recursion, k is the projection function *);;
    (* val T.ValDec (name, _, _) = T.lemmaLookup l *);;
    (* formatCases ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *);;
    (* formatPrg3 callname  (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
        *);;
    (* formatTuple (Psi, P) *);;
    (* formatTuple (Psi, P) *);;
    (* need to fix the first  argument to formatcases Tue Apr 27 10:38:57 2004 --cs *);;
    (* formatLet callname (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *);;
    (* was I.ctxLength Psi - max  --cs *);;
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *);;
    (* was I.ctxLength Psi - max  --cs *);;
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi1, S) *);;
    (*            val fmt =  formatDecs (0, Psi, Ds, (Psi1', s1)) 
                Fmt.Hbox [Fmt.String "" ..."" , Fmt.Space, Fmt.String ""="",  Fmt.Break, F1] *);;
    (* Added by ABP -- 2/25/03 -- Now a let can have multiple cases *);;
    (* need space since there is one before Fbody *);;
    (* formatHead callname (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *);;
    (*            val T.PDec (SOME name, _) = I.ctxLookup (Psi, index) *);;
    (*            val Fspine =   Print.formatSpine callname (T.coerceCtx Psi', S) *);;
    (* formatPrg2 ((max, index), Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *);;
    (* formatPrg1 ((max, index), Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *);;
    (* formatPrg0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *);;
    (*      fun formatPrg0 (T.Rec (T.PDec (SOME _, F),
                             T.Case (T.Cases [(Psi, t, P)]))) =
          let
            val max = I.ctxLength Psi    number of ih. 
          in
            Fmt.Vbox0 0 1 (formatPrg1 ((max, max), Psi, P))
          end
*);;
    (* number of ih. *);;
    (*    fun formatLemmaDec (T.LemmaDec (names, P, F)) =
      Fmt.Vbox0 0 1 [formatFor (I.Null, F) names, Fmt.Break,
                     formatPrg (I.Null, P) names]
*);;
    (*   fun lemmaDecToString Args = Fmt.makestring_fmt (formatLemmaDec Args) *);;
    (*    fun prgToString Args names = ""not yet implemented "" *);;
    (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *);;
    let formatFor = formatFor;;
    let forToString = forToString;;
    let formatFun = formatFun;;
    let formatPrg = formatPrg3 (function 
                                         | _ -> "?");;
    (*    val formatLemmaDec = formatLemmaDec *);;
    let evarName = evarName;;
    let evarReset = evarReset;;
    let nameEVar = nameEVar;;
    let prgToString = prgToString;;
    let funToString = funToString;;
    let nameCtx = nameCtx;;
    let formatCtx = function 
                             | psi_ -> (Fmt.HVbox (formatCtx psi_));;
    let ctxToString = ctxToString;;
    (*    val lemmaDecToString = lemmaDecToString *);;
    end;;
(*! sharing Print.IntSyn = IntSyn' !*);;
(* signature FUNPRINT *);;