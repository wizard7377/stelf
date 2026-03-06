# 1 "src/meta/funprint.sig.ml"
open! Basis;;
(* Printing of functional proof terms *);;
(* Author: Carsten Schuermann *);;
module type FUNPRINT = sig
                       (*! structure FunSyn : FUNSYN !*)
                       module Formatter : FORMATTER
                       val
                         formatForBare : (IntSyn.dctx * FunSyn.for_) ->
                                         Formatter.format
                       val
                         formatFor : (FunSyn.lfctx * FunSyn.for_) ->
                                     string
                                     list ->
                                     Formatter.format
                       val
                         formatPro : (FunSyn.lfctx * FunSyn.pro_) ->
                                     string
                                     list ->
                                     Formatter.format
                       val
                         formatLemmaDec : FunSyn.lemmaDec_ ->
                                          Formatter.format
                       val
                         forToString : (FunSyn.lfctx * FunSyn.for_) ->
                                       string
                                       list ->
                                       string
                       val
                         proToString : (FunSyn.lfctx * FunSyn.pro_) ->
                                       string
                                       list ->
                                       string
                       val lemmaDecToString : FunSyn.lemmaDec_ -> string
                       end;;
(* signature PRINT *);;
# 1 "src/meta/funprint.fun.ml"
open! Print;;
open! Basis;;
(* Printing of functional proof terms *);;
(* Author: Carsten Schuermann *);;
module FunPrint(FunPrint__0: sig
                             (*! structure FunSyn' : FUNSYN !*)
                             module Formatter : FORMATTER
                             module Names : NAMES
                             (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
                             module Print : PRINT
                             end) : FUNPRINT
  =
  struct
    (*! structure FunSyn = FunSyn' !*);;
    module Formatter = Formatter;;
    open!
      struct
        module F = FunSyn;;
        module I = IntSyn;;
        module Fmt = Formatter;;
        module P = Print;;
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
        let rec formatFor' =
          function 
                   | (g_, (F.All (ld_, f_), s))
                       -> begin
                          match ld_
                          with 
                               | F.Prim d_
                                   -> let d'_ = Names.decName (g_, d_)
                                        in [(Fmt.String "{{");
                                            P.formatDec
                                            (g_, I.decSub (d'_, s));
                                            (Fmt.String "}}"); Fmt.break_] @
                                             (formatFor'
                                              ((I.Decl (g_, d'_)),
                                               (f_, I.dot1 s)))
                               | F.Block (F.CtxBlock (l, g'_))
                                   -> let (g''_, s'', fmts) =
                                        formatCtxBlock (g_, (g'_, s))
                                        in [(Fmt.String "{");
                                            (Fmt.Hbox fmts);
                                            (Fmt.String "}"); Fmt.break_] @
                                             (formatFor' (g''_, (f_, s'')))
                          end
                   | (g_, (F.Ex (d_, f_), s))
                       -> let d'_ = Names.decName (g_, d_)
                            in [(Fmt.String "[[");
                                P.formatDec (g_, I.decSub (d'_, s));
                                (Fmt.String "]]"); Fmt.break_] @
                                 (formatFor'
                                  ((I.Decl (g_, d'_)), (f_, I.dot1 s)))
                   | (g_, (true_, s)) -> [(Fmt.String "True")];;
        let rec formatFor (psi_, f_) names =
          let rec nameLookup index = List.nth (names, index)
            in let rec formatFor1 =
                 function 
                          | (index, g_, (F.And (f1_, f2_), s))
                              -> (formatFor1 (index, g_, (f1_, s))) @
                                   ([Fmt.break_] @
                                      (formatFor1 (index + 1, g_, (f2_, s))))
                          | (index, g_, (f_, s))
                              -> [(Fmt.String (nameLookup index));
                                  Fmt.space_; (Fmt.String "::"); Fmt.space_;
                                  (Fmt.HVbox (formatFor' (g_, (f_, s))))]
                 in let rec formatFor0 args_ =
                      (Fmt.Vbox0 (0, 1, formatFor1 args_))
                      in begin
                           Names.varReset I.null_;
                           formatFor0 (0, F.makectx psi_, (f_, I.id))
                           end;;
        let rec formatForBare (g_, f_) =
          (Fmt.HVbox (formatFor' (g_, (f_, I.id))));;
        let rec formatPro args_ names =
          let rec nameLookup index = List.nth (names, index)
            in let rec blockName (g1_, g2_) =
                 let rec blockName' =
                   function 
                            | (g1_, null_) -> (g1_, I.null_)
                            | (g1_, I.Decl (g2_, d_))
                                -> let (g1'_, g2'_) = blockName' (g1_, g2_)
                                     in let d'_ = Names.decName (g1_, d_)
                                          in ((I.Decl (g1'_, d'_)),
                                              (I.Decl (g2'_, d'_)))
                   in let (g1'_, g2'_) = blockName' (g1_, g2_) in g2'_
                 in let rec ctxBlockName (g1_, F.CtxBlock (name, g2_)) =
                      (F.CtxBlock (name, blockName (g1_, g2_)))
                      in let rec decName =
                           function 
                                    | (g_, F.Prim d_)
                                        -> (F.Prim (Names.decName (g_, d_)))
                                    | (g_, F.Block cb_)
                                        -> (F.Block (ctxBlockName (g_, cb_)))
                           in let rec numberOfSplits ds_ =
                                let rec numberOfSplits' =
                                  function 
                                           | (empty_, n) -> n
                                           | (F.New (_, ds_), n)
                                               -> numberOfSplits' (ds_, n)
                                           | (F.App (_, ds_), n)
                                               -> numberOfSplits' (ds_, n)
                                           | (F.Lemma (_, ds_), n)
                                               -> numberOfSplits' (ds_, n)
                                           | (F.Split (_, ds_), n)
                                               -> numberOfSplits'
                                                  (ds_, n + 1)
                                           | (F.Left (_, ds_), n)
                                               -> numberOfSplits' (ds_, n)
                                           | (F.Right (_, ds_), n)
                                               -> numberOfSplits' (ds_, n)
                                  in numberOfSplits' (ds_, 0)
                                in let rec psiName (psi1_, s, psi2_, l) =
                                     let rec nameDec =
                                       function 
                                                | ((I.Dec (Some _, _) as d_),
                                                   name) -> d_
                                                | (I.Dec (None, v_), name)
                                                    -> (I.Dec
                                                        ((Some name), v_))
                                       in let rec namePsi =
                                            function 
                                                     | (I.Decl
                                                        (psi_, F.Prim d_), 1,
                                                        name)
                                                         -> (I.Decl
                                                             (psi_,
                                                              (F.Prim
                                                               (nameDec
                                                                (d_, name)))))
                                                     | (I.Decl
                                                        (psi_,
                                                         (F.Prim d_ as ld_)),
                                                        n, name)
                                                         -> (I.Decl
                                                             (namePsi
                                                              (psi_, 
                                                               n - 1, name),
                                                              ld_))
                                                     | (I.Decl
                                                        (psi_, F.Block
                                                         (F.CtxBlock
                                                          (label, g_))),
                                                        n, name)
                                                         -> let (psi'_, g'_)
                                                              =
                                                              nameG
                                                              (psi_, g_, n,
                                                               name,
                                                               function 
                                                                    | n'
                                                                    -> namePsi
                                                                    (psi_,
                                                                    n', name))
                                                              in (I.Decl
                                                                  (psi'_,
                                                                   (F.Block
                                                                    ((F.CtxBlock
                                                                    (label,
                                                                    g'_))))))
                                          and nameG =
                                            function 
                                                     | (psi_, null_, n, name,
                                                        k) -> (k n, I.null_)
                                                     | (psi_, I.Decl
                                                        (g_, d_), 1, name, k)
                                                         -> (psi_,
                                                             (I.Decl
                                                              (g_,
                                                               nameDec
                                                               (d_, name))))
                                                     | (psi_, I.Decl
                                                        (g_, d_), n, name, k)
                                                         -> let (psi'_, g'_)
                                                              =
                                                              nameG
                                                              (psi_, g_,
                                                               n - 1, name,
                                                               k)
                                                              in (psi'_,
                                                                  (I.Decl
                                                                   (g'_, d_)))
                                            in let rec ignore =
                                                 function 
                                                          | (s, 0) -> s
                                                          | (I.Dot (_, s), k)
                                                              -> ignore
                                                                 (s, k - 1)
                                                          | (I.Shift n, k)
                                                              -> ignore
                                                                 ((I.Dot
                                                                   ((I.Idx
                                                                    (n + 1)),
                                                                    (I.Shift
                                                                    (n + 1)))),
                                                                  k - 1)
                                                 in let rec copyNames arg__1
                                                      arg__2 =
                                                      begin
                                                      match (arg__1, arg__2)
                                                      with 
                                                           | ((I.Shift n,
                                                               (I.Decl _ as
                                                                 g_)),
                                                              psi1_)
                                                               -> copyNames
                                                                  ((I.Dot
                                                                    ((I.Idx
                                                                    (n + 1)),
                                                                    (I.Shift
                                                                    (n + 1)))),
                                                                   g_)
                                                                  psi1_
                                                           | ((I.Dot
                                                               (I.Exp _, s),
                                                               I.Decl
                                                               (g_, _)),
                                                              psi1_)
                                                               -> copyNames
                                                                  (s, g_)
                                                                  psi1_
                                                           | ((I.Dot
                                                               (I.Idx k, s),
                                                               I.Decl
                                                               (g_, I.Dec
                                                                (None, _))),
                                                              psi1_)
                                                               -> copyNames
                                                                  (s, g_)
                                                                  psi1_
                                                           | ((I.Dot
                                                               (I.Idx k, s),
                                                               I.Decl
                                                               (g_, I.Dec
                                                                (Some name,
                                                                 _))),
                                                              psi1_)
                                                               -> let psi1'_
                                                                    =
                                                                    namePsi
                                                                    (psi1_,
                                                                    k, name)
                                                                    in 
                                                                    copyNames
                                                                    (s, g_)
                                                                    psi1'_
                                                           | ((I.Shift _,
                                                               null_),
                                                              psi1_) -> psi1_
                                                      end
                                                      in let rec psiName' =
                                                           function 
                                                                    | 
                                                                    null_
                                                                    -> I.null_
                                                                    | 
                                                                    I.Decl
                                                                    (psi_,
                                                                    d_)
                                                                    -> 
                                                                    let psi'_
                                                                    =
                                                                    psiName'
                                                                    psi_
                                                                    in 
                                                                    (I.Decl
                                                                    (psi'_,
                                                                    decName
                                                                    (F.makectx
                                                                    psi'_,
                                                                    d_)))
                                                           in psiName'
                                                              (copyNames
                                                               (ignore (s, l),
                                                                F.makectx
                                                                psi2_)
                                                               psi1_)
                                     in let rec merge =
                                          function 
                                                   | (g1_, null_) -> g1_
                                                   | (g1_, I.Decl (g2_, d_))
                                                       -> (I.Decl
                                                           (merge (g1_, g2_),
                                                            d_))
                                          in let rec formatCtx (psi_, g_) =
                                               let g0_ = F.makectx psi_
                                                 in let rec formatCtx' =
                                                      function 
                                                               | null_ -> []
                                                               | I.Decl
                                                                   (null_,
                                                                    I.Dec
                                                                    (Some
                                                                    name, v_))
                                                                   -> 
                                                                   [(Fmt.String
                                                                    name);
                                                                    (Fmt.String
                                                                    ":");
                                                                    Print.formatExp
                                                                    (g0_, v_)]
                                                               | I.Decl
                                                                   (g_, I.Dec
                                                                    (Some
                                                                    name, v_))
                                                                   -> 
                                                                   (formatCtx'
                                                                    g_) @
                                                                    [(Fmt.String
                                                                    ",");
                                                                    Fmt.break_;
                                                                    (Fmt.String
                                                                    name);
                                                                    (Fmt.String
                                                                    ":");
                                                                    Print.formatExp
                                                                    (merge
                                                                    (g0_, g_),
                                                                    v_)]
                                                      in (Fmt.Hbox
                                                          (((Fmt.String "|")
                                                            :: (formatCtx' g_)
                                                                 @
                                                                 [(Fmt.String
                                                                   "|")])))
                                               in let rec formatTuple
                                                    (psi_, p_) =
                                                    let rec formatTuple' =
                                                      function 
                                                               | unit_ -> []
                                                               | F.Inx
                                                                   (m_,
                                                                    unit_)
                                                                   -> 
                                                                   [Print.formatExp
                                                                    (F.makectx
                                                                    psi_, m_)]
                                                               | F.Inx
                                                                   (m_, p'_)
                                                                   -> 
                                                                   (Print.formatExp
                                                                    (F.makectx
                                                                    psi_, m_)
                                                                    :: 
                                                                    (Fmt.String
                                                                    ",")
                                                                    :: Fmt.break_
                                                                    :: 
                                                                    formatTuple'
                                                                    p'_)
                                                      in begin
                                                         match p_
                                                         with 
                                                              | F.Inx
                                                                  (_, unit_)
                                                                  -> 
                                                                  (Fmt.Hbox
                                                                   (formatTuple'
                                                                    p_))
                                                              | _
                                                                  -> 
                                                                  (Fmt.HVbox0
                                                                   (1, 1, 1,
                                                                    ((Fmt.String
                                                                    "(")
                                                                    :: 
                                                                    (formatTuple'
                                                                    p_) @
                                                                    [(Fmt.String
                                                                    ")")])))
                                                         end
                                                    in let
                                                         rec formatSplitArgs
                                                         (psi_, l_) =
                                                         let
                                                           rec formatSplitArgs'
                                                           =
                                                           function 
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    (m_
                                                                    :: [])
                                                                    -> 
                                                                    [Print.formatExp
                                                                    (F.makectx
                                                                    psi_, m_)]
                                                                    | 
                                                                    (m_
                                                                    :: l_)
                                                                    -> 
                                                                    (Print.formatExp
                                                                    (F.makectx
                                                                    psi_, m_)
                                                                    :: 
                                                                    (Fmt.String
                                                                    ",")
                                                                    :: Fmt.break_
                                                                    :: 
                                                                    formatSplitArgs'
                                                                    l_)
                                                           in begin
                                                           if
                                                           (List.length l_) =
                                                             1
                                                           then
                                                           (Fmt.Hbox
                                                            (formatSplitArgs'
                                                             l_))
                                                           else
                                                           (Fmt.HVbox0
                                                            (1, 1, 1,
                                                             ((Fmt.String
                                                               "(")
                                                              :: (formatSplitArgs'
                                                                  l_) @
                                                                   [(Fmt.String
                                                                    ")")])))
                                                           end
                                                         in let
                                                              rec frontToExp
                                                              =
                                                              function 
                                                                    | I.Idx k
                                                                    -> (I.Root
                                                                    ((I.BVar
                                                                    k),
                                                                    I.nil_))
                                                                    | I.Exp
                                                                    u_ -> u_
                                                              in let
                                                                   rec formatDecs1
                                                                   =
                                                                   function 
                                                                    | (psi_,
                                                                    F.Split
                                                                    (xx, ds_),
                                                                    I.Dot
                                                                    (ft_, s1),
                                                                    l_)
                                                                    -> formatDecs1
                                                                    (psi_,
                                                                    ds_, s1,
                                                                    (frontToExp
                                                                    ft_
                                                                    :: l_))
                                                                    | (psi_,
                                                                    empty_,
                                                                    s1, l_)
                                                                    -> l_
                                                                    | (psi_,
                                                                    ds_,
                                                                    I.Shift
                                                                    n, l_)
                                                                    -> formatDecs1
                                                                    (psi_,
                                                                    ds_,
                                                                    (I.Dot
                                                                    ((I.Idx
                                                                    (n + 1)),
                                                                    (I.Shift
                                                                    (n + 1)))),
                                                                    l_)
                                                                   in 
                                                                   let
                                                                    rec formatDecs0
                                                                    =
                                                                    function 
                                                                    | (psi_,
                                                                    F.App
                                                                    ((xx, m_),
                                                                    ds_))
                                                                    -> let
                                                                    (ds'_,
                                                                    s_) =
                                                                    formatDecs0
                                                                    (psi_,
                                                                    ds_)
                                                                    in (ds'_,
                                                                    (I.App
                                                                    (m_, s_)))
                                                                    | (psi_,
                                                                    ds_)
                                                                    -> (ds_,
                                                                    I.nil_)
                                                                    in 
                                                                    let
                                                                    rec formatDecs
                                                                    =
                                                                    function 
                                                                    | (index,
                                                                    psi_,
                                                                    (F.App
                                                                    ((xx, _),
                                                                    p_) as
                                                                    ds_),
                                                                    (psi1_,
                                                                    s1))
                                                                    -> let
                                                                    (ds'_,
                                                                    s_) =
                                                                    formatDecs0
                                                                    (psi_,
                                                                    ds_)
                                                                    in let
                                                                    l'_ =
                                                                    formatDecs1
                                                                    (psi_,
                                                                    ds'_, s1,
                                                                    [])
                                                                    in let
                                                                    name =
                                                                    nameLookup
                                                                    index
                                                                    in (Fmt.Hbox
                                                                    [formatSplitArgs
                                                                    (psi1_,
                                                                    l'_);
                                                                    Fmt.space_;
                                                                    (Fmt.String
                                                                    "=");
                                                                    Fmt.break_;
                                                                    (Fmt.HVbox
                                                                    (((Fmt.String
                                                                    name)
                                                                    :: Fmt.break_
                                                                    :: 
                                                                    Print.formatSpine
                                                                    (F.makectx
                                                                    psi_, s_))))])
                                                                    | (index,
                                                                    psi_,
                                                                    F.New
                                                                    ((F.CtxBlock
                                                                    (_, g_)
                                                                    as b_),
                                                                    ds_),
                                                                    (psi1_,
                                                                    s1))
                                                                    -> let
                                                                    b'_ =
                                                                    ctxBlockName
                                                                    (F.makectx
                                                                    psi_, b_)
                                                                    in let
                                                                    fmt =
                                                                    formatDecs
                                                                    (index,
                                                                    (I.Decl
                                                                    (psi_,
                                                                    (F.Block
                                                                    b'_))),
                                                                    ds_,
                                                                    (psi1_,
                                                                    s1))
                                                                    in (Fmt.Vbox
                                                                    [formatCtx
                                                                    (psi_,
                                                                    g_);
                                                                    Fmt.break_;
                                                                    fmt])
                                                                    | (index,
                                                                    psi_,
                                                                    F.Lemma
                                                                    (lemma,
                                                                    ds_),
                                                                    (psi1_,
                                                                    s1))
                                                                    -> let
                                                                    (ds'_,
                                                                    s_) =
                                                                    formatDecs0
                                                                    (psi_,
                                                                    ds_)
                                                                    in let
                                                                    l'_ =
                                                                    formatDecs1
                                                                    (psi_,
                                                                    ds'_, s1,
                                                                    [])
                                                                    in let
                                                                    F.LemmaDec
                                                                    (names,
                                                                    _, _) =
                                                                    F.lemmaLookup
                                                                    lemma
                                                                    in (Fmt.Hbox
                                                                    [formatSplitArgs
                                                                    (psi1_,
                                                                    l'_);
                                                                    Fmt.space_;
                                                                    (Fmt.String
                                                                    "=");
                                                                    Fmt.break_;
                                                                    (Fmt.HVbox
                                                                    (((Fmt.String
                                                                    (List.nth
                                                                    (names,
                                                                    index)))
                                                                    :: Fmt.break_
                                                                    :: 
                                                                    Print.formatSpine
                                                                    (F.makectx
                                                                    psi_, s_))))])
                                                                    | (index,
                                                                    psi_,
                                                                    F.Left
                                                                    (_, ds_),
                                                                    (psi1_,
                                                                    s1))
                                                                    -> let
                                                                    fmt =
                                                                    formatDecs
                                                                    (index,
                                                                    psi_,
                                                                    ds_,
                                                                    (psi1_,
                                                                    s1))
                                                                    in fmt
                                                                    | (index,
                                                                    psi_,
                                                                    F.Right
                                                                    (_, ds_),
                                                                    (psi1_,
                                                                    s1))
                                                                    -> let
                                                                    fmt =
                                                                    formatDecs
                                                                    (index +
                                                                    1, psi_,
                                                                    ds_,
                                                                    (psi1_,
                                                                    s1))
                                                                    in fmt
                                                                    in 
                                                                    let
                                                                    rec formatLet
                                                                    =
                                                                    function 
                                                                    | (psi_,
                                                                    F.Let
                                                                    (ds_,
                                                                    F.Case
                                                                    (F.Opts
                                                                    (((psi1_,
                                                                    s1,
                                                                    (F.Let _
                                                                    as p1_))
                                                                    :: [])))),
                                                                    fmts)
                                                                    -> let
                                                                    psi1'_ =
                                                                    psiName
                                                                    (psi1_,
                                                                    s1, psi_,
                                                                    numberOfSplits
                                                                    ds_)
                                                                    in let
                                                                    fmt =
                                                                    formatDecs
                                                                    (0, psi_,
                                                                    ds_,
                                                                    (psi1'_,
                                                                    s1))
                                                                    in formatLet
                                                                    (psi1'_,
                                                                    p1_,
                                                                    fmts @
                                                                    [fmt;
                                                                    Fmt.break_])
                                                                    | (psi_,
                                                                    F.Let
                                                                    (ds_,
                                                                    F.Case
                                                                    (F.Opts
                                                                    (((psi1_,
                                                                    s1, p1_)
                                                                    :: [])))),
                                                                    fmts)
                                                                    -> let
                                                                    psi1'_ =
                                                                    psiName
                                                                    (psi1_,
                                                                    s1, psi_,
                                                                    numberOfSplits
                                                                    ds_)
                                                                    in let
                                                                    fmt =
                                                                    formatDecs
                                                                    (0, psi_,
                                                                    ds_,
                                                                    (psi1'_,
                                                                    s1))
                                                                    in (Fmt.Vbox0
                                                                    (0, 1,
                                                                    [(Fmt.String
                                                                    "let");
                                                                    Fmt.break_;
                                                                    (Fmt.Spaces
                                                                    2);
                                                                    (Fmt.Vbox0
                                                                    (0, 1,
                                                                    fmts @
                                                                    [fmt]));
                                                                    Fmt.break_;
                                                                    (Fmt.String
                                                                    "in");
                                                                    Fmt.break_;
                                                                    (Fmt.Spaces
                                                                    2);
                                                                    formatPro3
                                                                    (psi1'_,
                                                                    p1_);
                                                                    Fmt.break_;
                                                                    (Fmt.String
                                                                    "end")]))
                                                                    and
                                                                    formatPro3
                                                                    =
                                                                    function 
                                                                    | (psi_,
                                                                    (unit_ as
                                                                    p_))
                                                                    -> formatTuple
                                                                    (psi_,
                                                                    p_)
                                                                    | (psi_,
                                                                    (F.Inx _
                                                                    as p_))
                                                                    -> formatTuple
                                                                    (psi_,
                                                                    p_)
                                                                    | (psi_,
                                                                    (F.Let _
                                                                    as p_))
                                                                    -> formatLet
                                                                    (psi_,
                                                                    p_, [])
                                                                    in 
                                                                    let
                                                                    rec argsToSpine
                                                                    =
                                                                    function 
                                                                    | (s,
                                                                    null_,
                                                                    s_) -> s_
                                                                    | (I.Shift
                                                                    n, psi_,
                                                                    s_)
                                                                    -> argsToSpine
                                                                    ((I.Dot
                                                                    ((I.Idx
                                                                    (n + 1)),
                                                                    (I.Shift
                                                                    (n + 1)))),
                                                                    psi_, s_)
                                                                    | (I.Dot
                                                                    (ft_, s),
                                                                    I.Decl
                                                                    (psi_,
                                                                    d_), s_)
                                                                    -> argsToSpine
                                                                    (s, psi_,
                                                                    (I.App
                                                                    (frontToExp
                                                                    ft_, s_)))
                                                                    in 
                                                                    let
                                                                    rec formatHead
                                                                    (index,
                                                                    psi'_, s,
                                                                    psi_) =
                                                                    (Fmt.Hbox
                                                                    [Fmt.space_;
                                                                    (Fmt.HVbox
                                                                    (((Fmt.String
                                                                    (nameLookup
                                                                    index))
                                                                    :: Fmt.break_
                                                                    :: 
                                                                    Print.formatSpine
                                                                    (F.makectx
                                                                    psi'_,
                                                                    argsToSpine
                                                                    (s, psi_,
                                                                    I.nil_)))))])
                                                                    in 
                                                                    let
                                                                    rec formatPro2
                                                                    =
                                                                    function 
                                                                    | (index,
                                                                    psi_, [])
                                                                    -> []
                                                                    | (index,
                                                                    psi_,
                                                                    ((psi'_,
                                                                    s, p_)
                                                                    :: []))
                                                                    -> let
                                                                    psi''_ =
                                                                    psiName
                                                                    (psi'_,
                                                                    s, psi_,
                                                                    0)
                                                                    in let
                                                                    fhead =
                                                                    begin
                                                                    if
                                                                    index = 0
                                                                    then
                                                                    "fun"
                                                                    else
                                                                    "and" end
                                                                    in [(Fmt.HVbox0
                                                                    (1, 5, 1,
                                                                    [(Fmt.String
                                                                    fhead);
                                                                    formatHead
                                                                    (index,
                                                                    psi''_,
                                                                    s, psi_);
                                                                    Fmt.space_;
                                                                    (Fmt.String
                                                                    "=");
                                                                    Fmt.break_;
                                                                    formatPro3
                                                                    (psi''_,
                                                                    p_)]));
                                                                    Fmt.break_]
                                                                    | (index,
                                                                    psi_,
                                                                    ((psi'_,
                                                                    s, p_)
                                                                    :: o_))
                                                                    -> let
                                                                    psi''_ =
                                                                    psiName
                                                                    (psi'_,
                                                                    s, psi_,
                                                                    0)
                                                                    in (formatPro2
                                                                    (index,
                                                                    psi_, o_))
                                                                    @
                                                                    [(Fmt.HVbox0
                                                                    (1, 5, 1,
                                                                    [(Fmt.String
                                                                    "  |");
                                                                    formatHead
                                                                    (index,
                                                                    psi''_,
                                                                    s, psi_);
                                                                    Fmt.space_;
                                                                    (Fmt.String
                                                                    "=");
                                                                    Fmt.break_;
                                                                    formatPro3
                                                                    (psi''_,
                                                                    p_)]));
                                                                    Fmt.break_]
                                                                    in 
                                                                    let
                                                                    rec formatPro1
                                                                    =
                                                                    function 
                                                                    | (index,
                                                                    psi_,
                                                                    F.Lam
                                                                    (d_, p_))
                                                                    -> formatPro1
                                                                    (index,
                                                                    (I.Decl
                                                                    (psi_,
                                                                    decName
                                                                    (F.makectx
                                                                    psi_, d_))),
                                                                    p_)
                                                                    | (index,
                                                                    psi_,
                                                                    F.Case
                                                                    (F.Opts
                                                                    os_))
                                                                    -> formatPro2
                                                                    (index,
                                                                    psi_,
                                                                    os_)
                                                                    | (index,
                                                                    psi_,
                                                                    F.Pair
                                                                    (p1_,
                                                                    p2_))
                                                                    -> (formatPro1
                                                                    (index,
                                                                    psi_,
                                                                    p1_)) @
                                                                    (formatPro1
                                                                    (index +
                                                                    1, psi_,
                                                                    p2_))
                                                                    in 
                                                                    let
                                                                    rec formatPro0
                                                                    (psi_,
                                                                    F.Rec
                                                                    (dd_, p_))
                                                                    =
                                                                    (Fmt.Vbox0
                                                                    (0, 1,
                                                                    formatPro1
                                                                    (0, psi_,
                                                                    p_)))
                                                                    in 
                                                                    begin
                                                                    Names.varReset
                                                                    I.null_;
                                                                    formatPro0
                                                                    args_
                                                                    end;;
        let rec formatLemmaDec (F.LemmaDec (names, p_, f_)) =
          (Fmt.Vbox0
           (0, 1,
            [formatFor (I.null_, f_) names; Fmt.break_;
             formatPro (I.null_, p_) names]));;
        let rec forToString args_ names =
          Fmt.makestring_fmt (formatFor args_ names);;
        let rec proToString args_ names =
          Fmt.makestring_fmt (formatPro args_ names);;
        let rec lemmaDecToString args_ =
          Fmt.makestring_fmt (formatLemmaDec args_);;
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
    (* formatFor (Psi, F) names = fmt'
       formatForBare (Psi, F) = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi |- F = F1 ^ .. ^ Fn formula
       and  names is a list of n names,
       then fmt' is the pretty printed format
    *);;
    (* formatFor1 (index, G, (F, s)) = fmts'

           Invariant:
           If   |- G ctx
           and  G |- s : Psi
           and  Psi |- F1 ^ .. ^ F(index-1) ^ F formula
           then fmts' is a list of pretty printed formats for F
        *);;
    (* formatPro (Psi, P) names = fmt'

       Invariant:
       If   |- Psi ctx
       and  Psi; . |- P = rec x. (P1, P2, .. Pn) in F
       and  names is a list of n names,
       then fmt' is the pretty printed format of P
    *);;
    (* blockName (G1, G2) = G2'

           Invariant:
           If   G1 |- G2 ctx
           then G2' = G2 modulo new non-conficting variable names.
        *);;
    (* ctxBlockName (G1, CB) = CB'

           Invariant:
           If   G1 |- CB ctxblock
           then CB' = CB modulo new non-conficting variable names.
        *);;
    (* decName (G, LD) = LD'

           Invariant:
           If   G1 |- LD lfdec
           then LD' = LD modulo new non-conficting variable names.
        *);;
    (* numberOfSplits Ds = n'

           Invariant:
           If   Psi, Delta |- Ds :: Psi', Delta'
           then n'= |Psi'| - |Psi|
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
    (* merge (G1, G2) = G'

           Invariant:
           G' = G1, G2
        *);;
    (* formatCtx (Psi, G) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi |- G ctx
           then fmt' is a pretty print format of G
        *);;
    (* formatTuple (Psi, P) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Inx (M1, Inx ... (Mn, Unit))
           then fmt' is a pretty print format of (M1, .., Mn)
        *);;
    (* formatSplitArgs (Psi, L) = fmt'

           Invariant:
           If   |- Psi ctx
           and  L = (M1, .., Mn)
           and  Psi |- Mk:Ak for all 1<=k<=n
           then fmt' is a pretty print format of (M1, .., Mn)
        *);;
    (* frontToExp (Ft) = U'

           Invariant:
           G |- Ft = U' : V   for a G, V
        *);;
    (* formatDecs1 (Psi, Ds, s, L) = L'

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
        *);;
    (* formatDecs0 (Psi, Ds) = (Ds', S')

           Invariant:
           If   |- Psi ctx
           and  Psi ; Delta |- Ds : Psi', Delta'
           and  Ds = App M1 ... App Mn Ds'   (where Ds' starts with Split)
           then S' = (M1, M2 .. Mn)
           and  Psi1, Delta1 |- Ds' : Psi1', Delta1'
                (for some Psi1, Delta1, Psi1', Delta1')
        *);;
    (* formatDecs (index, Psi, Ds, (Psi1, s1)) = fmt'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- Ds : Psi'; Delta'
           and  Psi1 |- s1 : Psi, Psi'
           then fmt' is a pretty print format of Ds
        *);;
    (* formatLet (Psi, P, fmts) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P = Let . Case P' :: F
           and  fmts is a list of pretty print formats of P
           then fmts' extends fmts
           and  fmts also includes a pretty print format for P'
        *);;
    (* formatPro3 (Psi, P) = fmt

           Invariant:
           If   |- Psi ctx
           and  Psi; Delta |- P :: F
           and  P = let .. in .. end | <..,..> | <>
           then fmt is a pretty print of P
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
    (* formatHead (index, Psi1, s, Psi2) = fmt'

           Invariant:
           If    Psi1 |- s : Psi2
           then  fmt is a format of the entire head
           where index represents the function name
           and   s the spine.
        *);;
    (* formatPro2 (index, Psi, L) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi |- L a list of cases
           then fmts' list of pretty print formats of L
        *);;
    (* formatPro1 (index, Psi, P) = fmts'

           Invariant:
           If   |- Psi ctx
           and  Psi; . |- P :: F
           and  P is either a Lam .. | Case ... | Pair ...
           then fmts' is alist of pretty print formats of P
        *);;
    (* formatPro0 (Psi, P) = fmt'
           If   |- Psi ctx
           and  Psi; . |- P :: F
           then fmt' is a pretty print format of P
        *);;
    let formatFor = formatFor;;
    let formatForBare = formatForBare;;
    let formatPro = formatPro;;
    let formatLemmaDec = formatLemmaDec;;
    let forToString = forToString;;
    let proToString = proToString;;
    let lemmaDecToString = lemmaDecToString;;
    end;;
(*! sharing Print.IntSyn = FunSyn'.IntSyn !*);;
(* signature FUNPRINT *);;
# 1 "src/meta/funprint.sml.ml"
