open! Basis;;
open!
  struct
    open FunSyn;;
    open FunTypeCheck;;
    module I = IntSyn;;
    let _ = Twelf.loadFile "cp.elf";;
    let exp = (I.Root ((I.Const (valOf (Names.nameLookup "exp"))), I.nil_));;
    let exp' = (I.Root ((I.Const (valOf (Names.nameLookup "exp'"))), I.nil_));;
    let cp = (I.Const (valOf (Names.nameLookup "cp")));;
    let lam = (I.Const (valOf (Names.nameLookup "lam")));;
    let lam' = (I.Const (valOf (Names.nameLookup "lam'")));;
    let cp_lam = (I.Const (valOf (Names.nameLookup "cp_lam")));;
    let app = (I.Const (valOf (Names.nameLookup "app")));;
    let app' = (I.Const (valOf (Names.nameLookup "app'")));;
    let cp_app = (I.Const (valOf (Names.nameLookup "cp_app")));;
    let callcc = (I.Const (valOf (Names.nameLookup "callcc")));;
    let callcc' = (I.Const (valOf (Names.nameLookup "callcc'")));;
    let cp_callcc = (I.Const (valOf (Names.nameLookup "cp_callcc")));;
    let one = (I.Root ((I.BVar 1), I.nil_));;
    let two = (I.Root ((I.BVar 2), I.nil_));;
    let three = (I.Root ((I.BVar 3), I.nil_));;
    let four = (I.Root ((I.BVar 4), I.nil_));;
    let five = (I.Root ((I.BVar 5), I.nil_));;
    let six = (I.Root ((I.BVar 6), I.nil_));;
    let cpt_theorem =
      all_
      (prim_ ((I.Dec ((Some "E"), exp))),
       ex_
       ((I.Dec ((Some "E'"), exp')),
        ex_
        ((I.Dec
          ((Some "D"), (I.Root (cp, (I.App (two, (I.App (one, I.nil_)))))))),
         true_)));;
    let rec union =
      function 
               | (g_, null_) -> g_
               | (g_, I.Decl (g'_, d_)) -> (I.Decl (union (g_, g'_), d_));;
    let rec makectx =
      function 
               | null_ -> I.null_
               | I.Decl (g_, Prim d_) -> (I.Decl (makectx g_, d_))
               | I.Decl (g_, Block (CtxBlock (l, g'_)))
                   -> union (makectx g_, g'_);;
    let rec printCtx =
      function 
               | null_ -> ()
               | I.Decl (g_, Prim d_)
                   -> begin
                        printCtx g_;
                        TextIO.print
                        ((Print.decToString (makectx g_, d_)) ^ "\n")
                        end
               | I.Decl (g_, _)
                   -> begin
                        printCtx g_;TextIO.print "BLOCK\n"
                        end;;
    let rec print (psi_, u_) =
      TextIO.print ((Print.expToString (makectx psi_, u_)) ^ "\n");;
    let cpt_proof =
      rec_
      (mDec_ ((Some "IH"), cpt_theorem),
       lam_
       (prim_ ((I.Dec ((Some "E"), exp))),
        case_
        (opts_
         [((I.Decl
            (I.null_,
             block_
             (ctxBlock_
              ((Some 1),
               (I.Decl
                ((I.Decl
                  ((I.Decl (I.null_, (I.Dec ((Some "x"), exp)))),
                   (I.Dec ((Some "y"), exp')))),
                 (I.Dec
                  ((Some "u"),
                   (I.Root (cp, (I.App (two, (I.App (one, I.nil_)))))))))))))),
           (I.Dot ((I.Idx 3), I.id)), inx_ (two, inx_ (one, unit_)));
          ((I.Decl
            ((I.Decl
              (I.null_,
               block_
               (ctxBlock_
                ((Some 2),
                 (I.Decl
                  ((I.Decl
                    ((I.Decl
                      (I.null_,
                       (I.Dec
                        ((Some "c"),
                         (I.Pi (((I.Dec (None, exp)), I.no_), exp)))))),
                     (I.Dec
                      ((Some "d"),
                       (I.Pi (((I.Dec (None, exp')), I.no_), exp')))))),
                   (I.Dec
                    ((Some "e"),
                     (I.Pi
                      (((I.Dec ((Some "x"), exp)), I.maybe_),
                       (I.Pi
                        (((I.Dec ((Some "y"), exp')), I.maybe_),
                         (I.Pi
                          (((I.Dec
                             (None,
                              (I.Root
                               (cp, (I.App (two, (I.App (one, I.nil_)))))))),
                            I.no_),
                           (I.Root
                            (cp,
                             (I.App
                              ((I.Root ((I.BVar 5), (I.App (three, I.nil_)))),
                               (I.App
                                ((I.Root ((I.BVar 4), (I.App (two, I.nil_)))),
                                 I.nil_)))))))))))))))))))),
             prim_ ((I.Dec ((Some "E"), exp))))),
           (I.Dot
            ((I.Exp ((I.Root ((I.BVar 4), (I.App (one, I.nil_)))), exp)),
             I.id)),
           let_
           (app_ ((1, one), split_ (1, split_ (1, Empty))),
            inx_
            ((I.Root ((I.BVar 5), (I.App (two, I.nil_)))),
             inx_
             ((I.Root
               ((I.BVar 4),
                (I.App (three, (I.App (two, (I.App (one, I.nil_)))))))),
              unit_))));
          ((I.Decl
            (I.null_,
             prim_
             ((I.Dec
               ((Some "E1"),
                (I.Pi (((I.Dec ((Some "x"), exp)), I.no_), exp))))))),
           (I.Dot
            ((I.Exp ((I.Root (lam, (I.App (one, I.nil_)))), exp)),
             (I.Shift 1))),
           let_
           (new_
            (ctxBlock_
             ((Some 1),
              (I.Decl
               ((I.Decl
                 ((I.Decl (I.null_, (I.Dec ((Some "x"), exp)))),
                  (I.Dec ((Some "y"), exp')))),
                (I.Dec
                 ((Some "u"),
                  (I.Root (cp, (I.App (two, (I.App (one, I.nil_))))))))))),
             app_
             ((1, (I.Redex (four, (I.App (three, I.nil_))))),
              split_ (1, split_ (1, Empty)))),
            inx_
            ((I.Root (lam', (I.App (two, I.nil_)))),
             inx_
             ((I.Root
               (cp_lam,
                (I.App (three, (I.App (two, (I.App (one, I.nil_)))))))),
              unit_))));
          ((I.Decl
            ((I.Decl (I.null_, prim_ ((I.Dec ((Some "E1"), exp))))),
             prim_ ((I.Dec ((Some "E2"), exp))))),
           (I.Dot
            ((I.Exp
              ((I.Root (app, (I.App (two, (I.App (one, I.nil_)))))), exp)),
             (I.Shift 2))),
           let_
           (app_
            ((1, two),
             split_
             (1,
              split_ (1, app_ ((4, three), split_ (1, split_ (1, Empty)))))),
            inx_
            ((I.Root (app', (I.App (four, (I.App (two, I.nil_)))))),
             inx_
             ((I.Root
               (cp_app,
                (I.App
                 (five,
                  (I.App
                   (two,
                    (I.App
                     (six,
                      (I.App (four, (I.App (one, (I.App (three, I.nil_)))))))))))))),
              unit_))));
          ((I.Decl
            (I.null_,
             prim_
             ((I.Dec
               ((Some "E1"),
                (I.Pi
                 (((I.Dec
                    ((Some "x"), (I.Pi (((I.Dec (None, exp)), I.no_), exp)))),
                   I.no_),
                  exp))))))),
           (I.Dot
            ((I.Exp ((I.Root (callcc, (I.App (one, I.nil_)))), exp)),
             (I.Shift 1))),
           let_
           (new_
            (ctxBlock_
             ((Some 2),
              (I.Decl
               ((I.Decl
                 ((I.Decl
                   (I.null_,
                    (I.Dec
                     ((Some "c"), (I.Pi (((I.Dec (None, exp)), I.no_), exp)))))),
                  (I.Dec
                   ((Some "d"), (I.Pi (((I.Dec (None, exp')), I.no_), exp')))))),
                (I.Dec
                 ((Some "e"),
                  (I.Pi
                   (((I.Dec ((Some "x"), exp)), I.maybe_),
                    (I.Pi
                     (((I.Dec ((Some "y"), exp')), I.maybe_),
                      (I.Pi
                       (((I.Dec
                          (None,
                           (I.Root
                            (cp, (I.App (two, (I.App (one, I.nil_)))))))),
                         I.no_),
                        (I.Root
                         (cp,
                          (I.App
                           ((I.Root ((I.BVar 5), (I.App (three, I.nil_)))),
                            (I.App
                             ((I.Root ((I.BVar 4), (I.App (two, I.nil_)))),
                              I.nil_))))))))))))))))),
             app_
             ((1, (I.Redex (four, (I.App (three, I.nil_))))),
              split_ (1, split_ (1, Empty)))),
            inx_
            ((I.Root (callcc', (I.App (two, I.nil_)))),
             inx_
             ((I.Root
               (cp_callcc,
                (I.App (three, (I.App (two, (I.App (one, I.nil_)))))))),
              unit_))))])));;
    end;;
(* the copy function theorem, internal format *);;
(* ------------------------------------------------------------------------ *);;
(* ------------------------------------------------------------------------ *);;
(* ------------------------------------------------------------------------ *);;
(* ------------------------------------------------------------------------- *);;
(* ------------------------------------------------------------------------- *);;
let print = print;;
let printCtx = printCtx;;
let cpt_proof = cpt_proof;;
let cpt_theorem = cpt_theorem;;
let _ =
  try check (cpt_proof, cpt_theorem)
  with 
       | Error s -> TextIO.print (s ^ "\n")
       | TypeCheck.Error s -> TextIO.print (s ^ "\n");;