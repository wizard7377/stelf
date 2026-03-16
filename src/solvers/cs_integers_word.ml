(* # 1 "src/solvers/cs_integers_word.sig.ml" *)

(* # 1 "src/solvers/cs_integers_word.fun.ml" *)
open! Basis

module Cs_int_word (CSIntWord__0 : sig
  (* Solver for machine integers *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn !*)
  val wordSize : int
end) : Cs.CS = struct
  (*! structure Cs_manager = Cs_manager !*)
  module Whnf = CSIntWord__0.Whnf
  module Unify = CSIntWord__0.Unify

  open! struct
    open IntSyn

    module W = struct
      include LargeWord.Word

      let ( <= ) x y = LargeWord.Word.(x <= y)
      let ( >= ) x y = LargeWord.Word.(x >= y)
      let ( > ) x y = LargeWord.Word.(x > y)
      let ( + ) x y = LargeWord.Word.(x + y)
      let ( - ) x y = LargeWord.Word.(x - y)
      let ( * ) x y = LargeWord.Word.(x * y)
      let ( mod ) x y = LargeWord.Word.(x mod y)
      let ( >> ) w n = w lsr n
      let ( << ) w n = w lsl n
      let ( ~>> ) w n = w asr n
    end

    module FX = Cs_manager.Fixity
    module MS = ModeSyn

    exception MyFgnCnstrRepPlus of dctx * exp * exp * exp * exp
    exception MyFgnCnstrRepTimes of dctx * exp * exp * exp * exp
    exception MyFgnCnstrRepQuot of dctx * exp * exp * exp * exp

    let wordSize' = Int.min (CSIntWord__0.wordSize, W.wordSize)
    let zero = W.fromInt 0
    let max = W.(W.notb zero >> Word.fromInt (W.wordSize - wordSize'))
    let rec numCheck d = W.( <= ) d max

    let rec plusCheck (d1, d2) =
      let d3 = W.(d1 + d2) in
      W.(d3 >= d1) && W.(d3 >= d2) && W.( <= ) d3 max

    let rec timesCheck (d1, d2) =
      begin if d1 = zero || d2 = zero then true
      else
        let d3 = W.div (W.div (max, d1), d2) in
        W.(d3 > zero)
      end

    let rec quotCheck (d1, d2) = W.(d2 > zero)
    let myID = (ref (-1) : csid ref)
    let wordID = (ref (-1) : cid ref)
    let rec word () = Root (Const !wordID, Nil)
    let plusID = (ref (-1) : cid ref)
    let timesID = (ref (-1) : cid ref)
    let quotID = (ref (-1) : cid ref)

    let rec plusExp (u_, v_, w_) =
      Root (Const !plusID, App (u_, App (v_, App (w_, Nil))))

    let pi_ (name, ty, body) = Pi ((Dec (Some name, ty), No), body)

    let rec timesExp (u_, v_, w_) =
      Root (Const !timesID, App (u_, App (v_, App (w_, Nil))))

    let rec quotExp (u_, v_, w_) =
      Root (Const !quotID, App (u_, App (v_, App (w_, Nil))))

    let provePlusID = (ref (-1) : cid ref)
    let proveTimesID = (ref (-1) : cid ref)
    let proveQuotID = (ref (-1) : cid ref)
    let proofPlusID = (ref (-1) : cid ref)
    let proofTimesID = (ref (-1) : cid ref)
    let proofQuotID = (ref (-1) : cid ref)

    let rec provePlusExp (u_, v_, w_, p_) =
      Root (Const !provePlusID, App (u_, App (v_, App (w_, App (p_, Nil)))))

    let rec proofPlusExp (u_, v_, w_, p_) =
      Root (Const !proofPlusID, App (u_, App (v_, App (w_, App (p_, Nil)))))

    let rec proofTimesExp (u_, v_, w_, p_) =
      Root (Const !proofTimesID, App (u_, App (v_, App (w_, App (p_, Nil)))))

    let rec proveTimesExp (u_, v_, w_, p_) =
      Root (Const !proveTimesID, App (u_, App (v_, App (w_, App (p_, Nil)))))

    let rec proveQuotExp (u_, v_, w_, p_) =
      Root (Const !proveQuotID, App (u_, App (v_, App (w_, App (p_, Nil)))))

    let rec proofQuotExp (u_, v_, w_, p_) =
      Root (Const !proofQuotID, App (u_, App (v_, App (w_, App (p_, Nil)))))

    let rec numberConDec d =
      ConDec (W.fmt StringCvt.Dec d, None, 0, Normal, word (), Type)

    let rec numberExp d = Root (FgnConst (!myID, numberConDec d), Nil)

    let rec scanNumber str =
      let rec check = function
        | _ :: _ as chars -> List.all Char.isDigit chars
        | [] -> false
      in
      begin if check (String.explode str) then begin
        match StringCvt.scanString (W.scan StringCvt.Dec) str with
        | Some d -> begin if numCheck d then Some d else None end
        | None -> None
      end
      else None
      end

    let rec parseNumber string =
      begin match scanNumber string with
      | Some d -> Some (numberConDec d)
      | None -> None
      end

    let rec plusPfConDec (d1, d2) =
      let d3 = W.(d1 + d2) in
      ConDec
        ( (W.fmt StringCvt.Dec d1 ^ "+") ^ W.fmt StringCvt.Dec d2,
          None,
          0,
          Normal,
          plusExp (numberExp d1, numberExp d2, numberExp d3),
          Type )

    let rec plusPfExp ds = Root (FgnConst (!myID, plusPfConDec ds), Nil)

    let rec timesPfConDec (d1, d2) =
      let d3 = W.(d1 * d2) in
      ConDec
        ( (W.fmt StringCvt.Dec d1 ^ "*") ^ W.fmt StringCvt.Dec d2,
          None,
          0,
          Normal,
          timesExp (numberExp d1, numberExp d2, numberExp d3),
          Type )

    let rec timesPfExp ds = Root (FgnConst (!myID, timesPfConDec ds), Nil)

    let rec quotPfConDec (d1, d2) =
      let d3 = W.div (d1, d2) in
      ConDec
        ( (W.fmt StringCvt.Dec d1 ^ "/") ^ W.fmt StringCvt.Dec d2,
          None,
          0,
          Normal,
          quotExp (numberExp d1, numberExp d2, numberExp d3),
          Type )

    let rec quotPfExp ds = Root (FgnConst (!myID, quotPfConDec ds), Nil)

    let rec scanBinopPf oper string =
      let args = String.tokens (function c -> c = oper) string in
      begin match args with
      | [ arg1; arg2 ] -> begin
          match
            ( StringCvt.scanString (W.scan StringCvt.Dec) arg1,
              StringCvt.scanString (W.scan StringCvt.Dec) arg2 )
          with
          | Some d1, Some d2 -> Some (d1, d2)
          | _ -> None
        end
      | _ -> None
      end

    let rec parseBinopPf oper string =
      begin match (oper, scanBinopPf oper string) with
      | '+', Some ds -> Some (plusPfConDec ds)
      | '*', Some ds -> Some (timesPfConDec ds)
      | '/', Some ds -> Some (quotPfConDec ds)
      | _ -> None
      end

    let parsePlusPf = parseBinopPf '+'
    let parseTimesPf = parseBinopPf '*'
    let parseQuotPf = parseBinopPf '/'

    let rec parseAll string =
      begin match parseNumber string with
      | Some conDec -> Some conDec
      | None -> begin
          match parsePlusPf string with
          | Some conDec -> Some conDec
          | None -> begin
              match parseTimesPf string with
              | Some conDec -> Some conDec
              | None -> parseQuotPf string
            end
        end
      end

    type fixTerm =
      | Num of W.word
      | PlusPf of W.word * W.word
      | TimesPf of W.word * W.word
      | QuotPf of W.word * W.word
      | Expr of (exp * sub)

    let rec fromExpW = function
      | (Root (FgnConst (cs, conDec), _), _) as us_ -> begin
          if cs = !myID then
            let string = conDecName conDec in
            begin match scanNumber string with
            | Some d -> Num d
            | None -> begin
                match scanBinopPf '/' string with
                | Some (d1, d2) -> QuotPf (d1, d2)
                | None -> begin
                    match scanBinopPf '+' string with
                    | Some (d1, d2) -> PlusPf (d1, d2)
                    | None -> begin
                        match scanBinopPf '*' string with
                        | Some (d1, d2) -> TimesPf (d1, d2)
                        | None -> Expr us_
                      end
                  end
              end
            end
          else Expr us_
        end
      | (Root (Def d, _), _) as us_ -> fromExpW (Whnf.expandDef us_)
      | us_ -> Expr us_

    and fromExp us_ = fromExpW (Whnf.whnf us_)

    let rec toExp = function
      | Num d -> numberExp d
      | PlusPf (d1, d2) -> plusPfExp (d1, d2)
      | TimesPf (d1, d2) -> timesPfExp (d1, d2)
      | QuotPf (d1, d2) -> quotPfExp (d1, d2)
      | Expr (u_, s_) -> EClo (u_, s_)

    let rec solveNumber (g_, s_, k) = Some (numberExp (W.fromInt k))
    let eclo_ (u_, s_) = EClo (u_, s_)

    let rec fst = function
      | App (u1_, _), s -> (u1_, s)
      | SClo (s_, s'), s -> fst (s_, comp (s', s))

    let rec snd = function
      | App (_, s_), s -> fst (s_, s)
      | SClo (s_, s'), s -> snd (s_, comp (s', s))

    let rec trd = function
      | App (_, s_), s -> snd (s_, s)
      | SClo (s_, s'), s -> trd (s_, comp (s', s))

    let rec fth = function
      | App (_, s_), s -> trd (s_, s)
      | SClo (s_, s'), s -> fth (s_, comp (s', s))

    let rec toInternalPlus (g_, u1_, u2_, u3_) () =
      [ (g_, plusExp (u1_, u2_, u3_)) ]

    and awakePlus (g_, proof, u1_, u2_, u3_) () =
      begin match solvePlus (g_, App (u1_, App (u2_, App (u3_, Nil))), 0) with
      | Some proof' -> Unify.unifiable (g_, (proof, id), (proof', id))
      | None -> false
      end

    and makeCnstrPlus (g_, proof, u1_, u2_, u3_) =
      FgnCnstr (!myID, MyFgnCnstrRepPlus (g_, proof, u1_, u2_, u3_))

    and solvePlus = function
      | g_, s_, 0 ->
          let us1_ = fst (s_, id) in
          let us2_ = snd (s_, id) in
          let us3_ = trd (s_, id) in
          begin match (fromExp us1_, fromExp us2_, fromExp us3_) with
          | Num d1, Num d2, Num d3 -> begin
              if (d3 = W.(d1 + d2)) && plusCheck (d1, d2) then
                Some (plusPfExp (d1, d2))
              else None
            end
          | Expr us1_, Num d2, Num d3 -> begin
              if
                W.(d3 >= d2)
                && Unify.unifiable (g_, us1_, (numberExp W.(d3 - d2), id))
              then Some (plusPfExp (W.(d3 - d2), d2))
              else None
            end
          | Num d1, Expr us2_, Num d3 -> begin
              if
                W.(d3 >= d1)
                && Unify.unifiable (g_, us2_, (numberExp W.(d3 - d1), id))
              then Some (plusPfExp (d1, W.(d3 - d1)))
              else None
            end
          | Num d1, Num d2, Expr us3_ -> begin
              if
                plusCheck (d1, d2)
                && Unify.unifiable (g_, us3_, (numberExp W.(d1 + d2), id))
              then Some (plusPfExp (d1, d2))
              else None
            end
          | _ ->
              let proof =
                newEVar (g_, plusExp (eclo_ us1_, eclo_ us2_, eclo_ us3_))
              in
              let cnstr =
                makeCnstrPlus (g_, proof, eclo_ us1_, eclo_ us2_, eclo_ us3_)
              in
              let _ =
                List.app
                  (function us_ -> Unify.delay (us_, ref cnstr))
                  [ us1_; us2_; us3_ ]
              in
              Some proof
          end
      | g_, s_, n -> None

    and toInternalTimes (g_, u1_, u2_, u3_) () =
      [ (g_, timesExp (u1_, u2_, u3_)) ]

    and awakeTimes (g_, proof, u1_, u2_, u3_) () =
      begin match solveTimes (g_, App (u1_, App (u2_, App (u3_, Nil))), 0) with
      | Some proof' -> Unify.unifiable (g_, (proof, id), (proof', id))
      | None -> false
      end

    and makeCnstrTimes (g_, proof, u1_, u2_, u3_) =
      FgnCnstr (!myID, MyFgnCnstrRepTimes (g_, proof, u1_, u2_, u3_))

    and solveTimes = function
      | g_, s_, 0 ->
          let us1_ = fst (s_, id) in
          let us2_ = snd (s_, id) in
          let us3_ = trd (s_, id) in
          begin match (fromExp us1_, fromExp us2_, fromExp us3_) with
          | Num d1, Num d2, Num d3 -> begin
              if (d3 = W.(d1 * d2)) && timesCheck (d1, d2) then
                Some (timesPfExp (d1, d2))
              else None
            end
          | Expr us1_, Num d2, Num d3 -> begin
              if d3 = zero && Unify.unifiable (g_, us1_, (numberExp zero, id))
              then Some (timesPfExp (zero, d2))
              else begin
                if
                  W.(d2 > zero)
                  && W.(d3 > zero)
                  && W.(d3 mod d2) = zero
                  && Unify.unifiable (g_, us1_, (numberExp (W.div (d3, d2)), id))
                then Some (timesPfExp (W.div (d3, d2), d2))
                else None
              end
            end
          | Num d1, Expr us2_, Num d3 -> begin
              if d3 = zero && Unify.unifiable (g_, us2_, (numberExp zero, id))
              then Some (timesPfExp (d1, zero))
              else begin
                if
                  W.(d1 > zero)
                  && W.(d3 > zero)
                  && W.(d3 mod d1) = zero
                  && Unify.unifiable (g_, us2_, (numberExp (W.div (d3, d1)), id))
                then Some (timesPfExp (d1, W.div (d3, d1)))
                else None
              end
            end
          | Num d1, Num d2, Expr us3_ -> begin
              if
                timesCheck (d1, d2)
                && Unify.unifiable (g_, us3_, (numberExp W.(d1 * d2), id))
              then Some (timesPfExp (d1, d2))
              else None
            end
          | _ ->
              let proof =
                newEVar (g_, timesExp (eclo_ us1_, eclo_ us2_, eclo_ us3_))
              in
              let cnstr =
                makeCnstrTimes (g_, proof, eclo_ us1_, eclo_ us2_, eclo_ us3_)
              in
              let _ =
                List.app
                  (function us_ -> Unify.delay (us_, ref cnstr))
                  [ us1_; us2_; us3_ ]
              in
              Some proof
          end
      | g_, s_, n -> None

    and toInternalQuot (g_, u1_, u2_, u3_) () =
      [ (g_, quotExp (u1_, u2_, u3_)) ]

    and awakeQuot (g_, proof, u1_, u2_, u3_) () =
      begin match solveQuot (g_, App (u1_, App (u2_, App (u3_, Nil))), 0) with
      | Some proof' -> Unify.unifiable (g_, (proof, id), (proof', id))
      | None -> false
      end

    and makeCnstrQuot (g_, proof, u1_, u2_, u3_) =
      FgnCnstr (!myID, MyFgnCnstrRepQuot (g_, proof, u1_, u2_, u3_))

    and solveQuot = function
      | g_, s_, 0 ->
          let us1_ = fst (s_, id) in
          let us2_ = snd (s_, id) in
          let us3_ = trd (s_, id) in
          begin match (fromExp us1_, fromExp us2_, fromExp us3_) with
          | Num d1, Num d2, Num d3 -> begin
              if quotCheck (d1, d2) && d3 = W.div (d1, d2) then
                Some (quotPfExp (d1, d2))
              else None
            end
          | Num d1, Num d2, Expr us3_ -> begin
              if
                quotCheck (d1, d2)
                && Unify.unifiable (g_, us3_, (numberExp (W.div (d1, d2)), id))
              then Some (quotPfExp (d1, d2))
              else None
            end
          | _ ->
              let proof =
                newEVar (g_, quotExp (eclo_ us1_, eclo_ us2_, eclo_ us3_))
              in
              let cnstr =
                makeCnstrQuot (g_, proof, eclo_ us1_, eclo_ us2_, eclo_ us3_)
              in
              let _ =
                List.app
                  (function us_ -> Unify.delay (us_, ref cnstr))
                  [ us1_; us2_; us3_ ]
              in
              Some proof
          end
      | g_, s_, n -> None

    let rec solveProvePlus (g_, s_, k) =
      let us1_ = fst (s_, id) in
      let us2_ = snd (s_, id) in
      let us3_ = trd (s_, id) in
      let us4_ = fth (s_, id) in
      begin match
        solvePlus
          (g_, App (eclo_ us1_, App (eclo_ us2_, App (eclo_ us3_, Nil))), k)
      with
      | Some u_ -> begin
          if Unify.unifiable (g_, us4_, (u_, id)) then
            Some (proofPlusExp (eclo_ us1_, eclo_ us2_, eclo_ us3_, eclo_ us4_))
          else None
        end
      | None -> None
      end

    let rec solveProveTimes (g_, s_, k) =
      let us1_ = fst (s_, id) in
      let us2_ = snd (s_, id) in
      let us3_ = trd (s_, id) in
      let us4_ = fth (s_, id) in
      begin match
        solveTimes
          (g_, App (eclo_ us1_, App (eclo_ us2_, App (eclo_ us3_, Nil))), k)
      with
      | Some u_ -> begin
          if Unify.unifiable (g_, us4_, (u_, id)) then
            Some
              (proofTimesExp (eclo_ us1_, eclo_ us2_, eclo_ us3_, eclo_ us4_))
          else None
        end
      | None -> None
      end

    let rec solveProveQuot (g_, s_, k) =
      let us1_ = fst (s_, id) in
      let us2_ = snd (s_, id) in
      let us3_ = trd (s_, id) in
      let us4_ = fth (s_, id) in
      begin match
        solveQuot
          (g_, App (eclo_ us1_, App (eclo_ us2_, App (eclo_ us3_, Nil))), k)
      with
      | Some u_ -> begin
          if Unify.unifiable (g_, us4_, (u_, id)) then
            Some (proofQuotExp (eclo_ us1_, eclo_ us2_, eclo_ us3_, eclo_ us4_))
          else None
        end
      | None -> None
      end

    let rec arrow (u_, v_) = Pi ((Dec (None, u_), No), v_)
    let rec pi (name, u_, v_) = Pi ((Dec (Some name, u_), Maybe), v_)
    let rec bvar n = Root (BVar n, Nil)

    let rec installFgnCnstrOps () =
      let csid = !myID in
      let _ =
        FgnCnstrStd.ToInternal.install
          ( csid,
            function
            | MyFgnCnstrRepPlus (g_, _, u1_, u2_, u3_) ->
                toInternalPlus (g_, u1_, u2_, u3_)
            | MyFgnCnstrRepTimes (g_, _, u1_, u2_, u3_) ->
                toInternalTimes (g_, u1_, u2_, u3_)
            | MyFgnCnstrRepQuot (g_, _, u1_, u2_, u3_) ->
                toInternalQuot (g_, u1_, u2_, u3_)
            | fc -> raise (UnexpectedFgnCnstr fc) )
      in
      let _ =
        FgnCnstrStd.Awake.install
          ( csid,
            function
            | MyFgnCnstrRepPlus (g_, proof, u1_, u2_, u3_) ->
                awakePlus (g_, proof, u1_, u2_, u3_)
            | MyFgnCnstrRepTimes (g_, proof, u1_, u2_, u3_) ->
                awakeTimes (g_, proof, u1_, u2_, u3_)
            | MyFgnCnstrRepQuot (g_, proof, u1_, u2_, u3_) ->
                awakeQuot (g_, proof, u1_, u2_, u3_)
            | fc -> raise (UnexpectedFgnCnstr fc) )
      in
      let _ =
        FgnCnstrStd.Simplify.install
          ( csid,
            function
            | MyFgnCnstrRepPlus _ -> fun () -> false
            | MyFgnCnstrRepTimes _ -> fun () -> false
            | MyFgnCnstrRepQuot _ -> fun () -> false
            | fc -> raise (UnexpectedFgnCnstr fc) )
      in
      ()

    let rec init (cs, installF) =
      begin
        myID := cs;
        begin
          wordID :=
            installF
              ( ConDec
                  ( "word" ^ Int.toString wordSize',
                    None,
                    0,
                    Constraint (!myID, solveNumber),
                    Uni Type,
                    Kind ),
                (None : FX.fixity option),
                [ MS.Mnil ] );
          begin
            plusID :=
              installF
                ( ConDec
                    ( "+",
                      None,
                      0,
                      Constraint (!myID, solvePlus),
                      arrow_
                        (word (), arrow_ (word (), arrow_ (word (), Uni Type))),
                      Kind ),
                  None,
                  [
                    MS.Mapp
                      ( MS.Marg (MS.Plus, Some "X"),
                        MS.Mapp
                          ( MS.Marg (MS.Plus, Some "Y"),
                            MS.Mapp (MS.Marg (MS.Minus, Some "Z"), MS.Mnil) ) );
                    MS.Mapp
                      ( MS.Marg (MS.Plus, Some "X"),
                        MS.Mapp
                          ( MS.Marg (MS.Minus, Some "Y"),
                            MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil) ) );
                    MS.Mapp
                      ( MS.Marg (MS.Minus, Some "X"),
                        MS.Mapp
                          ( MS.Marg (MS.Plus, Some "Y"),
                            MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil) ) );
                  ] );
            begin
              timesID :=
                installF
                  ( ConDec
                      ( "*",
                        None,
                        0,
                        Constraint (!myID, solveTimes),
                        arrow_
                          (word (), arrow_ (word (), arrow_ (word (), Uni Type))),
                        Kind ),
                    None,
                    [
                      MS.Mapp
                        ( MS.Marg (MS.Plus, Some "X"),
                          MS.Mapp
                            ( MS.Marg (MS.Plus, Some "Y"),
                              MS.Mapp (MS.Marg (MS.Minus, Some "Z"), MS.Mnil) )
                        );
                      MS.Mapp
                        ( MS.Marg (MS.Plus, Some "X"),
                          MS.Mapp
                            ( MS.Marg (MS.Minus, Some "Y"),
                              MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil) )
                        );
                      MS.Mapp
                        ( MS.Marg (MS.Minus, Some "X"),
                          MS.Mapp
                            ( MS.Marg (MS.Plus, Some "Y"),
                              MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil) )
                        );
                    ] );
              begin
                quotID :=
                  installF
                    ( ConDec
                        ( "/",
                          None,
                          0,
                          Constraint (!myID, solveQuot),
                          arrow_
                            ( word (),
                              arrow_ (word (), arrow_ (word (), Uni Type)) ),
                          Kind ),
                      None,
                      [
                        MS.Mapp
                          ( MS.Marg (MS.Plus, Some "X"),
                            MS.Mapp
                              ( MS.Marg (MS.Plus, Some "Y"),
                                MS.Mapp (MS.Marg (MS.Minus, Some "Z"), MS.Mnil)
                              ) );
                        MS.Mapp
                          ( MS.Marg (MS.Plus, Some "X"),
                            MS.Mapp
                              ( MS.Marg (MS.Minus, Some "Y"),
                                MS.Mapp (MS.Marg (MS.Plus, Some "Z"), MS.Mnil)
                              ) );
                      ] );
                begin
                  provePlusID :=
                    installF
                      ( ConDec
                          ( "prove+",
                            None,
                            0,
                            Constraint (!myID, solveProvePlus),
                            pi_
                              ( "X",
                                word (),
                                pi_
                                  ( "Y",
                                    word (),
                                    pi_
                                      ( "Z",
                                        word (),
                                        pi_
                                          ( "P",
                                            plusExp (bvar 3, bvar 2, bvar 1),
                                            Uni Type ) ) ) ),
                            Kind ),
                        None,
                        [
                          MS.Mapp
                            ( MS.Marg (MS.Star, Some "X"),
                              MS.Mapp
                                ( MS.Marg (MS.Star, Some "Y"),
                                  MS.Mapp
                                    ( MS.Marg (MS.Star, Some "Z"),
                                      MS.Mapp
                                        (MS.Marg (MS.Star, Some "P"), MS.Mnil)
                                    ) ) );
                        ] );
                  begin
                    proofPlusID :=
                      installF
                        ( ConDec
                            ( "proof+",
                              None,
                              0,
                              Normal,
                              pi_
                                ( "X",
                                  word (),
                                  pi_
                                    ( "Y",
                                      word (),
                                      pi_
                                        ( "Z",
                                          word (),
                                          pi_
                                            ( "P",
                                              plusExp (bvar 3, bvar 2, bvar 1),
                                              provePlusExp
                                                (bvar 4, bvar 3, bvar 2, bvar 1)
                                            ) ) ) ),
                              Type ),
                          None,
                          [] );
                    begin
                      proveTimesID :=
                        installF
                          ( ConDec
                              ( "prove*",
                                None,
                                0,
                                Constraint (!myID, solveProveTimes),
                                pi_
                                  ( "X",
                                    word (),
                                    pi_
                                      ( "Y",
                                        word (),
                                        pi_
                                          ( "Z",
                                            word (),
                                            pi_
                                              ( "P",
                                                timesExp (bvar 3, bvar 2, bvar 1),
                                                Uni Type ) ) ) ),
                                Kind ),
                            None,
                            [
                              MS.Mapp
                                ( MS.Marg (MS.Star, Some "X"),
                                  MS.Mapp
                                    ( MS.Marg (MS.Star, Some "Y"),
                                      MS.Mapp
                                        ( MS.Marg (MS.Star, Some "Z"),
                                          MS.Mapp
                                            ( MS.Marg (MS.Star, Some "P"),
                                              MS.Mnil ) ) ) );
                            ] );
                      begin
                        proofTimesID :=
                          installF
                            ( ConDec
                                ( "proof*",
                                  None,
                                  0,
                                  Normal,
                                  pi_
                                    ( "X",
                                      word (),
                                      pi_
                                        ( "Y",
                                          word (),
                                          pi_
                                            ( "Z",
                                              word (),
                                              pi_
                                                ( "P",
                                                  timesExp
                                                    (bvar 3, bvar 2, bvar 1),
                                                  proveTimesExp
                                                    ( bvar 4,
                                                      bvar 3,
                                                      bvar 2,
                                                      bvar 1 ) ) ) ) ),
                                  Type ),
                              None,
                              [] );
                        begin
                          proveQuotID :=
                            installF
                              ( ConDec
                                  ( "prove/",
                                    None,
                                    0,
                                    Constraint (!myID, solveProveQuot),
                                    pi_
                                      ( "X",
                                        word (),
                                        pi_
                                          ( "Y",
                                            word (),
                                            pi_
                                              ( "Z",
                                                word (),
                                                pi_
                                                  ( "P",
                                                    quotExp
                                                      (bvar 3, bvar 2, bvar 1),
                                                    Uni Type ) ) ) ),
                                    Kind ),
                                None,
                                [
                                  MS.Mapp
                                    ( MS.Marg (MS.Star, Some "X"),
                                      MS.Mapp
                                        ( MS.Marg (MS.Star, Some "Y"),
                                          MS.Mapp
                                            ( MS.Marg (MS.Star, Some "Z"),
                                              MS.Mapp
                                                ( MS.Marg (MS.Star, Some "P"),
                                                  MS.Mnil ) ) ) );
                                ] );
                          begin
                            proofQuotID :=
                              installF
                                ( ConDec
                                    ( "proof/",
                                      None,
                                      0,
                                      Normal,
                                      pi_
                                        ( "X",
                                          word (),
                                          pi_
                                            ( "Y",
                                              word (),
                                              pi_
                                                ( "Z",
                                                  word (),
                                                  pi_
                                                    ( "P",
                                                      quotExp
                                                        (bvar 3, bvar 2, bvar 1),
                                                      proveQuotExp
                                                        ( bvar 4,
                                                          bvar 3,
                                                          bvar 2,
                                                          bvar 1 ) ) ) ) ),
                                      Type ),
                                  None,
                                  [] );
                            begin
                              installFgnCnstrOps ();
                              ()
                            end
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
  end

  (* Cs_manager.ModeSyn *)
  (* FgnCnstr Representation: (G, proof, U1, U2, U3) *)
  (* numCheck (d) = true iff d <= max *)
  (* plusCheck (d1, d2) = true iff d1 + d2 <= max *)
  (* timesCheck (d1, d2) = true iff d1 * d2 <= max *)
  (* quotCheck (d1, d2) = true iff  d2 != zero *)
  (* constraint solver ID of this module *)
  (* constant ID of the type family constant ""wordXX"" *)
  (* constant ID's of the operators defined by this module *)
  (* + : wordXX -> wordXX -> wordXX -> type *)
  (* * : wordXX -> wordXX -> wordXX -> type *)
  (* / : wordXX -> wordXX -> wordXX -> type *)
  (* constant ID's of the proof object generators and their proof objects *)
  (* (these are used as workaround for the lack of sigma types in Twelf)  *)
  (* prove+ : {U}{V}{W} + U V W -> type *)
  (* prove* : {U}{V}{W} * U V W -> type *)
  (* prove/ : {U}{V}{W} / U V W -> type *)
  (* proof* : {U}{V}{W}{P} prove+ U V W P *)
  (* proof* : {U}{V}{W}{P} prove* U V W P *)
  (* proof/ : {U}{V}{W}{P} prove/ U V W P *)
  (* scanNumber (str) = numOpt

       Invariant:
         numOpt = SOME(n) if str is the decimal representation of the number n
                = NONE otherwise
    *)
  (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
  (* parseBinopPf operator string = SOME(conDec) or NONE

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)
  (* Term                       *)
  (* Term ::= n                 *)
  (*        | n1+n2             *)
  (*        | n1*n2             *)
  (*        | n1/n2             *)
  (*        | <Expr>            *)
  (* fromExpW (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then t is the internal representation of U[s] as term
    *)
  (* fromExp (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V
       then t is the internal representation of U[s] as term
    *)
  (* toExp t = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of t
    *)
  (* fst (S, s) = U1, the first argument in S[s] *)
  (* snd (S, s) = U2, the second argument in S[s] *)
  (* trd (S, s) = U1, the third argument in S[s] *)
  (* fth (S, s) = U1, the fourth argument in S[s] *)
  (* constraint constructor *)
  (* solvePlus (G, S, n) tries to find the n-th solution to
          G |- '+' @ S : type
    *)
  (* solveTimes (G, S, n) tries to find the n-th solution to
         G |- '*' @ S : type
    *)
  (* constraint constructor *)
  (* solveQuot (G, S, n) tries to find the n-th solution to
         G |- '/' @ S : type
    *)
  (* solveProvePlus (G, S, n) tries to find the n-th solution to
         G |- prove+ @ S : type
    *)
  (* solveProveTimes (G, S, n) tries to find the n-th solution to
         G |- prove* @ S : type
    *)
  (* solveProveQuot (G, S, n) tries to find the n-th solution to
         G |- prove/ @ S : type
    *)
  (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
  let solver : Cs_manager.solver =
    {
      name = "word" ^ Int.toString wordSize';
      keywords = "numbers,equality";
      needs = [ "Unify" ];
      fgnConst = Some { parse = parseAll };
      init;
      reset = (fun () -> ());
      mark = (fun () -> ());
      unwind = (fun () -> ());
    }
end
(* functor Cs_int_word *)

(* # 1 "src/solvers/cs_integers_word.sml.ml" *)
