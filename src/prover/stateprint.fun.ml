open! Basis

module StatePrint (StatePrint__0 : sig
  (* Meta Printer Version 1.3 *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Formatter' : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TomegaPrint : TOMEGAPRINT
end) : STATEPRINT = struct
  module Formatter = Formatter'

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module State = State'

  exception Error of string

  open! struct
    module I = IntSyn
    module T = Tomega
    module S = State'
    module N = Names
    module Fmt = Formatter

    let rec nameCtx psi_ = psi_
    let rec nameState s_ = s_

    let rec formatCtx = function
      | null_ -> []
      | I.Decl (null_, T.UDec d_) -> begin
          if !Global.chatter >= 4 then
            [ Fmt.HVbox [ Fmt.break_; Print.formatDec (I.null_, d_) ] ]
          else [ Print.formatDec (I.null_, d_) ]
        end
      | I.Decl (null_, T.PDec (Some s, f_, _)) -> begin
          if !Global.chatter >= 4 then
            [
              Fmt.HVbox
                [
                  Fmt.break_;
                  Fmt.String s;
                  Fmt.space_;
                  Fmt.String "::";
                  Fmt.space_;
                  TomegaPrint.formatFor (I.null_, f_);
                ];
            ]
          else
            [
              Fmt.String s;
              Fmt.space_;
              Fmt.String "::";
              Fmt.space_;
              TomegaPrint.formatFor (I.null_, f_);
            ]
        end
      | I.Decl (psi_, T.UDec d_) ->
          let g_ = T.coerceCtx psi_ in
          begin if !Global.chatter >= 4 then
            formatCtx psi_
            @ [ Fmt.String ","; Fmt.break_; Fmt.break_ ]
            @ [ Fmt.HVbox [ Fmt.break_; Print.formatDec (g_, d_) ] ]
          else
            formatCtx psi_
            @ [ Fmt.String ","; Fmt.break_ ]
            @ [ Fmt.break_; Print.formatDec (g_, d_) ]
          end
      | I.Decl (psi_, T.PDec (Some s, f_, _)) -> begin
          if !Global.chatter >= 4 then
            formatCtx psi_
            @ [ Fmt.String ","; Fmt.break_; Fmt.break_ ]
            @ [
                Fmt.HVbox
                  [
                    Fmt.break_;
                    Fmt.String s;
                    Fmt.space_;
                    Fmt.String "::";
                    Fmt.space_;
                    TomegaPrint.formatFor (psi_, f_);
                  ];
              ]
          else
            formatCtx psi_
            @ [ Fmt.String ","; Fmt.break_ ]
            @ [
                Fmt.break_;
                Fmt.String s;
                Fmt.space_;
                Fmt.String "::";
                Fmt.space_;
                TomegaPrint.formatFor (psi_, f_);
              ]
        end

    let rec formatState (S.State (w_, psi_, p_, f_, _)) =
      Fmt.Vbox0
        ( 0,
          1,
          [
            Fmt.String "------------------------";
            Fmt.break_;
            Fmt.String "------------------------";
            Fmt.break_;
            TomegaPrint.formatPrg (psi_, p_);
          ] )

    let rec stateToString s_ = Fmt.makestring_fmt (formatState s_)
  end

  (*
    fun nameCtx I.Null = I.Null
      | nameCtx (I.Decl (Psi, T.UDec D)) =
          I.Decl (nameCtx Psi,
                  T.UDec (Names.decName (T.coerceCtx Psi, D)))
      | nameCtx (I.Decl (Psi, T.PDec (_, F, TC))) =
          I.Decl (nameCtx Psi,
                  T.PDec (SOME ""s"", F, TC))    to be fixed! --cs 

*)
  (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
  (*
    fun formatOrder (G, S.Arg (Us, Vs)) =
          [Print.formatExp (G, I.EClo Us), Fmt.String "":"",
           Print.formatExp (G, I.EClo Vs)]
      | formatOrder (G, S.Lex Os) =
          [Fmt.String ""{"", Fmt.HVbox0 1 0 1 (formatOrders (G, Os)), Fmt.String ""}""]
      | formatOrder (G, S.Simul Os) =
          [Fmt.String ""["", Fmt.HVbox0 1 0 1 (formatOrders (G, Os)), Fmt.String ""]""]

    and formatOrders (G, nil) = nil
      | formatOrders (G, O :: nil) = formatOrder (G, O)
      | formatOrders (G, O :: Os) = formatOrder (G, O) @
          [Fmt.String "","", Fmt.Break]  @ formatOrders (G, Os)

     format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    
    fun formatTag (G, S.Parameter l) = [Fmt.String ""<p>""]
      | formatTag (G, S.Lemma (S.Splits k)) = [Fmt.String ""<i"",
                                                 Fmt.String (Int.toString k),
                                                 Fmt.String "">""]
      | formatTag (G, S.Lemma (S.RL)) = [Fmt.String ""<i >""]
      | formatTag (G, S.Lemma (S.RLdone)) = [Fmt.String ""<i*>""]
      | formatTag (G, S.Assumption k) = [Fmt.String ""<a"",
                                         Fmt.String (Int.toString k),
                                         Fmt.String "">""] 

*)
  (* formatCtx (Psi) = fmt'

       Invariant:
       If   |- Psi ctx       and Psi is already named
       then fmt' is a format describing the context Psi
    *)
  (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
  (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
  let nameState = nameState
  let formatState = formatState
  let stateToString = stateToString
end
(*! sharing TomegaPrint.IntSyn = IntSyn' !*)
(*! sharing TomegaPrint.Tomega = Tomega' !*)
(* local *)
(* functor MTPrint *)
