open! Timers;;
open! Basis;;
module Translate : TRANSLATE =
  struct
    module L = Lib;;
    module I = IntSyn;;
    module S = Syntax;;
    module Sig = S.Signat;;
    module C = ClausePrint;;
    module D = Debug;;
    (* -------------------------------------------------------------------------- *);;
    (*  Exceptions                                                                *);;
    (* -------------------------------------------------------------------------- *);;
    exception Translate of string ;;
    exception Trans1 of S.const * I.conDec_ ;;
    exception Fail_exp of string * I.exp_ ;;
    (* -------------------------------------------------------------------------- *);;
    (*  Basic Translation                                                         *);;
    (* -------------------------------------------------------------------------- *);;
    let rec translate_uni = function 
                                     | kind_ -> S.Kind
                                     | type_ -> S.Type;;
    let rec translate_head =
      function 
               | I.BVar i -> (S.BVar i)
               | I.Const c -> (S.Const c)
               | I.Def c -> (S.Const c)
               | _ -> raise ((Translate "translate_head: bad case"));;
    let rec translate_depend =
      function 
               | no_ -> S.No
               | maybe_ -> S.Maybe
               | _ -> raise ((Fail "translate_depend: bad case"))
    and translate_exp =
      function 
               | I.Uni uni -> (S.Uni (translate_uni uni))
               | I.Pi ((I.Dec (name, u1_), depend), u2_)
                   -> (S.Pi
                       {
                       var = name;
                       arg = translate_exp u1_;
                       depend = translate_depend depend;
                       body = translate_exp u2_}
                       )
               | I.Root (h_, s_)
                   -> (S.Root (translate_head h_, translate_spine s_))
               | I.Lam (I.Dec (name, _), u_)
                   -> (S.Lam { var = name; body = translate_exp u_} )
               | e_ -> raise ((Fail_exp ("translate_exp: bad case", e_)))
    and translate_spine =
      function 
               | nil_ -> S.Nil
               | I.App (u_, s_)
                   -> (S.App (translate_exp u_, translate_spine s_))
               | _ -> raise ((Translate "translate_spine: bad case"));;
    let rec translate_condec =
      function 
               | (cid, I.ConDec (name, _, _, _, e_, u_))
                   -> (S.Decl
                       {
                       id = cid;
                       name;
                       exp = translate_exp e_;
                       uni = translate_uni u_}
                       )
               | (cid, I.ConDef
                  (name, _, _, u_, v_, type_, I.Anc (ex1, h, exa)))
                   -> (S.Def
                       {
                       id = cid;
                       name;
                       exp = translate_exp v_;
                       def = translate_exp u_;
                       height = h;
                       root = L.the exa;
                       uni = S.Type}
                       )
               | (cid, I.AbbrevDef (name, mid, n, u_, v_, lev))
                   -> (S.Abbrev
                       {
                       id = cid;
                       name;
                       exp = translate_exp v_;
                       def = translate_exp u_;
                       uni = translate_uni lev}
                       )
               | cdec -> raise ((Trans1 cdec));;
    (*     | translate_condec _ = raise Translate ""translate_condec: bad case"" *);;
    let rec can_translate =
      function 
               | I.ConDec _ -> true
               | I.ConDef _ -> true
               | I.AbbrevDef _ -> true
               | _ -> false;;
    let rec translate_signat' () =
      let n = L.fst (IntSyn.sgnSize ())
        in let ns = L.upto (0, n - 1)
             in let cds = map IntSyn.sgnLookup ns
                  in let cds' =
                       L.filter
                       (function 
                                 | (id, Dec_) -> can_translate Dec_)
                       (L.zip ns cds)
                       in map
                          (function 
                                    | ((c, e) as dec)
                                        -> (c, translate_condec Dec_))
                          cds';;
    let rec translate_signat () =
      Timers.time Timers.translation translate_signat' ();;
    end;;