open! Layout;;
open! Basis;;
(* -------------------------------------------------------------------------- *);;
(*  Printing                                                                  *);;
(* -------------------------------------------------------------------------- *);;
open!
  struct
    let rec ( $ ) x = Layout.str x;;
    let rec ( % ) x = Layout.mayAlign x;;
    let rec ( %% ) x = Layout.align x;;
    let rec ( & ) x = Layout.seq x;;
    let rec paren x =
      (fun (x__op, y__op) -> x__op & y__op)
      [(fun (x__op, y__op) -> x__op $ y__op) "("; x;
       (fun (x__op, y__op) -> x__op $ y__op) ")"];;
    let rec bracket x =
      (fun (x__op, y__op) -> x__op & y__op)
      [(fun (x__op, y__op) -> x__op $ y__op) "["; x;
       (fun (x__op, y__op) -> x__op $ y__op) "]"];;
    let rec squiggle x =
      (fun (x__op, y__op) -> x__op & y__op)
      [(fun (x__op, y__op) -> x__op $ y__op) "{"; x;
       (fun (x__op, y__op) -> x__op $ y__op) "}"];;
    let rec indent x = Layout.indent x;;
    let rec uni_to_layout =
      function 
               | Type -> (fun (x__op, y__op) -> x__op $ y__op) "type"
               | kind_ -> (fun (x__op, y__op) -> x__op $ y__op) "kind";;
    let rec const_to_string sgn c = name (Sig.lookup sgn c);;
    let rec spine_to_list =
      function 
               | nil_ -> []
               | App (e_, s_) -> (e_ :: spine_to_list s_);;
    let rec head_to_layout arg__0 arg__1 =
      begin
      match (arg__0, arg__1)
      with 
           | (sgn, Const c)
               -> (fun (x__op, y__op) -> x__op $ y__op)
                  (const_to_string sgn c)
           | (sgn, BVar n)
               -> (fun (x__op, y__op) -> x__op $ y__op) (Int.toString n)
      end;;
    let rec needs_parens_in_arg_pos =
      function 
               | Uni _ -> false
               | Root (_, nil_) -> false
               | _ -> true;;
    let rec needs_sparens_in_arg_pos =
      function 
               | nil_ -> false
               | App (e_, nil_) -> needs_parens_in_arg_pos e_
               | _ -> true;;
    let rec maybe_paren e_ l = begin
      if needs_parens_in_arg_pos e_ then paren l else l end;;
    let rec maybe_sparen s_ l = begin
      if needs_sparens_in_arg_pos s_ then paren l else l end;;
    let rec spine_to_layout sgn s_ =
      (fun (x__op, y__op) -> x__op %% y__op)
      (map (exp_to_layout sgn) (spine_to_list s_))
    and exp_to_layout arg__2 arg__3 =
      begin
      match (arg__2, arg__3)
      with 
           | (sgn, Uni lev) -> uni_to_layout lev
           | (sgn, Pi Pi_)
               -> (fun (x__op, y__op) -> x__op & y__op)
                  [(fun (x__op, y__op) -> x__op $ y__op) "PI ";
                   (fun (x__op, y__op) -> x__op %% y__op)
                   [(fun (x__op, y__op) -> x__op & y__op)
                    [maybe_paren
                     ((fun r -> r.arg) Pi_)
                     (exp_to_layout sgn ((fun r -> r.arg) Pi_));
                     (fun (x__op, y__op) -> x__op $ y__op) ". "];
                    exp_to_layout sgn ((fun r -> r.body) Pi_)]]
           | (sgn, Lam Lam_)
               -> (fun (x__op, y__op) -> x__op & y__op)
                  [(fun (x__op, y__op) -> x__op $ y__op) "LAM. ";
                   exp_to_layout sgn ((fun r -> r.body) Lam_)]
           | (sgn, Root (h_, nil_)) -> head_to_layout sgn h_
           | (sgn, Root (h_, s_))
               -> (fun (x__op, y__op) -> x__op & y__op)
                  [head_to_layout sgn h_;
                   (fun (x__op, y__op) -> x__op $ y__op) " ^ ";
                   maybe_sparen s_ (spine_to_layout sgn s_)]
      end;;
    type subelem = | SubShift of int 
                   | SubExp of exp ;;
    let rec sub_to_list =
      function 
               | (Shift n as sub) -> [(SubShift n)]
               | Dot (m_, sub) -> ((SubExp m_) :: sub_to_list sub)
               | Comp (s1, s2) -> (sub_to_list s1) @ (sub_to_list s2);;
    let rec sub_to_layout sgn sub =
      let sub' = sub_to_list sub
        in let rec mapfn =
             function 
                      | SubShift n
                          -> (fun (x__op, y__op) -> x__op $ y__op)
                             ("^" ^ (Int.toString n))
                      | SubExp exp -> exp_to_layout sgn exp
             in let sub'' = map mapfn sub' in Layout.list sub'';;
    end;;
let rec exp_to_string sgn exp = Layout.tostring (exp_to_layout sgn exp);;
let rec spine_to_string sgn sp = Layout.tostring (spine_to_layout sgn sp);;
let rec sub_to_string sgn sub = Layout.tostring (sub_to_layout sgn sub);;
let rec print_exp sgn exp = print (("\n" ^ (exp_to_string sgn exp)) ^ "\n");;
let rec print_spine sgn sp = print (("\n" ^ (spine_to_string sgn sp)) ^ "\n");;
let rec print_sub sgn sub = print (("\n" ^ (sub_to_string sgn sub)) ^ "\n");;