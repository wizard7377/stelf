open! Basis;;
(* structure GrowarrayTable : TABLE where type key = int = *);;
(* struct *);;
(*   structure L = Lib *);;
(*   structure A = GrowArray *);;
(*   type key = int  *);;
(*   type 'a table = 'a A.growarray *);;
(*   fun empty _ = A.empty() *);;
(*   fun size t = A.length t *);;
(*   fun insert t (n,v) = *);;
(*       if A.length t > n then raise Fail ""insert: signat contains key"" *);;
(*       else (A.update t n v;t) *);;
(*   fun lookup t n = A.sub t n *);;
(*   fun iter f : ('a -> unit) -> 'a table -> unit *);;
(*   val foldl : ('a * 'b -> 'b) -> 'b -> 'a table -> b *);;
(*   val foldr : ('a * 'b -> 'b) -> 'b -> 'a table -> b *);;
(* end *);;
module ArrayTable : TABLE =
  struct
    module L = Lib;;
    module A = Array;;
    type nonrec key = int;;
    type nonrec 'a __0 = { arr: 'a option array ; used: int ref };;
    type nonrec 'a table = 'a __0;;
    let rec table n = { arr = A.array (n, None); used = ref 0} ;;
    let rec clear { arr; used} =
      begin
        used := 0;A.modify (function 
                                     | _ -> None) arr
        end;;
    let rec insert (({ arr; used} as t)) (n, v) = begin
      if (n < 0) || (n > (A.length arr)) then raise Subscript else
      begin
      match A.sub (arr, n)
      with 
           | None
               -> begin
                    A.update (arr, n, (Some v));
                    begin
                      begin if n > (! used) then used := n else () end;t
                      end
                    
                    end
           | Some _ -> raise ((Fail "insert: key already present"))
      end end;;
    let rec lookup (({ arr} : 'a table)) n = begin
      if (n < 0) || (n > (A.length arr)) then raise Subscript else
      begin
      match A.sub (arr, n) with 
                                | None -> raise Subscript
                                | Some v -> v
      end end;;
    let rec size (({ arr} : 'a table)) = A.length arr;;
    exception Done ;;
    let rec app f { arr; used} =
      let used' = ! used
        in let rec f' (i, x) = begin
             if i >= used' then raise Done else
             begin match x with 
                                | Some n -> f n
                                | None -> () end
             end in try A.appi f' arr with 
                                           | Done -> ();;
    let rec appi f { arr; used} =
      let used' = ! used
        in let rec f' (i, x) = begin
             if i >= used' then raise Done else
             begin match x with 
                                | Some n -> f (i, n)
                                | None -> () end
             end in try A.appi f' arr with 
                                           | Done -> ();;
    end;;
module Table = ArrayTable;;