open! Basis

module GrowArray : GROWARRAY = struct
  module A = Array

  type nonrec 'a growarray = (int * 'a option A.array) ref

  (* start with 16 cells, why not? *)
  let rec empty () = ref (0, A.array (16, None))
  let rec growarray n i = ref (n, A.array (n, Some i))

  let rec sub { contents = used, a } n =
    begin if n < used && n >= 0 then begin
      match A.sub (a, n) with None -> raise Subscript | Some z -> z
    end
    else raise Subscript
    end

  let rec length { contents = l, _ } = l

  (* grow to accomodate at least n elements *)
  let rec accomodate ({ contents = l, a } as r) n =
    begin if A.length a >= n + 1 then ()
    else
      let rec nextpower x =
        begin if x >= n + 1 then x else nextpower (x * 2)
        end
      in
      let ns = nextpower (A.length a) in
      let na =
        A.tabulate
          (ns, function i -> begin if i < l then A.sub (a, i) else None end)
      in
      r := (l, na)
    end

  let rec update r n x =
    begin if n < 0 then raise Subscript
    else
      let _ = accomodate r n in
      let l, a = !r in
      begin
        A.update (a, n, Some x);
        begin if n >= l then r := (n + 1, a) else ()
        end
      end (* also update 'used' *)
    end

  let rec append ({ contents = n, _ } as r) x =
    let _ = accomodate r (n + 1) in
    let _, a = !r in
    begin
      A.update (a, n, Some x);
      r := (n + 1, a)
    end

  let rec used arr n =
    try
      begin
        ignore (sub arr n);
        true
      end
    with Subscript -> false

  let rec finalize { contents = n, a } =
    A.tabulate
      ( n,
        function
        | x -> begin
            match A.sub (a, x) with None -> raise Subscript | Some z -> z
          end )
end
