include SGN

module Make_Sgn
    (Common : Common.COMMON)
    (Ast : AST.AST with module Common = Common) :
  SGN.SGN with module Common = Common and module Ast = Ast = struct
  module CTable = Containers.Hashtbl.Make (struct
    type t = Ast.cid

    let equal a b = Common.Cid.equal a b
    let hash a = Hashtbl.hash a
  end)

  module MTable = Containers.Hashtbl.Make (struct
    type t = Ast.mid

    let equal a b = Common.Mid.equal a b
    let hash a = Hashtbl.hash a
  end)

  module Common = Common
  module Ast = Ast

  type cid = Ast.cid
  type mid = Ast.mid
  type conDec = Ast.conDec
  type strDec = Ast.strDec
  type dctx = Ast.dctx

  let table : conDec CTable.t = CTable.create (Common.Global.maxCid + 1)
  let structArray : strDec MTable.t = MTable.create (Common.Global.maxMid + 1)

  let rec bvarSub (n, s) =
    match (n, s) with
    | 1, Ast.Dot (ft, _) -> ft
    | n, Ast.Dot (_, s') -> bvarSub (n - 1, s')
    | n, Ast.Shift k -> Ast.Idx (n + k)

  and frontSub (ft, s) =
    match ft with
    | Ast.Idx n -> bvarSub (n, s)
    | Ast.Exp u -> Ast.Exp (Ast.EClo (u, s))
    | Ast.Axp u -> Ast.Axp (Ast.EClo (u, s))
    | Ast.Block b -> Ast.Block (blockSub (b, s))
    | Ast.Undef -> Ast.Undef

  and decSub (d, s) =
    match d with
    | Ast.Dec (x, v) -> Ast.Dec (x, Ast.EClo (v, s))
    | Ast.BDec (n, (l, t)) -> Ast.BDec (n, (l, comp (t, s)))
    | Ast.ADec (x, d) -> Ast.ADec (x, d)
    | Ast.NDec x -> Ast.NDec x

  and blockSub (b, s) =
    match b with
    | Ast.Bidx k ->
        begin match bvarSub (k, s) with
        | Ast.Idx k' -> Ast.Bidx k'
        | Ast.Block b' -> b'
        | Ast.Exp _ | Ast.Axp _ | Ast.Undef -> b
        end
    | Ast.LVar (r, sk, (l, t)) ->
        begin match !r with
        | Some b' -> blockSub (b', comp (sk, s))
        | None -> Ast.LVar (r, comp (sk, s), (l, t))
        end
    | Ast.Inst us -> Ast.Inst (List.map (fun u -> Ast.EClo (u, s)) us)

  and comp (s1, s2) =
    match (s1, s2) with
    | Ast.Shift 0, s | s, Ast.Shift 0 -> s
    | Ast.Shift n, Ast.Dot (_, s) -> comp (Ast.Shift (n - 1), s)
    | Ast.Shift n, Ast.Shift m -> Ast.Shift (n + m)
    | Ast.Dot (ft, s), s' -> Ast.Dot (frontSub (ft, s'), comp (s, s'))

  let reset () : unit =
    begin
      CTable.clear table;
      MTable.clear structArray;
      Common.Cid.reset ();
      Common.Mid.reset ()
    end

  let size () : int * int = (CTable.length table, MTable.length structArray)

  let add conDec : cid =
    let cid = Common.Cid.fresh () in
    CTable.replace table cid conDec;
    cid

  let lookup (cid : cid) : conDec = CTable.find table cid
  let app (f : cid -> unit) : unit = CTable.iter (fun cid _ -> f cid) table

  let structAdd (strDec : strDec) : mid =
    let mid = Common.Mid.fresh () in
    MTable.replace structArray mid strDec;
    mid

  let structLookup (mid : mid) : strDec = MTable.find structArray mid
  let constType c : Ast.exp = Ast.conDecType (lookup c)

  let constDef (c : Ast.cid) : Ast.exp =
    begin match lookup c with
    | Ast.ConDef (_, _, _, def, _, _, _) -> def
    | Ast.AbbrevDef (_, _, _, def, _, _) -> def
    | _ -> invalid_arg "constDef"
    end

  let constImp c : int = Ast.conDecImp (lookup c)
  let constStatus (c : Ast.cid) : Ast.status = Ast.conDecStatus (lookup c)
  let constUni (c : Ast.cid) : Ast.uni = Ast.conDecUni (lookup c)
  let constBlock (c : cid) : dctx * Ast.dec list = Ast.conDecBlock (lookup c)

  let rename (cid, new_name) =
    begin match lookup cid with
    | Ast.ConDec (_, parent, imp, status, exp, uni) ->
        CTable.replace table cid
          (Ast.ConDec (new_name, parent, imp, status, exp, uni))
    | Ast.ConDef (_, parent, imp, def, exp, uni, anc) ->
        CTable.replace table cid
          (Ast.ConDef (new_name, parent, imp, def, exp, uni, anc))
    | Ast.AbbrevDef (_, parent, imp, def, exp, uni) ->
        CTable.replace table cid
          (Ast.AbbrevDef (new_name, parent, imp, def, exp, uni))
    | Ast.BlockDec (_, parent, g, ds) ->
        CTable.replace table cid (Ast.BlockDec (new_name, parent, g, ds))
    | Ast.BlockDef (_, parent, cids) ->
        CTable.replace table cid (Ast.BlockDef (new_name, parent, cids))
    | Ast.SkoDec (_, parent, imp, exp, uni) ->
        CTable.replace table cid (Ast.SkoDec (new_name, parent, imp, exp, uni))
    end

  let ctxDec (g, k) =
    let rec ctxDec' (g', k') =
      match (g', k') with
      | Ast.Decl (_, Ast.Dec (x, v)), 1 -> Ast.Dec (x, Ast.EClo (v, Ast.Shift k))
      | Ast.Decl (_, Ast.BDec (n, (l, s))), 1 ->
          Ast.BDec (n, (l, comp (s, Ast.Shift k)))
      | Ast.Decl (_, d), 1 -> d
      | Ast.Decl (g'', _), k'' -> ctxDec' (g'', k'' - 1)
      | Ast.Null, _ -> invalid_arg "ctxDec"
    in
    ctxDec' (g, k)

  let blockDec (g, v, i) =
    match v with
    | Ast.Bidx k ->
        begin match ctxDec (g, k) with
        | Ast.BDec (_, (l, s)) ->
            let _, block_decls = Ast.conDecBlock (CTable.find table l) in
            let rec blockDec' (t, decls, n, j) =
              match (decls, n) with
              | d :: _, 1 -> decSub (d, t)
              | _ :: rest, n' ->
                  blockDec'
                    ( Ast.Dot (Ast.Exp (Ast.Root (Ast.Proj (v, j), Ast.Nil)), t),
                      rest,
                      n' - 1,
                      j + 1 )
              | [], _ -> invalid_arg "blockDec"
            in
            blockDec' (s, block_decls, i, 1)
        | _ -> invalid_arg "blockDec"
        end
    | _ -> invalid_arg "blockDec"
end
