include Misc_intf 

module Make_Misc
		(Common' : Common.COMMON)
		(Ast' : Ast_intf.AST with module Common = Common')
	: MISC with module Common = Common' and module Ast = Ast' =
struct
	module Common = Common'
	module Ast = Ast'

	let id : Ast.sub = Ast.Shift 0
	let shift : Ast.sub = Ast.Shift 1
	let invShift : Ast.sub = Ast.Dot (Ast.Undef, id)

	let rec bvarSub (n, s) =
		match n, s with
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
		| Ast.Bidx k -> (
			match bvarSub (k, s) with
			| Ast.Idx k' -> Ast.Bidx k'
			| Ast.Block b' -> b'
			| Ast.Exp _ | Ast.Axp _ | Ast.Undef -> b)
		| Ast.LVar (r, sk, (l, t)) ->
			begin
				match !r with
				| Some b' -> blockSub (b', comp (sk, s))
				| None -> Ast.LVar (r, comp (sk, s), (l, t))
			end
		| Ast.Inst us -> Ast.Inst (List.map (fun u -> Ast.EClo (u, s)) us)

	and comp (s1, s2) =
		match s1, s2 with
		| Ast.Shift 0, s | s, Ast.Shift 0 -> s
		| Ast.Shift n, Ast.Dot (_, s) -> comp (Ast.Shift (n - 1), s)
		| Ast.Shift n, Ast.Shift m -> Ast.Shift (n + m)
		| Ast.Dot (ft, s), s' -> Ast.Dot (frontSub (ft, s'), comp (s, s'))

	let dot1 s =
		match s with
		| Ast.Shift 0 -> s
		| _ -> Ast.Dot (Ast.Idx 1, comp (s, shift))

	let invDot1 s = comp (comp (shift, s), invShift)

	let newEVar (g, v) = Ast.EVar (ref None, g, v, ref [])
	let newAVar () = Ast.AVar (ref None)
	let newTypeVar g = newEVar (g, Ast.Uni Ast.Type)
	let newLVar (sk, (cid, t)) = Ast.LVar (ref None, sk, (cid, t))

	let rec headOpt = function
		| Ast.Tag (_, u) -> headOpt u
		| Ast.Root (h, _) -> Some h
		| Ast.Lam (_, u) -> headOpt u
		| _ -> None

	let ancestor u =
		let ancestor' = function
			| None -> Ast.Anc (None, 0, None)
			| Some (Ast.Const c) -> Ast.Anc (Some c, 1, Some c)
			| Some (Ast.Def d) -> Ast.Anc (Some d, 1, None)
			| Some _ -> Ast.Anc (None, 0, None)
		in
		ancestor' (headOpt u)

	let defAncestor d =
		Ast.Anc (Some d, 1, None)

	let rec targetHeadOpt = function
		| Ast.Tag (_, u) -> targetHeadOpt u
		| Ast.Root (h, _) -> Some h
		| Ast.Pi (_, v)
		| Ast.Redex (v, _)
		| Ast.Lam (_, v)
		| Ast.EClo (v, _) -> targetHeadOpt v
		| Ast.EVar (r, _, _, _) ->
			begin
				match !r with
				| Some v -> targetHeadOpt v
				| None -> None
			end
		| _ -> None

	let targetHead v =
		match targetHeadOpt v with
		| Some h -> h
		| None -> invalid_arg "targetHead"

	let rec targetFamOpt = function
		| Ast.Tag (_, u) -> targetFamOpt u
		| Ast.Root (Ast.Const cid, _) -> Some cid
		| Ast.Root (Ast.Def _, _) -> None
		| Ast.Pi (_, v)
		| Ast.Redex (v, _)
		| Ast.Lam (_, v)
		| Ast.EClo (v, _) -> targetFamOpt v
		| Ast.EVar (r, _, _, _) ->
			begin
				match !r with
				| Some v -> targetFamOpt v
				| None -> None
			end
		| _ -> None

	let targetFam v =
		match targetFamOpt v with
		| Some cid -> cid
		| None -> invalid_arg "targetFam"

	let rename (_cid, _new_name) = ()
end  
