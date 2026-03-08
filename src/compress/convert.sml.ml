open! Basis

module Convert = struct
  open Syntax

  exception Convert of string
  exception NotFound of string

  let sigma : string list ref = ref []
  let sigmat : class_ list ref = ref []
  let sigmap : bool list ref = ref []

  let rec clear () =
    begin
      sigma := [];
      begin
        sigmat := [];
        sigmap := []
      end
    end

  let rec findn arg__0 arg__1 =
    begin match (arg__0, arg__1) with
    | [], (v : string) -> raise (NotFound v)
    | v :: tl, v' -> begin if v = v' then 0 else 1 + findn tl v' end
    end

  let rec findid ctx v =
    try var_ (findn ctx v) with NotFound _ -> const_ (findn !sigma v)

  let rec modeconvert = function
    | mMINUS -> minus_
    | mPLUS -> plus_
    | mOMIT -> omit_

  let rec modesofclass = function
    | Kclass_ type_ -> []
    | Kclass_ (KPi (m, _, k)) -> m :: modesofclass (kclass k)
    | Tclass_ (TRoot _) -> []
    | Tclass_ (TPi (m, _, a)) -> m :: modesofclass (tclass a)

  (* given a context and an external expression, returns the internal 'spine form' as a 4-tuple
   (h, mopt, p, s)
   where h is the head (Var n or Const n)
         mopt is a list of modes for the arguments (MINUS, PLUS, OMIT)
         p is true iff the head is a synthesizing constant or a variable
         s is the list of arugments
*)
  let rec spine_form = function
    | g_, Parse.Id s -> begin
        match findid g_ s with
        | Var n -> (var_ n, None, true, [])
        | Const n ->
            ( const_ n,
              Some (modesofclass (List.nth (!sigmat, n))),
              List.nth (!sigmap, n),
              [] )
      end
    | g_, Parse.App (t, u) ->
        let h, mopt, p, s = spine_form (g_, t) in
        (h, mopt, p, s @ [ u ])
    | g_, Parse.Lam _ -> raise (Convert "illegal redex")
    | g_, _ -> raise (Convert "level mismatch")

  (* similar to spine_form for a type family applied to a list of arguments *)
  let rec type_spine_form = function
    | g_, Parse.Id s ->
        let n = findn !sigma s in
        (n, modesofclass (List.nth (!sigmat, n)), [])
    | g_, Parse.App (t, u) ->
        let n, m, s = type_spine_form (g_, t) in
        (n, m, s @ [ u ])
    | g_, _ -> raise (Convert "level mismatch")

  let rec safezip (l1, l2) =
    begin if length l1 = length l2 then ListPair.zip (l1, l2)
    else raise (Convert "wrong spine length")
    end

  (* given a context and an external expression and a mode, return a spine element or raise an exception*)
  let rec eltconvert arg__2 arg__3 =
    begin match (arg__2, arg__3) with
    | g_, (t, minus_) -> elt_ (convert (g_, t))
    | g_, (Parse.Ascribe (t, a), plus_) ->
        ascribe_ (nconvert (g_, t), typeconvert (g_, a))
    | g_, (t, plus_) -> aElt_ (aconvert (g_, t))
    | g_, (omit_, omit_) -> omit_
    | g_, (_, omit_) -> raise (Convert "found term expected to be omitted")
    end

  and aconvert (g_, t) =
    begin match convert (g_, t) with
    | ATerm t' -> t'
    | NTerm _ -> raise (Convert "required atomic, found normal")
    end

  and nconvert (g_, t) =
    begin match convert (g_, t) with
    | NTerm t' -> t'
    | ATerm _ -> raise (Convert "required normal, found atomic")
    end

  and convert = function
    | g_, Parse.Lam ((v, _), t) -> nTerm_ (lam_ (convert (v :: g_, t)))
    | g_, t ->
        let h, mopt, p, s = spine_form (g_, t) in
        let s' =
          map (eltconvert g_)
            begin match mopt with
            | None -> map (function elt -> (elt, minus_)) s
            | Some m -> safezip (s, m)
            end
        in
        begin if p then aTerm_ (aRoot_ (h, s')) else nTerm_ (nRoot_ (h, s'))
        end

  and typeconvert = function
    | g_, Parse.Pi (m, (v, Some t), t') ->
        let ct = typeconvert (g_, t) in
        let ct' = typeconvert (v :: g_, t') in
        tPi_ (modeconvert m, ct, ct')
    | g_, Parse.Pi (m, (_, None), _) ->
        raise (Convert "can't handle implicit pi")
    | g_, Parse.Arrow (t, t') ->
        let ct = typeconvert (g_, t) in
        let ct' = typeconvert ("" :: g_, t') in
        tPi_ (minus_, ct, ct')
    | g_, Parse.PlusArrow (t, t') ->
        let ct = typeconvert (g_, t) in
        let ct' = typeconvert ("" :: g_, t') in
        tPi_ (plus_, ct, ct')
    | g_, a ->
        let n, m, s = type_spine_form (g_, a) in
        let s' = map (eltconvert g_) (safezip (s, m)) in
        tRoot_ (n, s')

  and kindconvert = function
    | g_, Parse.Pi (m, (v, Some t), t') ->
        let ct = typeconvert (g_, t) in
        let ct' = kindconvert (v :: g_, t') in
        kPi_ (modeconvert m, ct, ct')
    | g_, Parse.Arrow (t, t') ->
        let ct = typeconvert (g_, t) in
        let ct' = kindconvert ("" :: g_, t') in
        kPi_ (minus_, ct, ct')
    | g_, Parse.PlusArrow (t, t') ->
        let ct = typeconvert (g_, t) in
        let ct' = kindconvert ("" :: g_, t') in
        kPi_ (plus_, ct, ct')
    | g_, Parse.Pi (m, (_, None), _) ->
        raise (Convert "can't handle implicit pi")
    | g_, type_ -> type_
    | _ -> raise (Convert "level mismatch")
  (* given a context and an external expression, return an atomic term or raise an exception*)
  (* given a context and an external expression, return a normal term or raise an exception*)
  (* given a context and an external expression, return a term or raise an exception *)
  (* given a context and an external expression, return a type or raise an exception *)
  (* given a context and an external expression, return a kind or raise an exception *)
end
