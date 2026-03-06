open! Basis;;
(* Modes: short and full mode declarations *);;
(* Author: Carsten Schuermann *);;
(* Modified: Frank Pfenning *);;
module ModeDec() : MODEDEC =
  struct
    (*! structure ModeSyn = ModeSyn' !*);;
    (*! structure Paths = Paths' !*);;
    exception Error of string ;;
    open!
      struct
        module M = ModeSyn;;
        module I = IntSyn;;
        module P = Paths;;
        type arg_ = | Implicit 
                    | Explicit 
                    | Local ;;
        let rec error (r, msg) = raise ((Error (P.wrap (r, msg))));;
        let rec checkName =
          function 
                   | mnil_ -> ()
                   | M.Mapp (M.Marg (_, Some name), mS)
                       -> let rec checkName' =
                            function 
                                     | mnil_ -> ()
                                     | M.Mapp (M.Marg (_, Some name'), mS)
                                         -> begin
                                         if name = name' then
                                         raise
                                         ((Error
                                           (("Variable name clash: " ^ name)
                                              ^ " is not unique")))
                                         else checkName' mS end
                            in checkName' mS;;
        let rec modeConsistent =
          function 
                   | (star_, plus_) -> false
                   | (star_, minus_) -> false
                   | (star_, minus1_) -> false
                   | (minus_, plus_) -> false
                   | (minus_, minus1_) -> false
                   | (minus1_, plus_) -> false
                   | _ -> true;;
        let rec empty =
          function 
                   | (0, ms, v_) -> (ms, v_)
                   | (k, ms, I.Pi (_, v_))
                       -> empty
                          (k - 1,
                           (I.Decl
                            (ms, ((M.Marg (M.star_, None)), Implicit))),
                           v_);;
        let rec inferVar =
          function 
                   | (I.Decl (ms, (M.Marg (star_, nameOpt), Implicit)), mode,
                      1)
                       -> (I.Decl (ms, ((M.Marg (mode, nameOpt)), Implicit)))
                   | (I.Decl (ms, (M.Marg (_, nameOpt), Implicit)), plus_, 1)
                       -> (I.Decl
                           (ms, ((M.Marg (M.plus_, nameOpt)), Implicit)))
                   | (I.Decl (ms, (M.Marg (minus_, nameOpt), Implicit)),
                      minus1_, 1)
                       -> (I.Decl
                           (ms, ((M.Marg (M.minus1_, nameOpt)), Implicit)))
                   | ((I.Decl (_, (_, Implicit)) as ms), _, 1) -> ms
                   | ((I.Decl (_, (_, Local)) as ms), _, 1) -> ms
                   | ((I.Decl (_, (M.Marg (mode', Some name), Explicit)) as
                        ms),
                      mode, 1) -> begin
                       if modeConsistent (mode', mode) then ms else
                       raise
                       ((Error
                         ((("Mode declaration for " ^ name) ^
                             " expected to be ")
                            ^ (M.modeToString mode))))
                       end
                   | (I.Decl (ms, md), mode, k)
                       -> (I.Decl (inferVar (ms, mode, k - 1), md));;
        let rec inferExp =
          function 
                   | (ms, mode, I.Root (I.BVar k, s_))
                       -> inferSpine (inferVar (ms, mode, k), mode, s_)
                   | (ms, mode, I.Root (I.Const cid, s_))
                       -> inferSpine (ms, mode, s_)
                   | (ms, mode, I.Root (I.Def cid, s_))
                       -> inferSpine (ms, mode, s_)
                   | (ms, mode, I.Root (I.FgnConst (cs, conDec), s_))
                       -> inferSpine (ms, mode, s_)
                   | (ms, mode, I.Lam ((I.Dec (nameOpt, _) as d_), u_))
                       -> I.ctxPop
                          (inferExp
                           ((I.Decl
                             (inferDec (ms, mode, d_),
                              ((M.Marg (mode, nameOpt)), Local))),
                            mode, u_))
                   | (ms, mode, I.Pi (((I.Dec (nameOpt, _) as d_), _), v_))
                       -> I.ctxPop
                          (inferExp
                           ((I.Decl
                             (inferDec (ms, mode, d_),
                              ((M.Marg (mode, nameOpt)), Local))),
                            mode, v_))
                   | (ms, mode, I.FgnExp _) -> ms
        and inferSpine =
          function 
                   | (ms, mode, nil_) -> ms
                   | (ms, mode, I.App (u_, s_))
                       -> inferSpine (inferExp (ms, mode, u_), mode, s_)
        and inferDec (ms, mode, I.Dec (_, v_)) = inferExp (ms, mode, v_);;
        let rec inferMode =
          function 
                   | ((ms, I.Uni type_), mnil_) -> ms
                   | ((_, I.Uni type_), _)
                       -> raise ((Error "Too many modes specified"))
                   | ((ms, I.Pi ((I.Dec (name, v1_), _), v2_)), M.Mapp
                      (M.Marg (mode, _), mS))
                       -> I.ctxPop
                          (inferMode
                           (((I.Decl
                              (inferExp (ms, mode, v1_),
                               ((M.Marg (mode, name)), Explicit))),
                             v2_),
                            mS))
                   | ((ms, I.Root _), _)
                       -> raise
                          ((Error
                            "Expected type family, found object constant"))
                   | _ -> raise ((Error "Not enough modes specified"));;
        let rec abstractMode (ms, mS) =
          let rec abstractMode' =
            function 
                     | (null_, mS, _) -> mS
                     | (I.Decl (ms, (marg, _)), mS, k)
                         -> abstractMode' (ms, (M.Mapp (marg, mS)), k + 1)
            in abstractMode' (ms, mS, 1);;
        let rec shortToFull (a, mS, r) =
          let rec calcImplicit' =
            function 
                     | I.ConDec (_, _, k, _, v_, _)
                         -> abstractMode
                            (inferMode (empty (k, I.null_, v_), mS), mS)
                     | I.ConDef (_, _, k, _, v_, _, _)
                         -> abstractMode
                            (inferMode (empty (k, I.null_, v_), mS), mS)
            in try begin
                     checkName mS;calcImplicit' (I.sgnLookup a)
                     end
               with 
                    | Error msg -> error (r, msg);;
        let rec checkFull (a, mS, r) =
          try begin
                checkName mS;
                begin
                match I.sgnLookup a
                with 
                     | I.ConDec (_, _, _, _, v_, _)
                         -> begin
                              inferMode ((I.null_, v_), mS);()
                              end
                     | I.ConDef (_, _, _, _, v_, _, _)
                         -> begin
                              inferMode ((I.null_, v_), mS);()
                              end
                end
                end
          with 
               | Error msg -> error (r, msg);;
        let rec checkPure =
          function 
                   | ((a, mnil_), r) -> ()
                   | ((a, M.Mapp (M.Marg (minus1_, _), mS)), r)
                       -> error
                          (r,
                           "Uniqueness modes (-1) not permitted in `%mode' declarations (use `%unique')")
                   | ((a, M.Mapp (_, mS)), r) -> checkPure ((a, mS), r);;
        end;;
    (* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       G corresponds to a context. We say M is a mode list for U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b X X -> b X Y -> type.

       Then

         %mode c +M -N.

       will infer X to be input and Y to be output

         %mode +{X:a} -{Y:a} +{M:b X Y} -{N:b X Y} (c M N).

       Generally, it is inconsistent
       for an unspecified ( * ) or output (-) argument to occur
       in the type of an input (+) argument
    *);;
    (* checkname mS = ()

       Invariant:
       mS modeSpine, all modes are named.
       If mS contains two entries with the same name
       then Error is raised
    *);;
    (* modeConsistent (m1, m2) = true
       iff it is consistent for a variable x with mode m1
           to occur as an index object in the type of a variable y:V(x) with mode m2

       m1\m2 + * - -1
        +    Y Y Y Y
        *    N y n n
        -    N y Y n
        -1   N Y Y Y

       The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
       The entry n specifies that the type
    *);;
    (* m1 should be M.Plus *);;
    (* m1 should be M.Minus *);;
    (* m1 should be M.Minus1 *);;
    (* m1 should be M.Plus *);;
    (* m1 should be M.Minus1 *);;
    (* m1 should be M.Plus *);;
    (* empty (k, ms, V) = (ms', V')

       Invariant:
       If    V = {A_1} .. {A_n} V1   in Sigma
       and   V has k implicit arguments
       then  ms' = ms, <( *, NONE), Implicit>  ... <( *, NONE), Implicit>   (k times)
       and   V' = V1
    *);;
    (* inferVar (ms, m, k) = ms'

       Invariant:
       If  ms is a mode list,
       and k is declared with mode mk in ms
       and m is the mode for a variable y in whose type k occurs
       then ms' is the same as ms replacing only mk by
       mk' = m o mk

        m o mk  + * - -1
        ----------------
        +       + + + +
        *       + * - -1
        -       + - - -1
        -1      + -1-1-1

        Effect: if the mode mk for k was explicitly declared and inconsistent
                with m o mk, an error is raised
    *);;
    (* inferExp (ms, m, U) = ms'

       Invariant:
       If  ms is a mode list for U,   (U in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in U,
         wrt. to m. (see inferVar)
    *);;
    (* cannot make any assumptions on what is inside a foreign object *);;
    (* inferSpine (ms, m, S) = ms'

       Invariant:
       If  ms is a mode list for S,   (S in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in S,
         wrt. to m. (see inferVar)
    *);;
    (* inferDec (ms, m, x:V) = ms'

       Invariant:
       If  ms is a mode list for V,   (V in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in V,
         wrt. to m.   (see inferVar)
    *);;
    (* inferMode ((ms, V), mS) = ms'

       Invariant:
       If  ms is a mode list for V,
       and mS is a mode spine,
       then ms' is the mode list for V which is consistent with V.
    *);;
    (* abstractMode (ms, mS) = mS'

       Invariant:
       If    V = {A1} .. {An} V1  is a type (with n implicit parameter)
       and   ms is a mode list for V,
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for the implicit parameters
    *);;
    (* shortToFull (cid, mS, r) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *);;
    (* ignore definition for defined type family since they are opaque *);;
    (* re-raise Error with location *);;
    (* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then
       exception Error is raised.
    *);;
    (* defined type families treated as separate types for
                 purposes of mode checking (as the operational
                 semantics doesn't expand type definitions) *);;
    (* re-raise error with location *);;
    (* checkPure (a, mS, r) = ()
       Effect: raises Error(msg) if the modes in mS mention (-1)
    *);;
    let shortToFull = shortToFull;;
    let checkFull = checkFull;;
    let checkPure = checkPure;;
    end;;
(*! structure ModeSyn' : MODESYN !*);;
(*! structure Paths' : PATHS !*);;
(* functor ModeDec *);;