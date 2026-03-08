open! Basis

(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)
(* Reverse subordination order *)
module MakeSubordinate (Subordinate__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module MemoTable : TABLE with type key = int * int
  module IntSet : Intset.INTSET
end) : SUBORDINATE = struct
  (*! structure IntSyn = IntSyn' !*)
  module Global = Subordinate__0.Global
  module Whnf = Subordinate__0.Whnf
  module Names = Subordinate__0.Names
  module Table = Subordinate__0.Table
  module MemoTable = Subordinate__0.MemoTable
  module IntSet = Subordinate__0.IntSet

  exception Error of string

  open! struct
    module I = IntSyn

    let soGraph : IntSet.intset Table.table_ = Table.new_ 32
    let insert = Table.insert soGraph
    let rec adjNodes a = valOf (Table.lookup soGraph a)
    let rec insertNewFam a = Table.insert soGraph (a, IntSet.empty)
    let updateFam = Table.insert soGraph
    let memoTable : (bool * int) MemoTable.table_ = MemoTable.new_ 2048
    let memoInsert = MemoTable.insert memoTable
    let memoLookup = MemoTable.lookup memoTable
    let memoClear = function () -> MemoTable.clear memoTable
    let memoCounter = ref 0

    let rec appReachable f b =
      let rec rch (b, visited) =
        begin if IntSet.member (b, visited) then visited
        else begin
          ignore (f b);
          IntSet.foldl rch (IntSet.insert (b, visited)) (adjNodes b)
        end
        end
      in
      begin
        ignore (rch (b, IntSet.empty));
        ()
      end

    exception Reachable

    let rec reach (b, a, visited) =
      let rec rch (b, visited) =
        begin if IntSet.member (b, visited) then visited
        else
          let adj = adjNodes b in
          begin if IntSet.member (a, adj) then raise Reachable
          else IntSet.foldl rch (IntSet.insert (b, visited)) adj
          end
        end
      in
      rch (b, visited)

    let rec reachable (b, a) = reach (b, a, IntSet.empty)

    let rec addNewEdge (b, a) =
      begin
        memoCounter := !memoCounter + 1;
        begin
          memoInsert ((b, a), (true, !memoCounter));
          updateFam (b, IntSet.insert (a, adjNodes b))
        end
      end

    let fTable : bool Table.table_ = Table.new_ 32
    let fLookup = Table.lookup fTable
    let fInsert = Table.insert fTable

    let rec fGet a =
      begin match fLookup a with Some frozen -> frozen | None -> false
      end

    let rec fSet (a, frozen) =
      let _ =
        Global.chPrint 5 (function () ->
            (begin if frozen then "Freezing " else "Thawing "
             end
            ^ Names.qidToString (Names.constQid a))
            ^ "\n")
      in
      fInsert (a, frozen)

    let rec checkFreeze (c, a) =
      begin if fGet a then
        raise
          (Error
             ((("Freezing violation: constant "
               ^ Names.qidToString (Names.constQid c))
              ^ "\nextends type family ")
             ^ Names.qidToString (Names.constQid a)))
      else ()
      end

    let rec expandFamilyAbbrevs a =
      begin match I.constUni a with
      | type_ ->
          raise
            (Error
               (("Constant " ^ Names.qidToString (Names.constQid a))
               ^ " must be a type family to be frozen or thawed"))
      | kind_ -> begin
          match IntSyn.sgnLookup a with
          | IntSyn.ConDec _ -> a
          | IntSyn.ConDef _ -> IntSyn.targetFam (IntSyn.constDef a)
          | IntSyn.SkoDec _ -> a
          | IntSyn.AbbrevDef _ -> IntSyn.targetFam (IntSyn.constDef a)
        end
      end

    let freezeList : IntSet.intset ref = ref IntSet.empty

    let rec freeze l_ =
      let _ = freezeList := IntSet.empty in
      let l'_ = map expandFamilyAbbrevs l_ in
      let _ =
        List.app
          (function
            | a ->
                appReachable
                  (function
                    | b -> begin
                        fSet (b, true);
                        freezeList := IntSet.insert (b, !freezeList)
                      end)
                  a)
          l'_
      in
      let cids = IntSet.foldl (fun (x, acc) -> x :: acc) [] !freezeList in
      cids

    let rec frozen l_ =
      let l'_ = map expandFamilyAbbrevs l_ in
      List.exists (function a -> fGet a) l'_

    let rec computeBelow (a, b) =
      try
        begin
          ignore (reachable (b, a));
          begin
            memoInsert ((b, a), (false, !memoCounter));
            false
          end
        end
      with Reachable ->
        begin
          memoInsert ((b, a), (true, !memoCounter));
          true
        end

    let rec below (a, b) =
      begin match memoLookup (b, a) with
      | None -> computeBelow (a, b)
      | Some (true, c) -> true
      | Some (false, c) -> begin
          if c = !memoCounter then false else computeBelow (a, b)
        end
      end

    let rec belowEq (a, b) = a = b || below (a, b)
    let rec equiv (a, b) = belowEq (a, b) && belowEq (b, a)

    let rec addSubord (a, b) =
      begin if below (a, b) then ()
      else begin
        if fGet b then
          raise
            (Error
               ((("Freezing violation: " ^ Names.qidToString (Names.constQid b))
                ^ " would depend on ")
               ^ Names.qidToString (Names.constQid a)))
        else addNewEdge (b, a)
      end
      end

    let aboveList : IntSyn.cid list ref = ref []

    let rec addIfBelowEq a's = function
      | b -> begin
          if List.exists (function a -> belowEq (a, b)) a's then
            aboveList := b :: !aboveList
          else ()
        end

    let rec thaw a's =
      let a's' = map expandFamilyAbbrevs a's in
      let _ = aboveList := [] in
      let _ = Table.app (function b, _ -> addIfBelowEq a's' b) soGraph in
      let _ = List.app (function b -> fSet (b, false)) !aboveList in
      !aboveList

    let defGraph : IntSet.intset Table.table_ = Table.new_ 32

    let rec occursInDef a =
      begin match Table.lookup defGraph a with None -> false | Some _ -> true
      end

    let rec insertNewDef (b, a) =
      begin match Table.lookup defGraph a with
      | None -> Table.insert defGraph (a, IntSet.insert (b, IntSet.empty))
      | Some bs -> Table.insert defGraph (a, IntSet.insert (b, bs))
      end

    let rec installConDec = function
      | b, I.ConDef (_, _, _, a_, k_, kind_, _) ->
          insertNewDef (b, I.targetFam a_)
      | _ -> ()

    let rec installDef c = installConDec (c, I.sgnLookup c)

    let rec checkNoDef a =
      begin if occursInDef a then
        raise
          (Error
             (("Definition violation: family "
              ^ Names.qidToString (Names.constQid a))
             ^ "\noccurs as right-hand side of type-level definition"))
      else
        appReachable
          (function
            | a' -> begin
                if occursInDef a' then
                  raise
                    (Error
                       (((("Definition violation: family "
                          ^ Names.qidToString (Names.constQid a))
                         ^ " |> ")
                        ^ Names.qidToString (Names.constQid a'))
                       ^ ",\n\
                          which occurs as right-hand side of a type-level \
                          definition"))
                else ()
              end)
          a
      end

    let rec reset () =
      begin
        Table.clear soGraph;
        begin
          Table.clear fTable;
          begin
            MemoTable.clear memoTable;
            Table.clear defGraph
          end
        end
      end

    and installTypeN' = function
      | I.Pi (((I.Dec (_, v1_) as d_), _), v2_), a -> begin
          addSubord (I.targetFam v1_, a);
          begin
            installTypeN v1_;
            installTypeN' (v2_, a)
          end
        end
      | (I.Root (I.Def _, _) as v_), a ->
          let v'_ = Whnf.normalize (Whnf.expandDef (v_, I.id)) in
          installTypeN' (v'_, a)
      | I.Root _, _ -> ()

    and installTypeN v_ = installTypeN' (v_, I.targetFam v_)

    let rec installKindN = function
      | I.Uni l_, a -> ()
      | I.Pi ((I.Dec (_, v1_), p_), v2_), a -> begin
          addSubord (I.targetFam v1_, a);
          begin
            installTypeN v1_;
            installKindN (v2_, a)
          end
        end

    let rec install c =
      let v_ = I.constType c in
      begin match I.targetFamOpt v_ with
      | None -> begin
          insertNewFam c;
          installKindN (v_, c)
        end
      | Some a -> begin
          begin match IntSyn.sgnLookup c with
          | IntSyn.ConDec _ -> checkFreeze (c, a)
          | IntSyn.SkoDec _ -> checkFreeze (c, a)
          | _ -> ()
          end;
          installTypeN' (v_, a)
        end
      end

    let rec installDec (I.Dec (_, v_)) = installTypeN v_

    let rec installSome = function
      | null_ -> ()
      | I.Decl (g_, d_) -> begin
          installSome g_;
          installDec d_
        end

    let rec installBlock b =
      let (I.BlockDec (_, _, g_, ds_)) = I.sgnLookup b in
      begin
        installSome g_;
        List.app (function d_ -> installDec d_) ds_
      end

    let rec checkBelow (a, b) =
      begin if not (below (a, b)) then
        raise
          (Error
             ((("Subordination violation: "
               ^ Names.qidToString (Names.constQid a))
              ^ " not <| ")
             ^ Names.qidToString (Names.constQid b)))
      else ()
      end

    let rec respectsTypeN' = function
      | I.Pi (((I.Dec (_, v1_) as d_), _), v2_), a -> begin
          checkBelow (I.targetFam v1_, a);
          begin
            respectsTypeN v1_;
            respectsTypeN' (v2_, a)
          end
        end
      | (I.Root (I.Def _, _) as v_), a ->
          let v'_ = Whnf.normalize (Whnf.expandDef (v_, I.id)) in
          respectsTypeN' (v'_, a)
      | I.Root _, _ -> ()

    and respectsTypeN v_ = respectsTypeN' (v_, I.targetFam v_)

    let rec respects (g_, (v_, s)) = respectsTypeN (Whnf.normalize (v_, s))
    let rec respectsN (g_, v_) = respectsTypeN v_

    let rec famsToString (bs, msg) =
      IntSet.foldl
        (function
          | a, msg -> (Names.qidToString (Names.constQid a) ^ " ") ^ msg)
        "\n" bs

    let rec showFam (a, bs) =
      print
        ((Names.qidToString (Names.constQid a)
         ^ begin if fGet a then " #> " else " |> "
         end)
        ^ famsToString (bs, "\n"))

    let rec show () = Table.app showFam soGraph

    let rec weaken = function
      | null_, a -> I.id
      | I.Decl (g'_, (I.Dec (name, v_) as d_)), a ->
          let w' = weaken (g'_, a) in
          begin if belowEq (I.targetFam v_, a) then I.dot1 w'
          else I.comp (w', I.shift)
          end

    open! struct
      let declared = ref 0
      let defined = ref 0
      let abbrev = ref 0
      let other = ref 0
      let heightArray = Array.array (32, 0)
      let maxHeight = ref 0
      let rec inc r = r := !r + 1

      let rec incArray h =
        Array.update (heightArray, h, Array.sub (heightArray, h) + 1)

      let rec max h = maxHeight := Int.max (h, !maxHeight)

      let rec reset () =
        begin
          declared := 0;
          begin
            defined := 0;
            begin
              abbrev := 0;
              begin
                other := 0;
                begin
                  Array.modify (function i -> 0) heightArray;
                  maxHeight := 0
                end
              end
            end
          end
        end
    end

    let rec analyzeAnc = function
      | I.Anc (None, _, _) -> incArray 0
      | I.Anc (_, h, _) -> begin
          incArray h;
          max h
        end

    let rec analyze = function
      | I.ConDec (_, _, _, _, _, l_) -> inc declared
      | I.ConDef (_, _, _, _, _, l_, ancestors) -> begin
          inc defined;
          analyzeAnc ancestors
        end
      | I.AbbrevDef (_, _, _, _, _, l_) -> inc abbrev
      | _ -> inc other

    let rec showDef () =
      let _ = reset () in
      let _ = I.sgnApp (function c -> analyze (I.sgnLookup c)) in
      let _ = print (("Declared: " ^ Int.toString !declared) ^ "\n") in
      let _ = print (("Defined : " ^ Int.toString !defined) ^ "\n") in
      let _ = print (("Abbrevs : " ^ Int.toString !abbrev) ^ "\n") in
      let _ = print (("Other   : " ^ Int.toString !other) ^ "\n") in
      let _ =
        print (("Max definition height: " ^ Int.toString !maxHeight) ^ "\n")
      in
      let _ =
        ArraySlice.appi
          (function
            | h, i ->
                print
                  ((((" Height " ^ Int.toString h) ^ ": ") ^ Int.toString i)
                  ^ " definitions\n"))
          (ArraySlice.slice (heightArray, 0, Some (!maxHeight + 1)))
      in
      ()
  end

  (* Subordination graph

       soGraph is valid
       iff for any type families a and b
       if b > a then there a path from b to a in the graph.

       Subordination is transitive, but not necessarily reflexive.
    *)
  (* must be defined! *)
  (* memotable to avoid repeated graph traversal *)
  (* think of hash-table model *)
  (* Apply f to every node reachable from b *)
  (* Includes the node itself (reflexive) *)
  (* b must be new *)
  (* this is sometimes violated below, is this a bug? *)
  (* Thu Mar 10 13:13:01 2005 -fp *)
  (*
       Freezing type families

       Frozen type families cannot be extended later with additional
       constructors.
     *)
  (* pre: a is not a type definition *)
  (* no longer needed since freeze is now transitive *)
  (* Sat Mar 12 21:40:15 2005 -fp *)
  (*
    fun frozenSubError (a, b) =
        raise Error (""Freezing violation: frozen type family ""
                     ^ Names.qidToString (Names.constQid b)
                     ^ ""\nwould depend on unfrozen type family ""
                     ^ Names.qidToString (Names.constQid a))
    *)
  (* no longer needed since freeze is now transitive *)
  (* Sat Mar 12 21:40:15 2005 -fp *)
  (* pre: a, b are not type definitions *)
  (*
    fun checkFrozenSub (a, b) =
        (case (fGet a, fGet b)
           of (false, true) => frozenSubError (a, b)
            | _ => ())
    *)
  (* pre: b is not a type definition *)
  (* no longer needed since freeze is transitive *)
  (* Sat Mar 12 21:38:58 2005 -fp *)
  (*
    fun checkMakeFrozen (b, otherFrozen) =
         Is this broken ??? 
         Mon Nov 11 16:54:29 2002 -fp 
         Example:
           a : type.
           b : type.
           %freeze a b.
           h : (a -> b) -> type.
           is OK, but as b |> a in its subordination
        
        let
          fun check a =
            if fGet a orelse List.exists (fn x => x = a) otherFrozen
              then ()
            else frozenSubError (a, b)
        in
          if fGet b then ()
          else appReachable check b
        end
    *)
  (* superseded by freeze *)
  (*
    fun installFrozen (L) =
        let
          val L = map expandFamilyAbbrevs L
           val _ = print (""L = "" ^ (foldl (fn (c,s) => Names.qidToString (Names.constQid c) ^ s) ""\n"" L)); 
        in
          List.app (fn a => checkMakeFrozen (a, L)) L;
          List.app (fn a => fSet (a, true)) L
        end
    *)
  (* freeze L = ()
       freezes all families in L, and all families transitively
       reachable from families in L

       Intended to be called from programs
    *)
  (* frozen L = true if one of the families in L is frozen *)
  (* a <| b = true iff a is (transitively) subordinate to b

       Invariant: a, b families
    *)
  (* true entries remain valid *)
  (* false entries are invalidated *)
  (* a <* b = true iff a is transitively and reflexively subordinate to b

       Invariant: a, b families
    *)
  (* a == b = true iff a and b subordinate each other

       Invariant: a, b families
    *)
  (* if b is frozen and not already b #> a *)
  (* subordination would change; signal error *)
  (* Thawing frozen families *)
  (* Returns list of families that were thawed *)
  (*
       Definition graph
       The definitions graph keeps track of chains of
       definitions for type families (not object-level definitions)

       We say b <# a if b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S

       The definition graph should be interpreted transitively.
       It can never be reflexive.

       The #> relation is stored in order to prevent totality
       checking on type families involved in definitions, because
       in the present implementation this would yield unsound
       results.

       NOTE: presently, the head ""a"" is always expanded until it is
       no longer a definition.  So if a #> b then a is always declared,
       never defined and b is always defined, never declared.

       Fri Dec 27 08:37:42 2002 -fp (just before 1.4 alpha)
    *)
  (* occursInDef a = true
       iff there is a b such that a #> b
    *)
  (* insertNewDef (b, a) = ()
       Effect: update definition graph.

       Call this upon seeing a type-level definition
           b = [x1:A1]...[xn:An] {y1:B1}...{y1:Bm} a @ S : K
       to record a #> b.
    *)
  (* installDef (c) = ()
       Effect: if c is a type-level definition,
               update definition graph.
    *)
  (* I.targetFam must be defined, but expands definitions! *)
  (* checkNoDef a = ()
       Effect: raises Error(msg) if there exists a b such that b <# a
               or b <# a' for some a' < a.
    *)
  (* reset () = ()

       Effect: Empties soGraph, fTable, defGraph
    *)
  (*
       Subordination checking no longer traverses spines,
       so approximate types are no longer necessary.
       This takes stronger advantage of the normal form invariant.
       Mon Nov 11 16:59:52 2002  -fp
    *)
  (* installTypeN' (V, a) = ()
       installTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: add subordination info from V into table
    *)
  (* this looks like blatant overkill ... *)
  (* Sun Nov 10 11:15:47 2002 -fp *)
  (* installKindN (V, a) = ()
       V nf, a : {x1:A1}...{xn:An} type, V = {xi:Ai}...{xn:An}type
       Effect: add subordination info from V into table
    *)
  (* there are no kind-level definitions *)
  (* install c = ()

       Effect: if c : V, add subordination from V into table
    *)
  (* FIX: skolem types should probably be created frozen -kw *)
  (* simplified  Tue Mar 27 20:58:31 2001 -fp *)
  (* installBlock b = ()
       Effect: if b : Block, add subordination from Block into table
    *)
  (* BDec, ADec, NDec are disallowed here *)
  (* b must be block *)
  (* Respecting subordination *)
  (* checkBelow (a, b) = () iff a <| b
       Effect: raise Error(msg) otherwise
    *)
  (* respectsTypeN' (V, a) = () iff V respects current subordination
       respectsTypeN (V) = ()
       V nf, V = {x1:A1}...{xn:An} a @ S

       Effect: raise Error (msg)
    *)
  (* this looks like blatant overkill ... *)
  (* Sun Nov 10 11:15:47 2002 -fp *)
  (* Printing *)
  (* Right now, AL is in always reverse order *)
  (* Reverse again --- do not sort *)
  (* Right now, Table.app will pick int order -- do not sort *)
  (*
    fun famsToString (nil, msg) = msg
      | famsToString (a::AL, msg) = famsToString (AL, Names.qidToString (Names.constQid a) ^ "" "" ^ msg)
    *)
  (* weaken (G, a) = (w') *)
  (* showDef () = ()
       Effect: print some statistics about constant definitions
    *)
  (* ignore blocks and skolem constants *)
  let reset = reset
  let install = install
  let installDef = installDef
  let installBlock = installBlock

  (* val installFrozen = installFrozen *)
  let freeze = freeze
  let frozen = frozen
  let thaw = thaw
  let addSubord = addSubord
  let below = below
  let belowEq = belowEq
  let equiv = equiv
  let checkNoDef = checkNoDef
  let respects = respects
  let respectsN = respectsN
  let weaken = weaken
  let show = show
  let showDef = showDef
end
(* local *)
(* functor Subordinate *)
