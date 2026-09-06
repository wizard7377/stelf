open! Basis
open! Table
open! Table.Table_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_

(* # 1 "src/names/Names_.sig.ml" *)
open! Basis

(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)

(** Modified: Jeff Polakow *)
include NAMES
(** signature FIXITY *)

(* signature NAMES *)

(* # 1 "src/names/Names_.fun.ml" *)
open! Basis
(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
module MakeNames
    (Global : GLOBAL)
    (Constraints : CONSTRAINTS)
    (HashTable : TABLE with type key = string)
    (StringTree : TABLE with type key = string) : NAMES = struct
  (*
  (*! structure IntSyn' : INTSYN !*)
  (*! sharing Constraints.IntSyn = IntSyn' !*)
*)
  (*! structure IntSyn = IntSyn' !*)
  module Global = Global
  module Constraints = Constraints
  module HashTable = HashTable
  module StringTree = StringTree

  exception Error of string

  (*
     Unprintable is raised when trying to resolve the names
     of unnamed variables.  Usually, this signals an error
     in Stelf; the only exception is the use of anonymous
     bound variables [_] or {_} in the source.
  *)
  exception Unprintable

  (***********************)
  (* Operator Precedence *)
  (***********************)
  module Fixity : FIXITY = struct
    (* Associativity ascribed to infix operators
       assoc ::= left    e.g. `<-'
               | right   e.g. `->'
               | none    e.g. `==' from some object language
    *)
    type associativity = Left | Right | None [@@deriving eq, ord, show]

    (* Operator Precedence *)
    type precedence = Strength of int [@@deriving eq, ord, show]

    (* Maximal and minimal precedence which can be declared explicitly *)
    let maxPrecInt = 9999
    let maxPrec = Strength maxPrecInt
    let minPrecInt = 0
    let minPrec = Strength minPrecInt
    let less (Strength p) (Strength q) = p < q
    let leq (Strength p) (Strength q) = p <= q

    let compare (Strength p) (Strength q) =
      match Int.compare (p, q) with
      | Less -> Less
      | Equal -> Equal
      | Greater -> Greater

    let inc (Strength p) = Strength (p + 1)
    let dec (Strength p) = Strength (p - 1)

    (* Fixities ascribed to constants *)
    type fixity =
      | Nonfix
      | Infix of precedence * associativity
      | Prefix of precedence
      | Postfix of precedence
    [@@deriving eq, ord, show]

    (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
    let precToIntAsc = function
      | Infix (Strength n, _) -> maxPrecInt + 1 - n
      | Prefix (Strength n) -> maxPrecInt + 1 - n
      | Postfix (Strength n) -> maxPrecInt + 1 - n
      | Nonfix -> minPrecInt

    (* prec (fix) = precedence of fix *)
    let prec = function
      | Infix (p, _) -> p
      | Prefix p -> p
      | Postfix p -> p
      | Nonfix -> inc maxPrec

    (* toString (fix) = declaration corresponding to fix *)
    let toString = function
      | Infix (Strength p, Left) -> "%infix left " ^ Int.toString p
      | Infix (Strength p, Right) -> "%infix right " ^ Int.toString p
      | Infix (Strength p, None) -> "%infix none " ^ Int.toString p
      | Prefix (Strength p) -> "%prefix " ^ Int.toString p
      | Postfix (Strength p) -> "%postfix " ^ Int.toString p
      | Nonfix -> "%nonfix"
  end

  (* not legal input *)
  (* structure Fixity *)
  (* argNumber (fix) = minimum # of explicit arguments required *)
  (* for operator with fixity fix (0 if there are no requirements) *)
  let argNumber = function
    | Fixity.Nonfix -> 0
    | Fixity.Infix _ -> 2
    | Fixity.Prefix _ -> 1
    | Fixity.Postfix _ -> 1

  (* checkAtomic (name, V, n) = ()
     if V expects exactly n arguments,
     raises Error(msg) otherwise
  *)
  let rec checkAtomic = function
    | name, IntSyn.Pi (d_, v_), 0 -> true
    | name, IntSyn.Pi (d_, v_), n ->
        Debug.msg' ~level:Debug.Level.Debug
          (fun f (name, v_, n) ->
            Format.fprintf f "checkAtomic: %s %s %d" name v_ n)
          (name, IntSyn.show_exp v_, n);
        checkAtomic (name, v_, n - 1)
    | name, IntSyn.Uni _, 0 ->
        Debug.msg ~level:Debug.Level.Debug
          (Debug.Fmt.shown_exact
             (fun name -> "checkAtomic: " ^ name ^ " is a universe")
             name);
        true
    | name, IntSyn.Root _, 0 ->
        Debug.msg ~level:Debug.Level.Debug
          (Debug.Fmt.shown_exact
             (fun name -> "checkAtomic: " ^ name ^ " is a root")
             name);
        true
    | name, v, n ->
        Debug.msg ~level:Debug.Level.Debug
          (Debug.Fmt.shown_exact
             (fun name ->
               "checkAtomic: " ^ name ^ " is neither a universe nor a root")
             name);
        false

  (* raise Error (""Constant "" ^ name ^ "" takes too many explicit arguments for given fixity"") *)
  (* allow extraneous arguments, Sat Oct 23 14:18:27 1999 -fp *)

  (* checkArgNumber (c, n) = ()
     if constant c expects exactly n explicit arguments,
     raises Error (msg) otherwise
  *)
  let checkArgNumber = function
    | IntSyn.ConDec (name, _, i, _, v_, l_), n -> checkAtomic (name, v_, i + n)
    | IntSyn.SkoDec (name, _, i, v_, l_), n -> checkAtomic (name, v_, i + n)
    | IntSyn.ConDef (name, _, i, _, v_, l_, _), n ->
        checkAtomic (name, v_, i + n)
    | IntSyn.AbbrevDef (name, _, i, _, v_, l_), n ->
        checkAtomic (name, v_, i + n)

  (** checkFixity (name, cidOpt, n) = () if n = 0 (no requirement on arguments)
      or name is declared and has n exactly explicit arguments, raises Error
      (msg) otherwise *)
  let checkFixity = function
    | name, _, 0 -> ()
    | name, cid, n ->
        begin if checkArgNumber (IntSyn.sgnLookup cid, n) then ()
        else
          raise
            (Error
               (("Constant " ^ name)
              ^ " takes too few explicit arguments for given fixity"))
        end

  (****************************************)
  (* Constants Names and Name Preferences *)
  (****************************************)
  (*
     Names (strings) are associated with constants (cids) in two ways:
     (1) There is an array nameArray mapping constants to print names (string),
     (2) there is a hashtable sgnHashTable mapping identifiers (strings) to constants.

     The mapping from constants to their print names must be maintained
     separately from the global signature, since constants which have
     been shadowed must be marked as such when printing.  Otherwise,
     type checking can generate very strange error messages such as
     ""Constant clash: c <> c"".

     In the same table we also record the fixity property of constants,
     since it is more a syntactic then semantic property which would
     pollute the lambda-calculus core.

     The mapping from identifers (strings) to constants is used during
     Parsing.

     There are global invariants which state the mappings must be
     consistent with each other.
  *)
  type qid = Qid of string list * string [@@deriving eq, ord, show]

  let qidToString (Qid (ids, name)) =
    List.foldr (function id, s -> (id ^ ".") ^ s) name ids

  let validateQualName = function
    | [] -> None
    | id :: ids as l ->
        begin if List.exists (function s -> s = "") l then None
        else Some (Qid (rev ids, id))
        end

  let stringToQid name =
    let name = Stdlib.String.trim name in
    validateQualName (rev (String.fields (function c -> c = '.') name))

  let unqualified = function Qid ([], id) -> Some id | _ -> None

  type nonrec namespace =
    IntSyn.mid StringTree.table * IntSyn.cid StringTree.table

  let newNamespace () = ((StringTree.new_ 0, StringTree.new_ 0) : namespace)

  let insertConst (structTable, constTable) cid =
    let condec_ = IntSyn.sgnLookup cid in
    let id = IntSyn.conDecName condec_ in
    begin match StringTree.insertShadow constTable (id, cid) with
    | None -> ()
    | Some _ ->
        raise
          (Error
             (("Shadowing: A constant named " ^ id)
             ^ "\nhas already been declared in this signature"))
    end

  let insertConstShadow (structTable, constTable) cid =
    let condec_ = IntSyn.sgnLookup cid in
    let id = IntSyn.conDecName condec_ in
    ignore (StringTree.insertShadow constTable (id, cid))

  let insertStruct (structTable, constTable) mid =
    let strdec = IntSyn.sgnStructLookup mid in
    let id = IntSyn.strDecName strdec in
    begin match StringTree.insertShadow structTable (id, mid) with
    | None -> ()
    | Some _ ->
        raise
          (Error
             (("Shadowing: A structure named " ^ id)
             ^ "\nhas already been declared in this signature"))
    end

  let appConsts f (structTable, constTable) = StringTree.app f constTable
  let appStructs f (structTable, constTable) = StringTree.app f structTable

  open! struct
    let rec fromTo f (from, to_) =
      begin if from >= to_ then ()
      else begin
        f from;
        fromTo f (from + 1, to_)
      end
      end

    let maxCid = Global.maxCid

    let shadowArray : IntSyn.cid option Array.array =
      Array.array (maxCid + 1, None)

    let shadowClear () = Array.modify (function _ -> None) shadowArray

    let fixityArray : Fixity.fixity Array.array =
      Array.array (maxCid + 1, Fixity.Nonfix)

    let fixityClear () =
      Array.modify (function _ -> Fixity.Nonfix) fixityArray

    let namePrefArray : (string list * string list) option Array.array =
      Array.array (maxCid + 1, None)

    let namePrefClear () = Array.modify (function _ -> None) namePrefArray

    (* The structure a constant was first installed as a component of, if
       any.  [IntSyn.conDecParent] answers the same question from the
       declaration itself, but only the module system ever fills that field
       in: %scope records membership here, in the name tables, and leaves
       the conDec's parent [None].  So this is the only record that a
       %scope-declared constant belongs anywhere.  See [constPath]. *)
    let parentArray : IntSyn.mid option Array.array =
      Array.array (maxCid + 1, None)

    let parentClear () = Array.modify (function _ -> None) parentArray
    let topNamespace : IntSyn.cid HashTable.table = HashTable.new_ 4096
    let topInsert = HashTable.insertShadow topNamespace
    let topLookup = HashTable.lookup topNamespace
    let topDelete = HashTable.delete topNamespace
    let topClear () = HashTable.clear topNamespace
    let dummyNamespace = ((StringTree.new_ 0, StringTree.new_ 0) : namespace)
    let maxMid = Global.maxMid

    let structShadowArray : IntSyn.mid option Array.array =
      Array.array (maxMid + 1, None)

    let structShadowClear () =
      Array.modify (function _ -> None) structShadowArray

    let componentsArray : namespace Array.array =
      Array.array (maxMid + 1, dummyNamespace)

    let componentsClear () =
      Array.modify (function _ -> dummyNamespace) componentsArray

    let topStructNamespace : IntSyn.mid HashTable.table = HashTable.new_ 4096
    let topStructInsert = HashTable.insertShadow topStructNamespace
    let topStructLookup = HashTable.lookup topStructNamespace
    let topStructDelete = HashTable.delete topStructNamespace
    let topStructClear () = HashTable.clear topStructNamespace
  end

  (* installName (name, cid) = ()
       Effect: update mapping from identifiers
               to constants, taking into account shadowing
    *)
  let installConstName cid =
    let condec_ = IntSyn.sgnLookup cid in
    let id = IntSyn.conDecName condec_ in
    begin match topInsert (id, cid) with
    | None -> ()
    | Some (_, cid') -> Array.update (shadowArray, cid, Some cid')
    end

  let installAlias name cid = ignore (topInsert (name, cid))

  let insertConstAlias (structTable, constTable) name cid =
    ignore (StringTree.insertShadow constTable (name, cid))

  let uninstallConst cid =
    let condec_ = IntSyn.sgnLookup cid in
    let id = IntSyn.conDecName condec_ in
    begin
      begin match Array.sub (shadowArray, cid) with
      | None ->
          begin if topLookup id = Some cid then topDelete id else ()
          end
      | Some cid' -> begin
          ignore (topInsert (id, cid'));
          Array.update (shadowArray, cid, None)
        end
      end;
      begin
        Array.update (fixityArray, cid, Fixity.Nonfix);
        Array.update (namePrefArray, cid, None)
      end
    end

  let installStructName mid =
    let strdec = IntSyn.sgnStructLookup mid in
    let id = IntSyn.strDecName strdec in
    begin match topStructInsert (id, mid) with
    | None -> ()
    | Some (_, mid') -> Array.update (structShadowArray, mid, Some mid')
    end

  let uninstallStruct mid =
    let strdec = IntSyn.sgnStructLookup mid in
    let id = IntSyn.strDecName strdec in
    begin
      begin match Array.sub (structShadowArray, mid) with
      | None ->
          begin if topStructLookup id = Some mid then topStructDelete id else ()
          end
      | Some mid' -> begin
          ignore (topStructInsert (id, mid'));
          Array.update (structShadowArray, mid, None)
        end
      end;
      Array.update (componentsArray, mid, dummyNamespace)
    end

  let resetFrom mark markStruct =
    let limit, limitStruct = IntSyn.sgnSize () in
    let rec ct f (i, j) =
      begin if j < i then ()
      else begin
        f j;
        ct f (i, j - 1)
      end
      end
    in
    begin
      ct uninstallConst (mark, limit - 1);
      ct uninstallStruct (markStruct, limitStruct - 1)
    end

  (* reset () = ()
       Effect: clear name tables related to constants
    *)
  let reset () =
    begin
      topClear ();
      begin
        topStructClear ();
        begin
          shadowClear ();
          begin
            structShadowClear ();
            begin
              fixityClear ();
              begin
                namePrefClear ();
                begin
                  componentsClear ();
                  parentClear ()
                end
              end
            end
          end
        end
      end
    end

  let structComps mid = (fun (r, _) -> r) (Array.sub (componentsArray, mid))
  let constComps mid = (fun (_, r) -> r) (Array.sub (componentsArray, mid))

  let rec findStruct = function
    | structTable, id :: [] -> StringTree.lookup structTable id
    | structTable, id :: ids ->
        begin match StringTree.lookup structTable id with
        | None -> None
        | Some mid -> findStruct (structComps mid, ids)
        end

  let findTopStruct = function
    | id :: [] -> HashTable.lookup topStructNamespace id
    | id :: ids ->
        begin match HashTable.lookup topStructNamespace id with
        | None -> None
        | Some mid -> findStruct (structComps mid, ids)
        end

  let rec findUndefStruct = function
    | structTable, id :: [], ids' ->
        begin match StringTree.lookup structTable id with
        | None -> Some (Qid (rev ids', id))
        | Some _ -> None
        end
    | structTable, id :: ids, ids' ->
        begin match StringTree.lookup structTable id with
        | None -> Some (Qid (rev ids', id))
        | Some mid -> findUndefStruct (structComps mid, ids, id :: ids')
        end

  let findTopUndefStruct = function
    | id :: [] ->
        begin match HashTable.lookup topStructNamespace id with
        | None -> Some (Qid ([], id))
        | Some _ -> None
        end
    | id :: ids ->
        begin match HashTable.lookup topStructNamespace id with
        | None -> Some (Qid ([], id))
        | Some mid -> findUndefStruct (structComps mid, ids, [ id ])
        end

  let constLookupIn a1 b1 = match a1, b1 with
    | (structTable, constTable), Qid ([], id) -> StringTree.lookup constTable id
    | (structTable, constTable), Qid (ids, id) ->
        begin match findStruct (structTable, ids) with
        | None -> None
        | Some mid -> StringTree.lookup (constComps mid) id
        end

  let structLookupIn a1 b1 = match a1, b1 with
    | (structTable, constTable), Qid ([], id) ->
        StringTree.lookup structTable id
    | (structTable, constTable), Qid (ids, id) ->
        begin match findStruct (structTable, ids) with
        | None -> None
        | Some mid -> StringTree.lookup (structComps mid) id
        end

  let constUndefIn a1 b1 = match a1, b1 with
    | (structTable, constTable), Qid ([], id) ->
        begin match StringTree.lookup constTable id with
        | None -> Some (Qid ([], id))
        | Some _ -> None
        end
    | (structTable, constTable), Qid (ids, id) ->
        begin match findUndefStruct (structTable, ids, []) with
        | Some _ as opt -> opt
        | None ->
            begin match
              StringTree.lookup
                (constComps (valOf (findStruct (structTable, ids))))
                id
            with
            | None -> Some (Qid (ids, id))
            | Some _ -> None
            end
        end

  let structUndefIn a1 b1 = match a1, b1 with
    | (structTable, constTable), Qid ([], id) ->
        begin match StringTree.lookup structTable id with
        | None -> Some (Qid ([], id))
        | Some _ -> None
        end
    | (structTable, constTable), Qid (ids, id) ->
        begin match findUndefStruct (structTable, ids, []) with
        | Some _ as opt -> opt
        | None ->
            begin match
              StringTree.lookup
                (structComps (valOf (findStruct (structTable, ids))))
                id
            with
            | None -> Some (Qid (ids, id))
            | Some _ -> None
            end
        end

  (* nameLookup (qid) = SOME(cid),  if qid refers to cid in the current context,
                        = NONE,       if there is no such constant
    *)
  let constLookup = function
    | Qid ([], id) -> HashTable.lookup topNamespace id
    | Qid (ids, id) ->
        begin match findTopStruct ids with
        | None -> None
        | Some mid -> StringTree.lookup (constComps mid) id
        end

  let structLookup = function
    | Qid ([], id) -> HashTable.lookup topStructNamespace id
    | Qid (ids, id) ->
        begin match findTopStruct ids with
        | None -> None
        | Some mid -> StringTree.lookup (structComps mid) id
        end

  (* The namespace of the %require group currently being loaded (or the
     top-level namespace if none). [Pal.Impl]'s [current_group_ns] is an
     alias for this ref: [ReconTerm]'s const-lookup chain only has access to
     [Names], never to [Impl]'s internals, so this needs to live here for
     [resolveQid] to see it. *)
  let currentGroupNamespace : namespace ref = ref (newNamespace ())

  (* [resolveQid ~shortest qid] is the shared entry point for %val/%abs name
     resolution.

     - [shortest:false] (%val, bare NAME, %( NAME )): identical to
       [constLookup qid] -- shadow-aware lookup via the global bare-name
       table, so an open [%scope]'s case-label binding wins over an
       outer/toplevel declaration of the same name ("longest match").

     - [shortest:true] on an unqualified qid ([Qid ([], name)]) (%abs NAME):
       prefer the binding of [name] within [!currentGroupNamespace]'s own
       table -- a genuine toplevel declaration of the currently-loading
       %require group, bypassing whatever %scope shadow is currently open in
       the global bare-name table -- falling back to the ordinary
       shadow-aware [constLookup qid] if no such toplevel binding exists.

     - [shortest:true] on a qualified qid ([Qid (ids, name)]) (%abs ( NAME
       S )): identical to [constLookup qid] -- ordinary qualified
       structure-member lookup is unaffected by shadowing either way. *)
  let resolveQid ~shortest qid =
    match (shortest, qid) with
    | true, Qid ([], _) ->
        begin match constLookupIn (!currentGroupNamespace) qid with
        | Some _ as found -> found
        | None -> constLookup qid
        end
    | _ -> constLookup qid

  let constUndef = function
    | Qid ([], id) ->
        begin match HashTable.lookup topNamespace id with
        | None -> Some (Qid ([], id))
        | Some _ -> None
        end
    | Qid (ids, id) ->
        begin match findTopUndefStruct ids with
        | Some _ as opt -> opt
        | None ->
            begin match
              StringTree.lookup (constComps (valOf (findTopStruct ids))) id
            with
            | None -> Some (Qid (ids, id))
            | Some _ -> None
            end
        end

  let structUndef = function
    | Qid ([], id) ->
        begin match HashTable.lookup topStructNamespace id with
        | None -> Some (Qid ([], id))
        | Some _ -> None
        end
    | Qid (ids, id) ->
        begin match findTopUndefStruct ids with
        | Some _ as opt -> opt
        | None ->
            begin match
              StringTree.lookup (structComps (valOf (findTopStruct ids))) id
            with
            | None -> Some (Qid (ids, id))
            | Some _ -> None
            end
        end

  let rec structPath (mid, ids) =
    let strdec = IntSyn.sgnStructLookup mid in
    let ids' = IntSyn.strDecName strdec :: ids in
    begin match IntSyn.strDecParent strdec with
    | None -> ids'
    | Some mid' -> structPath (mid', ids')
    end

  let maybeShadow = function
    | qid, false -> qid
    | Qid ([], id), true -> Qid ([], ("%" ^ id) ^ "%")
    | Qid (id :: ids, name), true -> Qid (("%" ^ id ^ "%") :: ids, name)

  let conDecQid condec_ =
    let id = IntSyn.conDecName condec_ in
    begin match IntSyn.conDecParent condec_ with
    | None -> Qid ([], id)
    | Some mid -> Qid (structPath (mid, []), id)
    end

  (* constQid (cid) = qid,
       where `qid' is the print name of cid
    *)
  let constQid cid =
    let condec_ = IntSyn.sgnLookup cid in
    let qid = conDecQid condec_ in
    maybeShadow (qid, constLookup qid <> Some cid)

  (* constPath (cid) = SOME qid, where qid names cid through the structure it
       was declared in and resolves back to it, or NONE if no such qid exists.

       This is the answer [constQid]'s "%c%" marker cannot give.  The marker
       says only that the bare name now means something else -- typically
       because a %scope closed and its components stopped being bare-visible
       -- while the constant itself is still perfectly reachable as
       [Qid ([scope], c)], since structure-member lookup does not consult the
       bare-name table at all.

       The result is verified rather than trusted: [parentArray] is not
       retracted by [uninstallConst] (bare-name retraction is not a change of
       membership) or by [resetFrom], so a stale entry is possible and must
       not turn into a name that resolves elsewhere.
    *)
  let constPath cid =
    begin match Array.sub (parentArray, cid) with
    | None -> None
    | Some mid ->
        let name = IntSyn.conDecName (IntSyn.sgnLookup cid) in
        let qid = Qid (structPath (mid, []), name) in
        begin if constLookup qid = Some cid then Some qid else None
        end
    end

  let structQid mid =
    let strdec = IntSyn.sgnStructLookup mid in
    let id = IntSyn.strDecName strdec in
    let qid =
      begin match IntSyn.strDecParent strdec with
      | None -> Qid ([], id)
      | Some mid -> Qid (structPath (mid, []), id)
      end
    in
    maybeShadow (qid, structLookup qid <> Some mid)

  (* installFixity (cid, fixity) = ()
       Effect: install fixity for constant cid,
               possibly print declaration depending on chatter level
    *)
  let installFixity cid fixity =
    let name = qidToString (constQid cid) in
    begin
      checkFixity (name, cid, argNumber fixity);
      Array.update (fixityArray, cid, fixity)
    end

  (* getFixity (cid) = fixity
       fixity defaults to Fixity.Nonfix, if nothing has been declared
    *)
  let getFixity cid = Array.sub (fixityArray, cid)

  (* fixityLookup qid = fixity
       where fixity is the fixity associated with constant named qid,
       defaults to Fixity.Nonfix if qid or fixity are undeclared
    *)
  let fixityLookup qid =
    begin match constLookup qid with
    | None -> Fixity.Nonfix
    | Some cid -> getFixity cid
    end

  (* Name Preferences *)
  (* ePref is the name preference for existential variables of given type *)
  (* uPref is the name preference for universal variables of given type *)
  (* installNamePref' (cid, (ePref, uPref)) see installNamePref *)
  let installNamePref' (cid, (ePref, uPref)) =
    let l_ = IntSyn.constUni cid in
    ignore begin match l_ with
      | Type ->
          raise
            (Error
               ((("Object constant " ^ qidToString (constQid cid))
                ^ " cannot be given name preference\n")
               ^ "Name preferences can only be established for type families"))
      | Kind -> ()
      end;
    Array.update (namePrefArray, cid, Some (ePref, uPref))

  (* installNamePref (cid, (ePref, uPrefOpt)) = ()
       Effect: install name preference for type family cid
       raise Error if cid does not refer to a type family
    *)
  let installNamePref a1 b1 = match a1, b1 with
    | cid, (ePref, []) ->
        installNamePref' (cid, (ePref, [ String.map Char.toLower (hd ePref) ]))
    | cid, (ePref, uPref) -> installNamePref' (cid, (ePref, uPref))

  let getNamePref cid = Array.sub (namePrefArray, cid)

  let installComponents mid namespace =
    begin
      (* First writer wins: a %scope reopening installs the same components
         again, and %open copies a constant into an enclosing namespace that
         may itself become a structure's.  The structure it was declared in
         is the one that keeps naming it. *)
      appConsts
        (fun (_, cid) ->
          begin match Array.sub (parentArray, cid) with
          | None -> Array.update (parentArray, cid, Some mid)
          | Some _ -> ()
          end)
        namespace;
      Array.update (componentsArray, mid, namespace)
    end

  let getComponents mid = Array.sub (componentsArray, mid)

  (* local names are more easily re-used: they don't increment the
       counter associated with a name
    *)
  type extent = Local | Global [@@deriving eq, ord, show]
  type role = Exist | Univ of extent [@@deriving eq, ord, show]

  let extent = function Exist -> Global | Univ ext -> ext

  let namePrefOf'' = function
    | Exist, None -> "_?"
    | Univ _, None -> "_"
    | Exist, Some (ePref, uPref) -> hd ePref
    | Univ _, Some (ePref, uPref) -> hd uPref

  let namePrefOf' = function
    | Exist, None -> "_?"
    | Univ _, None -> "_"
    | role, Some (IntSyn.Const cid) ->
        namePrefOf'' (role, Array.sub (namePrefArray, cid))
    | role, Some (IntSyn.Def cid) ->
        namePrefOf'' (role, Array.sub (namePrefArray, cid))
    | role, Some (IntSyn.FVar _) -> namePrefOf'' (role, None)
    | role, Some (IntSyn.NSDef cid) ->
        namePrefOf'' (role, Array.sub (namePrefArray, cid))
  (* the following only needed because reconstruction replaces
           undetermined types with FVars *)

  (* namePrefOf (role, V) = name
       where name is the preferred base name for a variable with type V

       V should be a type, but the code is robust, returning the default ""X"" or ""x""
    *)
  let namePrefOf (role, v_) = namePrefOf' (role, IntSyn.targetHeadOpt v_)

  (* local ... *)
  (******************)
  (* Variable Names *)
  (******************)
  (*
     Picking variable names is tricky, since we need to avoid capturing.
     This is entirely a matter of parsing and printing, since the
     internal representation relies on deBruijn indices and explicit
     substitutions.

     During parsing, a name is resolved as follows:
       lower case id => bound variable, constant, error
       upper case id => bound variable, constant, free variable
     where a free variable could become either an FVar
     (in constant declarations) or an EVar (in queries).

     Names are either given by the declaration or query itself, or
     assigned as late as possible.  For example, EVars which are never
     printed are never assigned a name.

     This may be a problem for contexts: if a name is not assigned when
     a declaration is entered into the context, terms in this context
     may not be printable.  Function decName below guarantees that new
     names are assigned to variables added to a context.
  *)
  (*
     There are three data structures:
     1. varTable mapping names (strings) to EVars and FVar types
          -- Actually, FVar types now handled entirely in recon-term.fun
          -- where there needs to be more info for approximate types.
          -- I don't see why EVar/BVar names should be generated apart from
          -- FVar names anyway, since the latter are printed with ""`"".
          -- -kw
     2. evarList mapping EVars to names (string)
     3. indexTable mapping base names B to integer suffixes to generate
        new names B1, B2, ...

     These are reset for each declaration or query, since
     EVars and FVars are local.
  *)
  open! struct
    type varEntry = Evar of IntSyn.exp

    let varTable : varEntry StringTree.table = StringTree.new_ 0
    let varInsert = StringTree.insert varTable
    let varLookup = StringTree.lookup varTable
    let varClear () = StringTree.clear varTable
    let varContext : IntSyn.dctx ref = ref IntSyn.Null
    let evarList : (IntSyn.exp * string) list ref = ref []
    let evarReset () = evarList := []

    let evarLookup x_ =
      let rec evlk = function
        | r, [] -> None
        | r, (IntSyn.EVar (r', _, _, _), name) :: l ->
            begin if r == r' then Some name else evlk (r, l)
            end
        | r, (IntSyn.AVar r', name) :: l ->
            begin if r == r' then Some name else evlk (r, l)
            end
      in
      begin match x_ with
      | IntSyn.EVar (r, _, _, _) -> evlk (r, !evarList)
      | IntSyn.AVar r -> evlk (r, !evarList)
      end

    let evarInsert entry = evarList := entry :: !evarList
    let namedEVars () = !evarList

    let rec evarCnstr' = function
      | [], acc -> acc
      | ( ((IntSyn.EVar ({ contents = None }, _, _, cnstrs), name) as xn_) :: l,
          acc ) ->
          begin match Constraints.simplify !cnstrs with
          | [] -> evarCnstr' (l, acc)
          | _ :: _ -> evarCnstr' (l, xn_ :: acc)
          end
      | _ :: l, acc -> evarCnstr' (l, acc)

    let evarCnstr () = evarCnstr' (!evarList, [])
    let indexTable : int StringTree.table = StringTree.new_ 0
    let indexInsert = StringTree.insert indexTable
    let indexLookup = StringTree.lookup indexTable
    let indexClear () = StringTree.clear indexTable

    let nextIndex' = function
      | name, None -> begin
          indexInsert (name, 1);
          1
        end
      | name, Some i -> begin
          indexInsert (name, i + 1);
          i + 1
        end

    let nextIndex name = nextIndex' (name, indexLookup name)
  end

  (* X *)
  (* remove this datatype? -kw *)
  (* varTable mapping identifiers (strings) to EVars and FVars *)
  (* A hashtable is too inefficient, since it is cleared too often; *)
  (* so we use a red/black trees instead *)
  (* initial size hint *)
  (* what is this for?  -kw *)
  (* evarList mapping EVars to names *)
  (* names are assigned only when EVars are parsed or printed *)
  (* the mapping must be implemented as an association list *)
  (* since EVars are identified by reference *)
  (* an alternative becomes possible if time stamps are introduced *)
  (* Since constraints are not printable at present, we only *)
  (* return a list of names of EVars that have constraints on them *)
  (* Note that EVars which don't have names, will not be considered! *)
  (* The indexTable maps a name to the last integer suffix used for it.
       The resulting identifer is not guaranteed to be new, and must be
       checked against the names of constants, FVars, EVars, and BVars.
    *)
  (* nextIndex (name) = i
       where i is the next available integer suffix for name,
       starting at 1.
       Effect: initialize or increment the indexTable entry for name
    *)
  (* varReset () = ()
       Effect: clear variable tables
       This must be called for each declaration or query
    *)
  let varReset g_ =
    begin
      varClear ();
      begin
        evarReset ();
        begin
          indexClear ();
          varContext := g_
        end
      end
    end

  (* addEVar (X, name) = ()
       effect: adds (X, name) to varTable and evarList
       assumes name not already used *)
  let addEVar x_ name =
    begin
      evarInsert (x_, name);
      varInsert (name, Evar x_)
    end

  let getEVarOpt name =
    begin match varLookup name with None -> None | Some (Evar x_) -> Some x_
    end

  (* varDefined (name) = true iff `name' refers to a free variable, *)
  (* which could be an EVar for constant declarations or FVar for queries *)
  let varDefined name =
    begin match varLookup name with None -> false | Some _ -> true
    end

  (* conDefined (name) = true iff `name' refers to a constant *)
  let conDefined name =
    begin match constLookup (Qid ([], name)) with
    | None -> false
    | Some _ -> true
    end

  (* ctxDefined (G, name) = true iff `name' is declared in context G *)
  let ctxDefined (g_, name) =
    let rec cdfd = function
      | IntSyn.Null -> false
      | IntSyn.Decl (g'_, IntSyn.Dec (Some name', _)) ->
          name = name' || cdfd g'_
      | IntSyn.Decl (g'_, IntSyn.BDec (Some name', _)) ->
          name = name' || cdfd g'_
      | IntSyn.Decl (g'_, IntSyn.NDec (Some name')) -> name = name' || cdfd g'_
      | IntSyn.Decl (g'_, _) -> cdfd g'_
    in
    cdfd g_

  (* tryNextName (G, base) = baseN
       where N is the next suffix such that baseN is unused in
       G, as a variable, or as a constant.
    *)
  let rec tryNextName (g_, base) =
    let name = base ^ Int.toString (nextIndex base) in
    begin if varDefined name || conDefined name || ctxDefined (g_, name) then
      tryNextName (g_, base)
    else name
    end

  let rec findNameLocal (g_, base, i) =
    let name = base ^ Int.toString i in
    begin if varDefined name || conDefined name || ctxDefined (g_, name) then
      findNameLocal (g_, base, i + 1)
    else name
    end

  let findName = function
    | g_, base, Local -> findNameLocal (g_, base, 0)
    | g_, base, Global -> tryNextName (g_, base)

  let takeNonDigits = Substring.takel (fun x -> not (Char.isDigit x))

  (* baseOf (name) = name',
       where name' is the prefix of name not containing a digit
    *)
  let baseOf name = Substring.string (takeNonDigits (Substring.full name))

  (* newEvarName (G, X) = name
       where name is the next unused name appropriate for X,
       based on the name preference declaration for A if X:A
    *)
  let newEVarName = function
    | g_, (IntSyn.EVar (r, _, v_, cnstr_) as x_) ->
        let name = tryNextName (g_, namePrefOf (Exist, v_)) in
        begin
          evarInsert (x_, name);
          name
        end
        (* use name preferences below *)
    | g_, (IntSyn.AVar r as x_) ->
        let name = tryNextName (g_, namePrefOf' (Exist, None)) in
        begin
          evarInsert (x_, name);
          name
        end
  (* use name preferences below *)

  (* evarName (G, X) = name
       where `name' is the print name X.
       If no name has been assigned yet, assign a new one.
       Effect: if a name is assigned, update varTable
    *)
  let evarName g_ x_ =
    begin match evarLookup x_ with
    | None ->
        let name = newEVarName (g_, x_) in
        begin
          varInsert (name, Evar x_);
          name
        end
    | Some name -> name
    end

  (* bvarName (G, k) = name
       where `name' is the print name for variable with deBruijn index k.
       Invariant: 1 <= k <= |G|
                  G_k must assign a name
       If no name has been assigned, the context might be built the wrong
       way---check decName below instread of IntSyn.Dec
    *)
  let bvarName g_ k =
    begin match IntSyn.ctxLookup g_ k with
    | IntSyn.Dec (Some name, _) -> name
    | IntSyn.ADec (Some name, _) -> name
    | IntSyn.NDec (Some name) -> name
    | IntSyn.ADec (None, _) -> "ADec_"
    | IntSyn.Dec (None, _) -> "Dec_"
    | _ -> raise Unprintable
    end
  (* Evars can depend on NDec :-( *)

  (* decName' role (G, D) = G,D'
       where D' is a possible renaming of the declaration D
       in order to avoid shadowing other variables or constants
       If D does not assign a name, this picks, based on the name
       preference declaration.
    *)
  let decName' arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | role, (g_, IntSyn.Dec (None, v_)) ->
        let name = findName (g_, namePrefOf (role, v_), extent role) in
        IntSyn.Dec (Some name, v_)
    | role, (g_, (IntSyn.Dec (Some name, v_) as d_)) ->
        begin if varDefined name || conDefined name || ctxDefined (g_, name)
        then IntSyn.Dec (Some (tryNextName (g_, baseOf name)), v_)
        else d_
        end
    | role, (g_, (IntSyn.BDec (None, ((cid, t) as b)) as d_)) ->
        let name =
          findName (g_, "#" ^ IntSyn.conDecName (IntSyn.sgnLookup cid), Local)
        in
        IntSyn.BDec (Some name, b)
    | role, (g_, (IntSyn.BDec (Some name, ((cid, t) as b)) as d_)) ->
        begin if varDefined name || conDefined name || ctxDefined (g_, name)
        then IntSyn.BDec (Some (tryNextName (g_, baseOf name)), b)
        else d_
        end
    | role, (g_, IntSyn.ADec (None, d)) ->
        let name = findName (g_, namePrefOf' (role, None), extent role) in
        IntSyn.ADec (Some name, d)
    | role, (g_, (IntSyn.ADec (Some name, d) as d_)) ->
        begin if varDefined name || conDefined name || ctxDefined (g_, name)
        then IntSyn.ADec (Some (tryNextName (g_, baseOf name)), d)
        else d_
        end
    | role, (g_, (IntSyn.NDec None as d_)) ->
        let name = findName (g_, "@x", Local) in
        ignore (print name);
        IntSyn.NDec (Some name)
    | role, (g_, (IntSyn.NDec (Some name) as d_)) ->
        begin if varDefined name || conDefined name || ctxDefined (g_, name)
        then IntSyn.NDec (Some (tryNextName (g_, baseOf name)))
        else d_
        end
    end
  (*      IntSyn.ADec(SOME(name), d) *)
  (* use #l as base name preference for label l *)

  let decName g_ d_ = decName' Exist (g_, d_)
  let decEName g_ d_ = decName' Exist (g_, d_)
  let decUName g_ d_ = decName' (Univ Global) (g_, d_)
  let decLUName g_ d_ = decName' (Univ Local) (g_, d_)

  (* ctxName G = G'

        Invariant:
        |- G == G' ctx
        where some Declaration in G' have been named/renamed
    *)
  let rec ctxName = function
    | IntSyn.Null -> IntSyn.Null
    | IntSyn.Decl (g_, d_) ->
        let g'_ = ctxName g_ in
        IntSyn.Decl (g'_, decName g'_ d_)

  (* ctxLUName G = G'
       like ctxName, but names assigned are local universal Names.
    *)
  let rec ctxLUName = function
    | IntSyn.Null -> IntSyn.Null
    | IntSyn.Decl (g_, d_) ->
        let g'_ = ctxLUName g_ in
        IntSyn.Decl (g'_, decLUName g'_ d_)

  (* pisEName' (G, i, V) = V'
       Assigns names to dependent Pi prefix of V with i implicit abstractions
       Used for implicit EVar in constant declarations after abstraction.
    *)
  let rec pisEName' = function
    | g_, i, IntSyn.Pi ((d_, IntSyn.Maybe), v_) when i > 0 ->
        let d'_ = decEName g_ d_ in
        IntSyn.Pi
          ((d'_, IntSyn.Maybe), pisEName' (IntSyn.Decl (g_, d'_), i - 1, v_))
    | g_, _, v_ -> v_

  (* | pisEName' (G, i, V) = V *)
  let pisEName (i, v_) = pisEName' (IntSyn.Null, i, v_)

  (* defEName' (G, i, (U,V)) = (U',V')
       Invariant: G |- U : V  and G |- U' : V' since U == U' and V == V'.
       Assigns name to dependent Pi prefix of V and corresponding lam prefix of U
       with i implicit abstractions
       Used for implicit EVar in constant definitions after abstraction.
    *)
  let rec defEName' = function
    | g_, 0, uv -> uv
    | g_, i, (IntSyn.Lam (d_, u_), IntSyn.Pi ((_, p_ (* = D *)), v_)) ->
        let d'_ = decEName g_ d_ in
        let u'_, v'_ = defEName' (IntSyn.Decl (g_, d'_), i - 1, (u_, v_)) in
        (IntSyn.Lam (d'_, u'_), IntSyn.Pi ((d'_, p_), v'_))
  (* i > 0 *)

  (* | defEName' (G, i, (U, V)) = (U, V) *)
  let defEName (imp, uv) = defEName' (IntSyn.Null, imp, uv)

  let nameConDec' = function
    | IntSyn.ConDec (name, parent, imp, status, v_, l_) ->
        IntSyn.ConDec (name, parent, imp, status, pisEName (imp, v_), l_)
    | IntSyn.ConDef (name, parent, imp, u_, v_, l_, anc) ->
        let u'_, v'_ = defEName (imp, (u_, v_)) in
        IntSyn.ConDef (name, parent, imp, u'_, v'_, l_, anc)
    | IntSyn.AbbrevDef (name, parent, imp, u_, v_, l_) ->
        let u'_, v'_ = defEName (imp, (u_, v_)) in
        IntSyn.AbbrevDef (name, parent, imp, u'_, v'_, l_)
    | skodec -> skodec

  (* fix ??? *)
  (* Assigns names to variables in a constant declaration *)
  (* The varReset (); is necessary so that explicitly named variables keep their name *)
  let nameConDec conDec =
    begin
      varReset IntSyn.Null;
      nameConDec' conDec
    end
  (* declaration is always closed *)

  let skonstName name = tryNextName (IntSyn.Null, name)
  let namedEVars = namedEVars
  let evarCnstr = evarCnstr
end

module Wrap (M : NAMES.FIXITY) : NAMES.WRAP = struct 
  module Fixity = M
  module type S = NAMES with module Fixity = M
  type t = (module S)

  let wrap (m : (module S)) : t = m
  let unwrap (t : t) : (module S) = t
end  
(* local varTable ... *)
(* functor Names *)

(* # 1 "src/names/Names_.sml.ml" *)
open! Basis

module Names =
  MakeNames (Global) (Constraints) (TableInstances.StringHashTable)
    (TableInstances.StringRedBlackTree)

include Names

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

let () =
  Printexc.register_printer (function
    | Unprintable -> Some "Unprintable"
    | _ -> None)
