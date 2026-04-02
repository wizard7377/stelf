(* # 1 "src/meta/Funnames.sig.ml" *)
open! Basis
open Funsyn

(* Names of Constants and Variables *)
(* Author: Carsten Schuermann *)
include Funnames_intf
(* will mark if shadowed *)
(* signature NAMES *)

(* # 1 "src/meta/Funnames.fun.ml" *)
open! Global
open! Basis

(* Names of Constants and Variables *)
(* Author: Carsten Schuermann *)
module FunNames (FunNames__0 : sig
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module HashTable : TABLE with type key = string
end) : Funnames_intf.FUNNAMES = struct
  open FunNames__0

  (*! structure FunSyn = FunSyn' !*)
  exception Error of string

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
  (* nameInfo carries the print name and fixity for a constant *)
  type nameInfo = NameInfo of string

  open! struct
    let maxCid = Global.maxCid

    let nameArray =
      (Array.array (maxCid + 1, NameInfo "") : nameInfo Array.array)

    let sgnHashTable : IntSyn.cid HashTable.table = HashTable.new_ 4096
    let hashInsert = HashTable.insertShadow sgnHashTable
    let hashLookup = HashTable.lookup sgnHashTable
    let rec hashClear () = HashTable.clear sgnHashTable
  end

  (* nameArray maps constants to print names and fixity *)
  (* sgnHashTable maps identifiers (strings) to constants (cids) *)
  (* returns optional shadowed entry *)
  (* returns optional cid *)
  (* reset () = ()
       Effect: clear name tables related to constants

       nameArray does not need to be reset, since it is reset individually
       for every constant as it is declared
    *)
  let rec reset () = hashClear ()

  (* override (cid, nameInfo) = ()
       Effect: mark cid as shadowed --- it will henceforth print as %name%
    *)
  let rec override (cid, NameInfo name) =
    Array.update (nameArray, cid, NameInfo (("%" ^ name) ^ "%"))
  (* should shadowed identifiers keep their fixity? *)

  let rec shadow = function
    | None -> ()
    | Some (_, cid) -> override (cid, Array.sub (nameArray, cid))

  (* installName (name, cid) = ()
       Effect: update mappings from constants to print names and identifiers
               to constants, taking into account shadowing
    *)
  let rec installName (name, lemma) =
    let shadowed = hashInsert (name, lemma) in
    begin
      Array.update (nameArray, lemma, NameInfo name);
      shadow shadowed
    end
  (* returns optional shadowed entry *)

  (* nameLookup (name) = SOME(cid),  if cid has name and is not shadowed,
                         = NONE,   if there is no such constant
    *)
  let rec nameLookup name = hashLookup name

  (* constName (cid) = name,
       where `name' is the print name of cid
    *)
  let rec constName cid =
    begin match Array.sub (nameArray, cid) with NameInfo name -> name
    end
end
(* local ... *)
(* functor Names *)

(* # 1 "src/meta/Funnames.sml.ml" *)
