open! Basis

(* Origins of Declarations *)
(* Author: Frank Pfenning *)
module MakeOrigins (Origins__0 : sig
  module Global : GLOBAL
  module Table : TABLE with type key = string
end) : ORIGINS = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  open! struct
    module Table = Origins__0.Table

    let linesInfoTable : Paths.linesInfo Table.table_ = Table.new_ 31
    let rec reset () = Table.clear linesInfoTable

    let rec install (string, linesInfo) =
      Table.insert linesInfoTable (string, linesInfo)

    let rec lookup string = Table.lookup linesInfoTable string
  end

  let reset = reset
  let installLinesInfo = install
  let linesInfoLookup = lookup

  open! struct
    let originArray =
      (Array.array (Global.maxCid + 1, ("", None))
        : (string * Paths.occConDec option) Array.array)
  end

  let rec installOrigin (cid, fileNameOpt) =
    Array.update (originArray, cid, fileNameOpt)

  let rec originLookup cid = Array.sub (originArray, cid)
end
(*! structure IntSyn' : INTSYN !*)
(*! structure Paths' : PATHS !*)
(* functor Origins *)
