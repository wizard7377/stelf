include module type of SOLVE

module Solve (Solve__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module ReconQuery : RECONQUERY.RECON_QUERY

  module Parser :
    PARSER.PARSER
      with type ExtQuery.query = ReconQuery.query
       and type ExtQuery.define = ReconQuery.define
       and type ExtQuery.solve = ReconQuery.solve

  (*! sharing ReconQuery.IntSyn = IntSyn' !*)
  (* sharing type ReconQuery.Paths.occConDec = Origins.Paths.occConDec *)
  module Timers : Timers.TIMERS

  (*! structure CompSyn : COMPSYN !*)
  (*! sharing CompSyn.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn !*)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn !*)
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn' !*)
  module AbsMachine : Absmachine.ABSMACHINE

  (*! sharing AbsMachine.IntSyn = IntSyn' !*)
  (*! sharing AbsMachine.CompSyn = CompSyn !*)
  module AbsMachineSbt : AbsmachineSbt.ABSMACHINESBT

  (*! sharing AbsMachineSbt.IntSyn = IntSyn' !*)
  (*! sharing AbsMachineSbt.CompSyn = CompSyn!*)
  module PtRecon : Ptrecon.PTRECON

  (*! sharing PtRecon.IntSyn = IntSyn' !*)
  (*! sharing PtRecon.CompSyn = CompSyn !*)
  (*! structure TableParam : TABLEPARAM !*)
  module Tabled : TabledMachine.TABLED

  (*! sharing Tabled.IntSyn = IntSyn' !*)
  (*! sharing Tabled.CompSyn = CompSyn !*)
  (*! structure MemoTable : MEMOTABLE !*)
  (*! sharing MemoTable.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Msg : MSG
end) : SOLVE with module ExtQuery = Solve__0.ReconQuery
