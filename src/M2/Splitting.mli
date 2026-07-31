open! Basis
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Subordinate
open! Subordinate
open! Table
open! Table.Table_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
include module type of SPLITTING

module Splitting (Splitting__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY
end) : SPLITTING.SPLITTING with module MetaSyn = Splitting__0.MetaSyn'
