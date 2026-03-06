open! Basis;;
module MetaSyn = (MetaSyn)(struct
                             (*! structure IntSyn' = IntSyn !*);;
                             module Whnf = Whnf;;
                             end);;
module MetaAbstract = (MetaAbstract)(struct
                                       module Global = Global;;
                                       module MetaSyn' = MetaSyn;;
                                       module MetaGlobal = MetaGlobal;;
                                       module Abstract = Abstract;;
                                       module ModeTable = ModeTable;;
                                       module Whnf = Whnf;;
                                       module Print = Print;;
                                       module Constraints = Constraints;;
                                       module Unify = UnifyNoTrail;;
                                       module Names = Names;;
                                       module TypeCheck = TypeCheck;;
                                       module Subordinate = Subordinate;;
                                       end);;
(*! structure CSManager = CSManager !*);;
module MetaPrint = (MetaPrint)(struct
                                 module Global = Global;;
                                 module MetaSyn' = MetaSyn;;
                                 module Formatter = Formatter;;
                                 module Print = Print;;
                                 module ClausePrint = ClausePrint;;
                                 end);;
module Init = (Init)(struct
                       module MetaSyn' = MetaSyn;;
                       module MetaAbstract = MetaAbstract;;
                       end);;
module OLDSearch = (OLDSearch)(struct
                                 module MetaGlobal = MetaGlobal;;
                                 module Conv = Conv;;
                                 module MetaSyn' = MetaSyn;;
                                 (*! structure CompSyn' = CompSyn !*);;
                                 module Compile = Compile;;
                                 module Whnf = Whnf;;
                                 module Unify = UnifyTrail;;
                                 module Index = IndexSkolem;;
                                 (* structure Assign = Assign *);;
                                 module CPrint = CPrint;;
                                 module Print = Print;;
                                 module Names = Names;;
                                 end);;
(*! structure CSManager = CSManager !*);;
module Lemma = (Lemma)(struct
                         module MetaSyn' = MetaSyn;;
                         module MetaAbstract = MetaAbstract;;
                         end);;
module Splitting = (Splitting)(struct
                                 module Global = Global;;
                                 module MetaSyn' = MetaSyn;;
                                 module MetaPrint = MetaPrint;;
                                 module MetaAbstract = MetaAbstract;;
                                 module Whnf = Whnf;;
                                 module ModeTable = ModeTable;;
                                 module Index = Index;;
                                 module Print = Print;;
                                 module Unify = UnifyTrail;;
                                 end);;
(*! structure CSManager = CSManager !*);;
module Filling = (Filling)(struct
                             module Global = Global;;
                             module MetaSyn' = MetaSyn;;
                             module MetaAbstract = MetaAbstract;;
                             module Print = Print;;
                             module Search = OLDSearch;;
                             module Whnf = Whnf;;
                             end);;
module Recursion = (Recursion)(struct
                                 module Global = Global;;
                                 module MetaSyn' = MetaSyn;;
                                 module MetaPrint = MetaPrint;;
                                 module Whnf = Whnf;;
                                 module Unify = UnifyTrail;;
                                 module Conv = Conv;;
                                 module Names = Names;;
                                 module Print = Print;;
                                 module Subordinate = Subordinate;;
                                 module Order = Order;;
                                 module ModeTable = ModeTable;;
                                 module MetaAbstract = MetaAbstract;;
                                 module Lemma = Lemma;;
                                 module Filling = Filling;;
                                 module Formatter = Formatter;;
                                 end);;
(*! structure CSManager = CSManager !*);;
module Qed = (Qed)(struct
                     module Global = Global;;
                     module MetaSyn' = MetaSyn;;
                     end);;
module StrategyFRS = (StrategyFRS)(struct
                                     module MetaGlobal = MetaGlobal;;
                                     module MetaSyn' = MetaSyn;;
                                     module MetaAbstract = MetaAbstract;;
                                     module Lemma = Lemma;;
                                     module Filling = Filling;;
                                     module Recursion = Recursion;;
                                     module Splitting = Splitting;;
                                     module Qed = Qed;;
                                     module MetaPrint = MetaPrint;;
                                     module Timers = Timers;;
                                     end);;
module StrategyRFS = (StrategyRFS)(struct
                                     module MetaGlobal = MetaGlobal;;
                                     module MetaSyn' = MetaSyn;;
                                     module MetaAbstract = MetaAbstract;;
                                     module Lemma = Lemma;;
                                     module Filling = Filling;;
                                     module Recursion = Recursion;;
                                     module Splitting = Splitting;;
                                     module Qed = Qed;;
                                     module MetaPrint = MetaPrint;;
                                     module Timers = Timers;;
                                     end);;
module Strategy = (Strategy)(struct
                               module MetaGlobal = MetaGlobal;;
                               module MetaSyn' = MetaSyn;;
                               module StrategyFRS = StrategyFRS;;
                               module StrategyRFS = StrategyRFS;;
                               end);;
module Prover = (Prover)(struct
                           module MetaGlobal = MetaGlobal;;
                           module MetaSyn' = MetaSyn;;
                           module MetaAbstract = MetaAbstract;;
                           module MetaPrint = MetaPrint;;
                           module Filling = Filling;;
                           module Splitting = Splitting;;
                           module Recursion = Recursion;;
                           module Init = Init;;
                           module Strategy = Strategy;;
                           module Qed = Qed;;
                           module Names = Names;;
                           module Timers = Timers;;
                           end);;
module Mpi = (Mpi)(struct
                     module MetaGlobal = MetaGlobal;;
                     module MetaSyn' = MetaSyn;;
                     module MetaAbstract = MetaAbstract;;
                     module Init = Init;;
                     module Lemma = Lemma;;
                     module Filling = Filling;;
                     module Recursion = Recursion;;
                     module Splitting = Splitting;;
                     module Strategy = Strategy;;
                     module Qed = Qed;;
                     module MetaPrint = MetaPrint;;
                     module Names = Names;;
                     module Timers = Timers;;
                     module Ring = Ring;;
                     end);;
module Skolem = (Skolem)(struct
                           module Global = Global;;
                           (*! structure IntSyn' = IntSyn !*);;
                           module Whnf = Whnf;;
                           module Abstract = Abstract;;
                           module IndexSkolem = IndexSkolem;;
                           module ModeTable = ModeTable;;
                           module Print = Print;;
                           module Timers = Timers;;
                           module Compile = Compile;;
                           module Names = Names;;
                           end);;