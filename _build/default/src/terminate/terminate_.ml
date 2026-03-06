# 1 "src/terminate/terminate_.sig.ml"

# 1 "src/terminate/terminate_.fun.ml"

# 1 "src/terminate/terminate_.sml.ml"
open! Basis;;
module Checking = (Checking)(struct
                               module Global = Global;;
                               (*! structure IntSyn' = IntSyn !*);;
                               module Whnf = Whnf;;
                               module Conv = Conv;;
                               module Unify = UnifyTrail;;
                               module Trail = Trail;;
                               module Names = Names;;
                               module Index = Index;;
                               module Subordinate = Subordinate;;
                               module Formatter = Formatter;;
                               module Print = Print;;
                               module Order = Order;;
                               module Paths = Paths;;
                               module Origins = Origins;;
                               end);;
(*! structure CSManager = CSManager !*);;
module Reduces = (Reduces)(struct
                             module Global = Global;;
                             (*! structure IntSyn' = IntSyn !*);;
                             module Whnf = Whnf;;
                             module Names = Names;;
                             module Index = Index;;
                             module Subordinate = Subordinate;;
                             module Formatter = Formatter;;
                             module Print = Print;;
                             module Order = Order;;
                             module Checking = Checking;;
                             module Paths = Paths;;
                             module Origins = Origins;;
                             end);;
(*! structure CSManager = CSManager !*);;