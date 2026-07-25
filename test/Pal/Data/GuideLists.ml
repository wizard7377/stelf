(* List append, element type, and list sort.
   Ported from twelf/examples/guide/lists.elf.
   Note: %query directives omitted (not supported).
   Element type 'o' declared here to keep this chunk self-contained.
*)
let guide_lists_types =
  {|
%sort o
%sort list
%term nil list
%term cons {_ o} {_ list} list
|}

let guide_lists_append =
  {|
%sort append {_ list} {_ list} {_ list}
%term appNil {K list} append nil K K
%term appCons {A o} {L list} {K list} {M list} %if (append (cons A L) K (cons A M)) %<- (append L K M)
|}

let guide_lists_mode =
  {|
%mode append %in %in %out
%worlds () (append _ _ _)
%total L (append L _ _)
|}
