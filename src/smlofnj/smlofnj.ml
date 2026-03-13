include Smlofnj_intf

module SMLofNJ : SML_OF_NJ = struct 
  let exportML = assert false
  let exportFn = assert false
  let getCmdName = assert false
  let getArgs = assert false
  let getAllArgs = assert false
  type 'a frag
    = QUOTE of string
    | ANTIQUOTE of 'a
  let exnHistory = assert false
end