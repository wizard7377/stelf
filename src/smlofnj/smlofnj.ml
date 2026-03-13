include Smlofnj_intf

module SMLofNJ : SML_OF_NJ = struct
  let exportML _ = true
  let exportFn _ = ()
  let getCmdName () = Sys.argv.(0)
  let getArgs () = Sys.argv |> Array.to_list |> List.tl
  let getAllArgs () = Sys.argv |> Array.to_list

  type 'a frag = QUOTE of string | ANTIQUOTE of 'a

  let exnHistory _e = assert false
end
