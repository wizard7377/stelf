include Smlofnj_intf

module SMLofNJ : SML_OF_NJ = struct
  let () = Printexc.record_backtrace true
  let exportML _ = true
  let exportFn _ = ()
  let getCmdName () = Sys.argv.(0)
  let getArgs () = Sys.argv |> Array.to_list |> List.tl
  let getAllArgs () = Sys.argv |> Array.to_list

  type 'a frag = QUOTE of string | ANTIQUOTE of 'a

  let exnHistory _e =
    let raw = Printexc.get_raw_backtrace () in
    match Printexc.backtrace_slots raw with
    | None -> []
    | Some slots ->
      Array.to_list slots |> List.filter_map (fun slot ->
        Printexc.Slot.format 0 slot
      )
end
