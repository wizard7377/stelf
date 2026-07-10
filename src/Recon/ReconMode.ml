module type RECON_MODE = RECON_MODE.RECON_MODE

exception Error of string

module ModeDec = Modes.Modedec.MakeModeDec ()

let ghost_region = Paths.Paths_.Paths.Reg (0, 0)

module Make_ReconMode (M : S.S) : RECON_MODE with module M = M = struct
  module M = M
  module Syntax = M.Syntax
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Modes = Modes.Modesyn.ModeSyn

  exception Error = Error

  let raise' m =
    Display.(
      error ~src:Info.Recon
        (string "Error processing mode declaration: " ++ string m));
    raise (Error m)

  let modeToMode md =
    try
      begin match Cst.View.Mode.Dec.view md with
      | Cst.View.Mode.Dec.ModeDec (_, spine, root) ->
          let sym =
            match Cst.View.Mode.Term.view root with
            | Cst.View.Mode.Term.ModeTerm (_, sym, _) -> sym
            | _ -> raise' "Mode declaration root is not a constant"
          in
          let ns, id = sym in
          let qid = Qid (ns, id) in
          begin match constLookup qid with
          | None ->
              raise
                (Error
                   ("Undeclared identifier "
                   ^ qidToString (valOf (constUndef qid))
                   ^ " in mode declaration"))
          | Some cid ->
              if spine = [] then begin
                let mS = ModeDec.shortToFull (cid, Modes.Mnil, ghost_region) in
                ((cid, mS), Paths.Reg (0, 0))
              end
              else begin
                let convert_mode m =
                  match Cst.View.Mode.view m with
                  | Cst.View.Mode.Plus _ -> Modes.Plus
                  | Cst.View.Mode.Star _ -> Modes.Star
                  | Cst.View.Mode.Minus _ -> Modes.Minus
                  | Cst.View.Mode.Minus1 _ -> Modes.Minus1
                  | _ -> assert false
                in
                let rec build_spine = function
                  | [] -> Modes.Mnil
                  | (m, name_opt) :: rest ->
                      Modes.Mapp
                        (Modes.Marg (convert_mode m, name_opt), build_spine rest)
                in
                let mS_short = build_spine spine in
                let mS = ModeDec.shortToFull (cid, mS_short, ghost_region) in
                ((cid, mS), Paths.Reg (0, 0))
              end
          end
      | _ -> raise' "Invalid mode declaration"
      end
    with Error m -> raise' m
end
