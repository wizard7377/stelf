open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Table
open! Table.Table_
open! Msg
open! Msg.Msg_
open! Print
open! Print.Print_
open! Debug

module type RECON_MODE = RECON_MODE.RECON_MODE

exception Error of string

module ModeDec = Modes.Modedec.MakeModeDec ()

let ghost_region = Paths.Paths_.Paths.Reg (0, 0)

(* Substring search without relying on Basis's SML-flavored String shadowing
   (this file has [-open Basis]) or pulling in a regex library for one check. *)
let string_contains ~needle haystack =
  let nlen = Stdlib.String.length needle in
  let hlen = Stdlib.String.length haystack in
  let rec go i =
    i + nlen <= hlen
    && (Stdlib.String.sub haystack i nlen = needle || go (i + 1))
  in
  go 0

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
                let mS = ModeDec.shortToFull cid Modes.Mnil ghost_region in
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
                let mS_user = build_spine spine in
                (* Braced %mode {...} is ambiguous between short- and full-form
                   at parse time (depends on the constant's arity), so try
                   short-form first and only reinterpret as full-form spine on
                   "too many modes specified". *)
                try
                  let mS = ModeDec.shortToFull cid mS_user ghost_region in
                  ((cid, mS), Paths.Reg (0, 0))
                with
                | ModeDec.Error msg
                when string_contains ~needle:"Too many modes specified" msg
                ->
                  ModeDec.checkFull cid mS_user ghost_region;
                  ((cid, mS_user), Paths.Reg (0, 0))
              end
          end
      | _ -> raise' "Invalid mode declaration"
      end
    with Error m -> raise' m
end
