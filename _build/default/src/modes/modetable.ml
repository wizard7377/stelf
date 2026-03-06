# 1 "src/modes/modetable.sig.ml"
open! Basis;;
(* Mode Table *);;
(* Author: Frank Pfenning *);;
module type MODETABLE = sig
                        exception Error of string 
                        val reset : unit -> unit
                        (* single mode installation and lookup *)
                        val
                          installMode : (IntSyn.cid * ModeSyn.modeSpine_) ->
                                        unit
                        val
                          modeLookup : IntSyn.cid ->
                                       ModeSyn.modeSpine_
                                       option
                        val uninstallMode : IntSyn.cid -> bool
                        (* true: was declared, false: not *)
                        (* multiple mode installation and lookup *)
                        val
                          installMmode : (IntSyn.cid * ModeSyn.modeSpine_) ->
                                         unit
                        val
                          mmodeLookup : IntSyn.cid -> ModeSyn.modeSpine_ list
                        end;;
(* signature MODETABLE *);;
# 1 "src/modes/modetable.fun.ml"
open! Basis;;
(* Mode Table *);;
(* Author: Carsten Schuermann *);;
(* Modified: Frank Pfenning, Roberto Virga *);;
module ModeTable(ModeTable__0: sig module Table : TABLE end) : MODETABLE =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    exception Error of string ;;
    open!
      struct
        module I = IntSyn;;
        module M = ModeSyn;;
        let modeSignature : M.modeSpine_ list Table.table_ = Table.new_ 0;;
        let rec reset () = Table.clear modeSignature;;
        let rec modeLookup a =
          begin
          match Table.lookup modeSignature a
          with 
               | Some ((mS :: _)) -> (Some mS)
               | None -> None
          end;;
        let rec mmodeLookup a =
          begin
          match Table.lookup modeSignature a
          with 
               | Some mSs -> mSs
               | None -> []
          end;;
        let rec installMode (a, mS) = Table.insert modeSignature (a, [mS]);;
        let rec uninstallMode a =
          begin
          match modeLookup a
          with 
               | None -> false
               | Some _ -> begin
                             Table.delete modeSignature a;true
                             end
          end;;
        let rec installMmode (a, mS) =
          let mSs = mmodeLookup a
            in Table.insert modeSignature (a, (mS :: mSs));;
        end;;
    (* reset () = ()

       Effect: Resets mode array
    *);;
    (* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *);;
    (* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *);;
    (* installMode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *);;
    (* uninstallMode a = true iff a was declared in mode table
       Effect: the mode stored with a is removed
    *);;
    (* installMmode (a, mS) = ()

       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *);;
    let reset = reset;;
    let installMode = installMode;;
    let modeLookup = modeLookup;;
    let uninstallMode = uninstallMode;;
    let installMmode = installMmode;;
    let mmodeLookup = mmodeLookup;;
    end;;
(*! structure IntSyn' : INTSYN !*);;
(* structure Names : NAMES *);;
(*! sharing Names.IntSyn = IntSyn' !*);;
(* structure Index : INDEX *);;
(*! sharing Index.IntSyn = IntSyn' !*);;
(* functor ModeTable *);;
# 1 "src/modes/modetable.sml.ml"
