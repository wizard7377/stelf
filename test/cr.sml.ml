open! Basis

let rec test file =
  begin match Twelf.Config.load (Twelf.Config.read file) with
  | ok_ -> Twelf.ok_
  | abort_ -> raise Domain
  end
;;

Twelf.unsafe := true;;
test "examples/church-rosser/test-unsafe.cfg";;
Twelf.unsafe := false
