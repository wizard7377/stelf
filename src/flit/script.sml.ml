open! Flit
open! Basis

let rec dumpText (tcb, semant, checker, outputSemant, outputChecker) =
  let _ = Twelf.reset () in
  let _ = Flit.initForText () in
  let _ = Twelf.Print.width := Option.valOf Int.maxInt in
  let _ = Twelf.Print.implicit := true in
  let _ = Twelf.Print.printInfix := true in
  let _ = Twelf.Print.noShadow := true in
  let _ = Twelf.chatter := 1 in
  let _ = Twelf.reset () in
  let tcbConfig = Twelf.Config.read tcb in
  let _ = Twelf.Config.append tcbConfig in
  let _ = Flit.setEndTcb () in
  let semantConfig = Twelf.Config.readWithout (semant, tcbConfig) in
  let _ = Twelf.Config.append semantConfig in
  let _ = Flit.setFlag () in
  let _ = Twelf.Config.append (Twelf.Config.read checker) in
  let _ = Flit.dumpText (outputSemant, outputChecker) in
  ()
;;

dumpText
  ( "pcc/flit/ltal.cfg",
    "pcc/ltal/semant.cfg",
    "pcc/ltal/checker.cfg",
    "dumpsemant",
    "dumpchecker" )
