open! Basis

module Run = struct
  let argv = CommandLine.arguments ()
  let stat = RegressionTest.process (List.nth (argv, List.length argv - 1))
  let _ = OS.Process.exit stat
end
