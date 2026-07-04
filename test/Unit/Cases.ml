let cases () =
  Alcotest.run "Unit"
    (TableTests.suites
    @ TrailTests.suites
    @ WhnfTests.suites
    @ ConvTests.suites
    @ UnifyTests.suites
    @ AbstractTests.suites)
