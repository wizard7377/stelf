open! Basis;;
;;NetServer.setExamplesDir "/usr0/stuff/twelf-cvs/examples";;
let rec httpServer _ =
  begin
    NetServer.httpServer 1066 "/usr0/stuff/twelf-cvs/src/netserver/htdocs";
    OS.Process.success
    end;;
;;SMLofNJ.exportFn ("netserver.heap", httpServer);;