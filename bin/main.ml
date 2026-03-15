let main () : int = Server.Server_.Server.server ("twelf", [])
let () = if main () = 0 then exit 0 else exit 1
