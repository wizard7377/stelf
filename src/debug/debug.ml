let setup_log ~level () =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some level)

module Level = struct
  type t = Debug | Info | Warning | Error
end

module Group = struct
  let approx = Logs.Src.create "twelf.approx"
  let check = Logs.Src.create "twelf.check"
  let compile = Logs.Src.create "twelf.compile"
  let typecheck = Logs.Src.create "twelf.typecheck"
  let unify = Logs.Src.create "twelf.unify"
  let cover = Logs.Src.create "twelf.cover"
  let parse = Logs.Src.create "twelf.parse"
  let reduce = Logs.Src.create "twelf.reduce"
  let meta = Logs.Src.create "twelf.meta"
end

let msg (src : Logs.src) (level : Level.t) fmt args =
  match level with
  | Level.Debug -> Logs.debug ~src (fun m -> m "%a" fmt args)
  | Level.Info -> Logs.info ~src (fun m -> m "%a" fmt args)
  | Level.Warning -> Logs.warn ~src (fun m -> m "%a" fmt args)
  | Level.Error -> Logs.err ~src (fun m -> m "%a" fmt args)

module Fmt = Fmt
