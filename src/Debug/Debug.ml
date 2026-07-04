let setup_log ~level () =
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level (Some level)

module Level = struct
  type t = Debug | Info | Warning | Error | App

  let log_level = function
    | Debug -> Logs.Debug
    | Info -> Logs.Info
    | Warning -> Logs.Warning
    | Error -> Logs.Error
    | App -> Logs.App

  let from_chatter x =
    assert (x >= 0);
    match x with
    | 0 -> Error
    | 1 | 2 | 3 -> Warning
    | 4 -> Info
    | _ -> Debug
end

module Group = struct
  let approx = Logs.Src.create "stelf.approx"
  let check = Logs.Src.create "stelf.check"
  let compile = Logs.Src.create "stelf.compile"
  let typecheck = Logs.Src.create "stelf.typecheck"
  let unify = Logs.Src.create "stelf.unify"
  let cover = Logs.Src.create "stelf.cover"
  let parse = Logs.Src.create "stelf.parse"
  let reduce = Logs.Src.create "stelf.reduce"
  let meta = Logs.Src.create "stelf.meta"
  let pal = Logs.Src.create "stelf.pal"
  let default = Logs.Src.create "stelf"
end

let msg' ?(src = Group.default) ?(level = Level.Info) (fmt : 'a Fmt.t)
    (args : 'a) : unit =
  match level with
  | Level.Debug -> Logs.debug ~src (fun m -> m "%a" fmt args)
  | Level.Info -> Logs.info ~src (fun m -> m "%a" fmt args)
  | Level.Warning -> Logs.warn ~src (fun m -> m "%a" fmt args)
  | Level.Error -> Logs.err ~src (fun m -> m "%a" fmt args)
  | Level.App -> Logs.app ~src (fun m -> m "%a" fmt args)

let msg ?(src = Group.default) ?(level = Level.Info) (fmt : unit Fmt.t) : unit =
  msg' ~src ~level fmt ()

module Fmt = struct
  include Fmt

  let exact (x : string) : 'a Fmt.t = Fmt.const Fmt.string x
  let shown (f : 'a -> string) : 'a Fmt.t = Fmt.using f Fmt.string

  let shown_exact (f : 'a -> string) (x : 'a) : 'b Fmt.t =
    Fmt.const (Fmt.using f Fmt.string) x
end
