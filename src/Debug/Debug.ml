module Level = struct
  type t = Debug | Info | Warning | Error | App
end

module Group = struct
  let approx = Display.Info.Approx
  let check = Display.Info.Check
  let compile = Display.Info.Compile
  let typecheck = Display.Info.Typecheck
  let unify = Display.Info.Unify
  let cover = Display.Info.Cover
  let parse = Display.Info.Parse
  let reduce = Display.Info.Reduce
  let meta = Display.Info.Meta
  let pal = Display.Info.Pal
  let default = Display.Info.Default
end

let msg'' ?(src = Group.default) ?(level = Level.Info) (fmt : 'a Fmt.t)
    (args : 'a) : unit =
  match level with
  | Level.Debug ->
      Display.message ~src ~level:Display.Level.debug (fun f ->
          Format.fprintf f "%a" fmt args)
  | Level.Info ->
      Display.message ~src ~level:Display.Level.normal (fun f ->
          Format.fprintf f "%a" fmt args)
  | Level.Warning ->
      Display.message ~src ~level:Display.Level.terse (fun f ->
          Format.fprintf f "%a" fmt args)
  | Level.Error ->
      Display.message ~src ~level:Display.Level.quiet (fun f ->
          Format.fprintf f "%a" fmt args)
  | Level.App ->
      Display.message ~src ~level:Display.Level.normal (fun f ->
          Format.fprintf f "%a" fmt args)

let msg' ?(src = Group.default) ?(level = Level.Info) (fmt : 'a Fmt.t)
    (args : 'a) : unit =
  msg'' ~src ~level fmt args

let msg ?(src = Group.default) ?(level = Level.Info) (fmt : unit Fmt.t) : unit =
  msg' ~src ~level fmt ()

module Fmt = struct
  include Fmt

  let exact (x : string) : 'a Fmt.t = Fmt.const Fmt.string x
  let shown (f : 'a -> string) : 'a Fmt.t = Fmt.using f Fmt.string

  let shown_exact (f : 'a -> string) (x : 'a) : 'b Fmt.t =
    Fmt.const (Fmt.using f Fmt.string) x
end
