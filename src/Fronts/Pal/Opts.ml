module type OPTS = OPTS.OPTS

module Opts : OPTS = struct
  open Cmdliner

  type 'a t = 'a Arg.t

  (* These four are the options every command accepts, so they belong under
     COMMON OPTIONS -- which is what each command's [~sdocs] points at -- rather
     than in each command's own OPTIONS section. *)
  let docs = Cmdliner.Manpage.s_common_options

  let verbosity : Display.Info.level t =
    begin
      let v_conv =
        Arg.vflag Display.Info.Level.normal
          [
            ( Display.Info.Level.quiet,
              Arg.info ~docs ~doc:"Display less information"
                [ "q"; "quiet" ] );
            ( Display.Info.Level.terse,
              Arg.info ~docs ~doc:"Display slightly less information"
                [ "t"; "terse" ] );
            ( Display.Info.Level.verbose,
              Arg.info ~docs ~doc:"Display more information"
                [ "v"; "verbose" ] );
            ( Display.Info.Level.debug,
              Arg.info ~docs ~doc:"Display debug information" [ "debug" ] );
          ]
      in
      v_conv
    end

  let mute : bool t =
    begin
      let doc : Arg.info =
        Arg.info ~docs ~doc:"Suppress all output, including errors"
          [ "s"; "silent"; "no-output" ]
      in
      Arg.flag doc
    end

  type color_when = Auto | Always | Never

  let color : color_when t =
    begin
      (* Not named [conv]: the [Arg.(...)] below opens Arg, where [conv] is a
         function, and the local binding would be shadowed. *)
      let color_conv =
        Arg.enum [ ("auto", Auto); ("always", Always); ("never", Never) ]
      in
      let doc : Arg.info =
        Arg.info ~docs
          ~doc:
            "When to colour output. $(b,auto), the default, follows the \
             terminal: styling is emitted only when standard error is a tty, \
             and is suppressed when $(b,TERM) is $(b,dumb) or $(b,NO_COLOR) is \
             set. $(b,always) forces styling even into a pipe or a file; \
             $(b,never) disables it entirely."
          [ "c"; "color"; "colour" ] ~docv:"WHEN"
      in
      Arg.(opt color_conv Auto doc)
    end

  let unicode : bool t =
    begin
      let doc : Arg.info =
        Arg.info ~docs ~doc:"Whether to use unicode characters"
          [ "u"; "unicode" ] ~docv:"UNICODE"
      in
      Arg.(opt bool true doc)
      (* TODO , make use Env variables *)
    end

  let file_list : string list t =
    begin
      let doc : Arg.info =
        Arg.info ~doc:"The list of files to process" [] ~docv:"FILES"
      in
      Arg.(pos_all string [] doc)
    end

  let help : string option t =
    begin
      let doc : Arg.info =
        Arg.info ~doc:"Display help information" [ "h"; "help" ] ~docv:"TOPIC"
      in
      Arg.(opt (some string) None doc)
    end
end
