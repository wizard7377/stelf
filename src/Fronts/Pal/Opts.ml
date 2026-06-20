module type OPTS = OPTS.OPTS

module Opts : OPTS = struct
  open Cmdliner

  type 'a t = 'a Arg.t

  let verbosity : Display.Info.level t =
    begin
      let doc : Arg.info =
        Arg.info ~doc:"The verbosity level" [ "v"; "verbose" ] ~docv:"LEVEL"
      and v_conv =
        Arg.enum
          [
            ("terse", Display.Info.Terse);
            ("normal", Display.Info.Normal);
            ("detailed", Display.Info.Detailed);
            ("exhaustive", Display.Info.Exhaustive);
            ("minimal", Display.Info.Minimal);
            ("off", Display.Info.Off);
          ]
      in
      Arg.(opt v_conv Display.Info.(Normal) & doc)
    end

  let color : bool t =
    begin
      let doc : Arg.info =
        Arg.info ~doc:"Whether to use colors in output" [ "c"; "color" ]
          ~docv:"COLOR"
      in
      Arg.(opt bool true doc)
      (* TODO , make use Env variables *)
    end

  let unicode : bool t =
    begin
      let doc : Arg.info =
        Arg.info ~doc:"Whether to use unicode characters" [ "u"; "unicode" ]
          ~docv:"UNICODE"
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
