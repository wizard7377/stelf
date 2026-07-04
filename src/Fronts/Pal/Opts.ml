module type OPTS = OPTS.OPTS

module Opts : OPTS = struct
  open Cmdliner

  type 'a t = 'a Arg.t

  let verbosity : Display.Info.level t =
    begin
      let v_conv =
        Arg.vflag Display.Info.Normal
          [
          (Display.Info.Terse, Arg.info ~doc:"Display less information" [ "q"; "quiet" ]);
            (Display.Info.Detailed, Arg.info ~doc:"Display more information" [ "v"; "verbose" ]); 
            (Display.Info.Exhaustive, Arg.info ~doc:"Display exhaustive information" [ "debug" ]);
            (Display.Info.Minimal, Arg.info ~doc:"Display minimal information" [ "s"; "silent" ]);
            (Display.Info.Off, Arg.info ~doc:"Display no information" [ "no-output" ]);
          ]
      in
      v_conv
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
