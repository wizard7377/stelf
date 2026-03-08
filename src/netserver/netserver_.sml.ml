open! Basis

module type NETSERVER = sig
  (* int argument is which port number to run on *)
  val flashServer : int -> unit

  (* Macromedia Flash XMLSocket interface *)
  val humanServer : int -> unit

  (* Human-readable interface, suitable for telnet *)
  (* second argument is what directory server.html is kept in *)
  val httpServer : int -> string -> unit

  (* HTTP interface, suitable for javascript XMLHttpRequest *)
  val setExamplesDir : string -> unit
end

(* filesystem directory where twelf examples are kept *)
(* signature SERVER *)
module NetServer (NetServer__0 : sig
  module Timing : TIMING
  module Twelf : TWELF
  module Msg : MSG
end) : NETSERVER = struct
  let rec join arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | delim, [] -> ""
    | delim, x :: [] -> x
    | delim, h :: tl -> (h ^ delim) ^ join delim tl
    end

  type nonrec __0 = { send : string -> unit; exec : string -> unit }
  type nonrec server = __0

  type nonrec __1 = {
    init : unit -> unit;
    reset : unit -> unit;
    recv : server -> string -> unit;
    send : server -> string -> unit;
    done_ : unit -> unit;
  }

  type nonrec protocol = __1

  module S = Socket

  let maxConnections = 128

  (* queue size for waiting connections in listen *)
  (* below --- set to some arbitrary high value. *)
  (* fun loop f state = loop f (f state) *)
  let rec loop f =
    begin
      f ();
      loop f
    end

  let rec vec2str v =
    String.implode
      (map (fun x -> Char.chr (Word8.toInt x)) (Word8Vector.foldr ( :: ) [] v))

  let rec str2vec l =
    Word8Vector.fromList
      (map (fun x -> Word8.fromInt (Char.ord x)) (String.explode l))

  let rec fileText fname =
    let s = TextIO.openIn fname in
    let txt = TextIO.inputAll s in
    let _ = TextIO.closeIn s in
    txt

  let rec fileData fname =
    let s = BinIO.openIn fname in
    let data = BinIO.inputAll s in
    let _ = BinIO.closeIn s in
    vec2str data

  exception Eof
  exception Quit

  let rec send conn str =
    begin
      Compat.SocketIO.sendVec (conn, str2vec str);
      ()
    end

  open! struct
    module SS = Substring
  end

  let rec parseCmd s =
    let c, a = SS.position " " (Compat.Substring.full s) in
    (SS.string c, SS.string (SS.dropl Char.isSpace a))

  let rec quote string = ("`" ^ string) ^ "'"
  let examplesDir : string option ref = ref None
  let rec setExamplesDir s = examplesDir := Some s

  (* exception Error for server errors *)
  exception Error of string

  let rec error msg = raise (Error msg)

  let rec serveExample e =
    begin if
      begin match e with
      | "ccc" -> true
      | "cut-elim" -> true
      | "handbook" -> true
      | "lp-horn" -> true
      | "prop-calc" -> true
      | "units" -> true
      | "church-rosser" -> true
      | "fj" -> true
      | "incll" -> true
      | "mini-ml" -> true
      | "small-step" -> true
      | "alloc-sem" -> true
      | "compile" -> true
      | "fol" -> true
      | "kolm" -> true
      | "modal" -> true
      | "tabled" -> true
      | "arith" -> true
      | "cpsocc" -> true
      | "guide" -> true
      | "lp" -> true
      | "polylam" -> true
      | "tapl-ch13" -> true
      | _ -> false
    end
    then
      try
        begin
          OS.FileSys.chDir ((Option.valOf !examplesDir ^ "/") ^ e);
          Twelf.make "sources.cfg"
        end
      with e -> raise (Error (("Exception " ^ exnName e) ^ " raised."))
    else raise (Error ("Unknown example " ^ quote e))
    end

  (* Natural numbers *)
  let rec getNat = function
    | t :: [] -> (
        try Lexer.stringToNat t with
        | Lexer.NotDigit char -> error (quote t ^ " is not a natural number")
        | [] -> error "Missing natural number"
        | ts -> error "Extraneous arguments")

  (* Example specifiers *)
  let rec getExample = function
    | t :: [] -> t
    | [] -> error "Missing example"
    | ts -> error "Extraneous arguments"

  (* Setting Twelf parameters *)
  let rec setParm = function
    | "chatter" :: ts -> Twelf.chatter := getNat ts
    | t :: ts -> error ("Unknown parameter " ^ quote t)
    | [] -> error "Missing parameter"

  let rec exec' arg__3 arg__4 =
    begin match (arg__3, arg__4) with
    | conn, ("quit", args) -> begin
        Msg.message "goodbye.\n";
        raise Quit
      end
    | conn, ("set", args) -> begin
        setParm (String.tokens Char.isSpace args);
        Twelf.ok_
      end
    | conn, ("readDecl", args) -> Twelf.loadString args
    | conn, ("decl", args) -> Twelf.decl args
    | conn, ("example", args) ->
        serveExample (getExample (String.tokens Char.isSpace args))
    | conn, (t, args) -> raise (Error ("Unrecognized command " ^ quote t))
    end

  let rec exec conn str =
    begin match
      try exec' conn (parseCmd str)
      with Error s ->
        begin
          Msg.message (("Server Error: " ^ s) ^ "\n");
          Twelf.abort_
        end
    with
    | ok_ -> Msg.message "%%% OK %%%\n"
    | abort_ -> Msg.message "%%% ABORT %%%\n"
    end

  let rec stripcr s =
    Substring.string
      (Substring.dropr (function x -> x = 'r') (Compat.Substring.full s))

  let rec flashProto () =
    let buf : string ref = ref "" in
    let rec isnull = function '\000' -> true | _ -> false in
    let rec recv (u : server) s =
      let _ = buf := !buf ^ s in
      let (rem :: cmds) = rev (String.fields isnull !buf) in
      let _ = App_ ((fun r -> r.exec) u, rev cmds) in
      buf := rem
    in
    let rec send (u : server) s = (fun r -> r.send) u (s ^ "\000") in
    {
      init =
        (function
        | () -> (
            Msg.message (Twelf.version ^ "\n%%% OK %%%\n");
            reset = function
            | () -> (
                buf := "";
                send;
                recv;
                done_ = function () -> ())));
    }

  let rec humanProto () =
    let buf : string ref = ref "" in
    let rec isnewl = function '\n' -> true | 'r' -> false | _ -> false in
    let rec recv (u : server) s =
      let _ = buf := !buf ^ s in
      let (rem :: cmds) = rev (String.fields isnewl !buf) in
      let _ = App_ ((fun r -> r.exec) u, map stripcr (rev cmds)) in
      buf := rem
    in
    let rec send (u : server) s = (fun r -> r.send) u ("> " ^ s) in
    {
      init =
        (function
        | () -> (
            Msg.message (Twelf.version ^ "\n%%% OK %%%\n");
            reset = function
            | () -> (
                buf := "";
                send;
                recv;
                done_ = function () -> ())));
    }

  let rec httpProto dir =
    let ibuf : string ref = ref "" in
    let obuf : string ref = ref "" in
    let parsingHeaders = ref true in
    let contentLength = ref 0 in
    let method_ : string ref = ref "" in
    let url : string ref = ref "" in
    let headers : string list ref = ref [] in
    let rec isnewl = function '\n' -> true | _ -> false in
    let rec handlePostRequest (u : server) =
      let shouldQuit =
        try
          begin
            (fun r -> r.exec) u !ibuf;
            false
          end
        with Quit -> true
      in
      let response = !obuf in
      let clmsg = ("Content-Length: " ^ Int.toString (size response)) ^ "\n" in
      begin
        (fun r -> r.send)
          u
          (("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg) ^ "\n");
        begin
          (fun r -> r.send) u response;
          begin if shouldQuit then raise Quit else raise Eof
          end
        end
      end
    in
    let rec handleGetRequest (u : server) =
      let ok = "200 OK" in
      let missing = "404 Not Found" in
      let content, ctype, rcode =
        begin match !url with
        | "/" -> (fileText (dir ^ "/server.html"), "application/xhtml+xml", ok)
        | "/server.js" -> (fileText (dir ^ "/server.js"), "text/plain", ok)
        | "/server.css" -> (fileText (dir ^ "/server.css"), "text/css", ok)
        | "/grad.png" -> (fileData (dir ^ "/grad.png"), "image/png", ok)
        | "/twelfguy.png" -> (fileData (dir ^ "/twelfguy.png"), "image/png", ok)
        | "/input.png" -> (fileData (dir ^ "/input.png"), "image/png", ok)
        | "/output.png" -> (fileData (dir ^ "/output.png"), "image/png", ok)
        | "/floral.png" -> (fileData (dir ^ "/floral.png"), "image/png", ok)
        | _ -> ("Error 404", "text/plain", missing)
        end
      in
      let clmsg = ("Content-Length: " ^ Int.toString (size content)) ^ "\r\n" in
      let ctmsg = ("Content-Type: " ^ ctype) ^ "\r\n" in
      let resp = ("HTTP/1.1 " ^ rcode) ^ "\r\n" in
      begin
        (fun r -> r.send) u (((resp ^ ctmsg) ^ clmsg) ^ "\r\n");
        begin
          (fun r -> r.send) u content;
          begin
            raise Eof;
            ()
          end
        end
      end
    in
    let rec handleRequest (u : server) =
      begin if !method_ = "GET" then handleGetRequest u
      else begin
        if !method_ = "POST" then handlePostRequest u
        else (fun r -> r.send) u "HTTP/1.1 500 Server Error\n\n"
      end
      end
    in
    let rec headerExec s = headers := s :: !headers in
    let rec recvContent u =
      begin if size !ibuf >= !contentLength then handleRequest u else ()
      end
    in
    let rec parseHeaders () =
      try
        let (request :: headers) = rev !headers in
        let [ m; u; httpVersion ] =
          String.tokens (function x -> x = ' ') request
        in
        let _ = method_ := m in
        let _ = url := u in
        let rec getField s =
          let (k :: v) = String.fields (function x -> x = ':') s in
          let v = join ":" v in
          (k, substring (v, 1, size v - 1))
        in
        let rec proc_one s =
          let k, v = getField s in
          begin if k = "Content-Length" then
            contentLength :=
              begin match Int.fromString v with None -> 0 | Some n -> n
              end
          else ()
          end
        in
        let () = App_ (proc_one, headers) in
        parsingHeaders := false
      with bind_ -> raise Eof
    in
    let rec interp arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | (u : server), [] -> raise Match
      | u, x :: [] -> ibuf := x
      | u, h :: tl ->
          let sch = stripcr h in
          begin if sch = "" then begin
            ibuf := join "\n" tl;
            begin
              parseHeaders ();
              recvContent u
            end
          end
          else begin
            headerExec (stripcr h);
            interp u tl
          end
          end
      end
    in
    let rec recv (u : server) s =
      begin
        ibuf := !ibuf ^ s;
        begin if !parsingHeaders then interp u (String.fields isnewl !ibuf)
        else recvContent u
        end
      end
    in
    let rec send (u : server) s = obuf := !obuf ^ s in
    let rec reset () =
      begin
        parsingHeaders := true;
        begin
          ibuf := "";
          begin
            obuf := "";
            begin
              contentLength := 0;
              begin
                headers := [];
                begin
                  url := "";
                  method_ := ""
                end
              end
            end
          end
        end
      end
    in
    {
      init =
        (function
        | () -> (
            ();
            reset;
            send;
            recv;
            done_ = function () -> ()));
    }

  let rec protoServer (proto : protocol) portNum =
    let sock = INetSock.TCP.socket () in
    let _ = S.Ctl.setREUSEADDR (sock, true) in
    let _ = S.bind (sock, INetSock.any portNum) in
    let _ = S.listen (sock, maxConnections) in
    let rec read_one conn u () =
      let v = S.recvVec (conn, 1024) in
      begin if Word8Vector.length v = 0 then raise Eof
      else (fun r -> r.recv) proto u (vec2str v)
      end
      (* arbitrary buffer size *)
    in
    let rec accept_one () =
      let conn, addr = S.accept sock in
      let _ = (fun r -> r.reset) proto () in
      let u = { send = send conn; exec = exec conn } in
      let _ = Msg.setMessageFunc ((fun r -> r.send) proto u) in
      let _ = (fun r -> r.init) proto () in
      try loop (read_one conn u) with
      | Eof -> begin
          (fun r -> r.done_) proto ();
          S.close conn
        end
      | Quit -> begin
          (fun r -> r.done_) proto ();
          begin
            S.close conn;
            raise Quit
          end
        end
    in
    try loop accept_one with Quit -> S.close sock

  let rec flashServer port = protoServer (flashProto ()) port
  let rec humanServer port = protoServer (humanProto ()) port
  let rec httpServer port dir = protoServer (httpProto dir) port
end

module NetServer = NetServer (struct
  module Timing = Timing
  module Twelf = Twelf
  module Msg = Msg
end)
