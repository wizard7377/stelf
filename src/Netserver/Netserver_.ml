(* # 1 "src/netserver/Netserver_.sig.ml" *)

(* # 1 "src/netserver/Netserver_.fun.ml" *)

(* # 1 "src/netserver/Netserver_.sml.ml" *)
open! Basis
include NETSERVER

(* filesystem directory where stelf examples are kept *)
(* signature SERVER *)
exception Eof

let () =
  Printexc.register_printer (function Eof -> Some "End of file" | _ -> None)

exception Quit

let () = Printexc.register_printer (function Quit -> Some "Quit" | _ -> None)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module NetServer : NETSERVER = struct
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

  let vec2str v =
    String.implode
      (Vector.foldr (fun (x, acc) -> Char.chr (Word8.toInt x) :: acc) [] v)

  let str2vec l : Word8Vector.vector =
    Vector.fromList
      (map (fun x -> Word8.fromInt (Char.ord x)) (String.explode l))

  let fileText fname =
    let s = TextIO.openIn fname in
    let txt = TextIO.inputAll s in
    ignore (TextIO.closeIn s);
    txt

  let fileData fname =
    let s = TextIO.openIn fname in
    let data = TextIO.inputAll s in
    ignore (TextIO.closeIn s);
    data

  exception Eof = Eof
  exception Quit = Quit

  let send _conn _str = ()

  open! struct
    module SS = Substring
  end

  let parseCmd s =
    let c, a = SS.position " " (Substring.full s) in
    (SS.string c, SS.string (SS.dropl Char.isSpace a))

  let quote string = ("`" ^ string) ^ "'"
  let examplesDir : string option ref = ref None
  let setExamplesDir s = examplesDir := Some s

  (* exception Error for server errors *)
  exception Error = Error

  let error msg = raise (Error msg)

  let serveExample e =
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
          Stelf.make "sources.cfg"
        end
      with e -> raise (Error (("Exception " ^ exnName e) ^ " raised."))
    else raise (Error ("Unknown example " ^ quote e))
    end

  (* Natural numbers *)
  let getNat = function
    | t :: [] -> (
        match Int.fromString t with
        | Some n when n >= 0 -> n
        | _ -> error (quote t ^ " is not a natural number"))

  (* Example specifiers *)
  let getExample = function
    | t :: [] -> t
    | [] -> error "Missing example"
    | ts -> error "Extraneous arguments"

  (* Setting Stelf parameters *)
  let setParm = function
    | "chatter" :: ts -> Stelf.chatter := getNat ts
    | t :: ts -> error ("Unknown parameter " ^ quote t)
    | [] -> error "Missing parameter"

  let exec' arg__3 arg__4 =
    begin match (arg__3, arg__4) with
    | conn, ("quit", args) -> begin
        Display.debug (Display.string "goodbye.\n");
        raise Quit
      end
    | conn, ("set", args) -> begin
        setParm (String.tokens Char.isSpace args);
        Stelf.Ok
      end
    | conn, ("readDecl", args) -> Stelf.loadString args
    | conn, ("decl", args) -> Stelf.decl args
    | conn, ("example", args) ->
        serveExample (getExample (String.tokens Char.isSpace args))
    | conn, (t, args) -> raise (Error ("Unrecognized command " ^ quote t))
    end

  let exec conn str =
    begin match
      try exec' conn (parseCmd str)
      with Error s ->
        begin
          Display.debug (Display.string (("Server Error: " ^ s) ^ "\n"));
          Stelf.Abort
        end
    with
    | Stelf.Ok -> Display.debug (Display.string "%%% OK %%%\n")
    | Stelf.Abort -> Display.debug (Display.string "%%% ABORT %%%\n")
    end

  let stripcr s =
    Substring.string
      (Substring.dropr (function x -> x = 'r') (Substring.full s))

  let noopProto () =
    {
      init = (fun () -> ());
      reset = (fun () -> ());
      recv = (fun (_ : server) (_ : string) -> ());
      send = (fun (_ : server) (_ : string) -> ());
      done_ = (fun () -> ());
    }

  let flashProto () = noopProto ()
  let humanProto () = noopProto ()
  let httpProto _dir = noopProto ()

  let protoServer (proto : protocol) portNum =
    raise
      (Error
         "NetServer unavailable: Socket support is not implemented in this \
          OCaml port")

  let flashServer port = protoServer (flashProto ()) port
  let humanServer port = protoServer (humanProto ()) port
  let httpServer port dir = protoServer (httpProto dir) port
end
