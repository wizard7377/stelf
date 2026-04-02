(* # 1 "src/netserver/Netserver_.sig.ml" *)

(* # 1 "src/netserver/Netserver_.fun.ml" *)

(* # 1 "src/netserver/Netserver_.sml.ml" *)
open! Basis
include Netserver_intf
(* filesystem directory where stelf examples are kept *)
(* signature SERVER *)
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

  let rec vec2str v =
    String.implode
      (Vector.foldr (fun (x, acc) -> Char.chr (Word8.toInt x) :: acc) [] v)

  let rec str2vec l : Word8Vector.vector =
    Vector.fromList
      (map (fun x -> Word8.fromInt (Char.ord x)) (String.explode l))

  let rec fileText fname =
    let s = TextIO.openIn fname in
    let txt = TextIO.inputAll s in
    let _ = TextIO.closeIn s in
    txt

  let rec fileData fname =
    let s = TextIO.openIn fname in
    let data = TextIO.inputAll s in
    let _ = TextIO.closeIn s in
    data

  exception Eof
  exception Quit

  let rec send _conn _str = ()

  open! struct
    module SS = Substring
  end

  let rec parseCmd s =
    let c, a = SS.position " " (Substring.full s) in
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
          Stelf.make "sources.cfg"
        end
      with e -> raise (Error (("Exception " ^ exnName e) ^ " raised."))
    else raise (Error ("Unknown example " ^ quote e))
    end

  (* Natural numbers *)
  let rec getNat = function
    | t :: [] -> (
        match Int.fromString t with
        | Some n when n >= 0 -> n
        | _ -> error (quote t ^ " is not a natural number"))

  (* Example specifiers *)
  let rec getExample = function
    | t :: [] -> t
    | [] -> error "Missing example"
    | ts -> error "Extraneous arguments"

  (* Setting Stelf parameters *)
  let rec setParm = function
    | "chatter" :: ts -> Stelf.chatter := getNat ts
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
        Stelf.Ok
      end
    | conn, ("readDecl", args) -> Stelf.loadString args
    | conn, ("decl", args) -> Stelf.decl args
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
          Stelf.Abort
        end
    with
    | Stelf.Ok -> Msg.message "%%% OK %%%\n"
    | Stelf.Abort -> Msg.message "%%% ABORT %%%\n"
    end

  let rec stripcr s =
    Substring.string
      (Substring.dropr (function x -> x = 'r') (Substring.full s))

  let rec noopProto () =
    {
      init = (fun () -> ());
      reset = (fun () -> ());
      recv = (fun (_ : server) (_ : string) -> ());
      send = (fun (_ : server) (_ : string) -> ());
      done_ = (fun () -> ());
    }

  let rec flashProto () = noopProto ()
  let rec humanProto () = noopProto ()
  let rec httpProto _dir = noopProto ()

  let rec protoServer (proto : protocol) portNum =
    raise
      (Error
         "NetServer unavailable: Socket support is not implemented in this \
          OCaml port")

  let rec flashServer port = protoServer (flashProto ()) port
  let rec humanServer port = protoServer (humanProto ()) port
  let rec httpServer port dir = protoServer (httpProto dir) port
end
