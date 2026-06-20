(** Formatting options generally
    @author Asher Frost *)

module type FORM = FORM.FORM

module Form : FORM = struct
  type box = HBox | VBox | HVBox

  type t =
    | Space of int
    | NonbreakingSpace of int
    | Cut of int
    | Exact of string
    | Empty
    | Concat of t list
    | Fg of Notty.A.color * t
    | Bg of Notty.A.color * t
    | Bold of t
    | Italic of t
    | Underline of t
    | Marked of t * t  (** Ie, with carats *)
    | Boxed of box * t list  (** Box with style *)
    | Custom of unit Fmt.t

  type style = t -> t
  type 'a scribe = 'a -> t

  let ( +++ ) x y = Concat [ x; y ]
  let empty = Empty

  let concat ?(sep = empty) xs =
    List.fold_left (fun acc x -> acc +++ sep +++ x) empty xs

  let string s = Exact s
  let int n = string (string_of_int n)
  let char c = string (String.make 1 c)
  let bool b = string (string_of_bool b)
  let cut () = string "\n"
  let shown f x = string (f x)
  let shown_exact f x = string (f x)
  let shown_many ?(sep = empty) f xs = concat ~sep (List.map (shown f) xs)
  let inside (open_, close) x = open_ +++ x +++ close
  let nl ?(n = 1) () = string (String.make n '\n')
  let each ?(sep = empty) f xs = concat ~sep (List.map f xs)
  let space ?(n = 1) () = Space n
  let non_breaking_space ?(n = 1) () = NonbreakingSpace n
  let hbox xs = Boxed (HBox, xs)
  let vbox xs = Boxed (VBox, xs)
  let hvbox xs = Boxed (HVBox, xs)

  let optional ?def f = function
    | None -> ( match def with Some d -> d | None -> empty)
    | Some x -> f x

  let ( ++ ) x y = x +++ space () +++ y

  module Style = struct
    let bold x = Bold x
    let italic x = Italic x
    let underline x = Underline x

    module Fore = struct
      let black x = Fg (Notty.A.black, x)
      let red x = Fg (Notty.A.red, x)
      let green x = Fg (Notty.A.green, x)
      let yellow x = Fg (Notty.A.yellow, x)
      let blue x = Fg (Notty.A.blue, x)
      let magenta x = Fg (Notty.A.magenta, x)
      let cyan x = Fg (Notty.A.cyan, x)
      let white x = Fg (Notty.A.white, x)
      let orange x = Fg (Notty.A.rgb ~r:255 ~g:165 ~b:0, x)
      let rgb r g b x = Fg (Notty.A.rgb_888 ~r ~g ~b, x)
    end

    module Back = struct
      let black x = Bg (Notty.A.black, x)
      let red x = Bg (Notty.A.red, x)
      let green x = Bg (Notty.A.green, x)
      let yellow x = Bg (Notty.A.yellow, x)
      let blue x = Bg (Notty.A.blue, x)
      let magenta x = Bg (Notty.A.magenta, x)
      let cyan x = Bg (Notty.A.cyan, x)
      let white x = Bg (Notty.A.white, x)
      let orange x = Bg (Notty.A.rgb_888 ~r:255 ~g:165 ~b:0, x)
      let rgb r g b x = Bg (Notty.A.rgb_888 ~r ~g ~b, x)
    end
  end

  let style f x = f x
  let styles fs x = List.fold_left (fun acc f -> style f acc) x fs

  module Syntax = struct
    let syntax = Style.bold
  end

  let rec to_plain : t -> string = function
    | Space n | NonbreakingSpace n -> String.make n ' '
    | Cut n -> String.make n '\n'
    | Exact s -> s
    | Empty -> ""
    | Concat xs -> String.concat "" (List.map to_plain xs)
    | Fg (_, x) | Bg (_, x) | Bold x | Italic x | Underline x -> to_plain x
    | Marked (_carats, x) -> to_plain x
    | Boxed (box, xs) -> (
        match box with
        | HBox -> String.concat "" (List.map to_plain xs)
        | VBox -> String.concat "\n" (List.map to_plain xs)
        | HVBox -> String.concat " " (List.map to_plain xs))

  let rec go : Notty.attr -> t -> Notty.image = fun attr ->
    let attr' : Notty.attr -> Notty.attr = Notty.A.((++) attr) in
    Notty.(function
    | Space n -> I.string attr (String.make n ' ')
    | NonbreakingSpace n -> I.string attr (String.make n ' ')
    | Cut n ->
        let row = I.string attr "" in
        let rows = List.init n (fun _ -> row) in
        List.fold_left I.(<->) I.empty rows
    | Exact s ->
        (match String.split_on_char '\n' s with
         | [] -> I.empty
         | [line] -> I.string attr line
         | lines -> I.vcat (List.map (I.string attr) lines))
    | Empty -> I.empty
    | Concat xs -> I.(hcat (List.map (go attr) xs))
    | Fg (c, x) -> go (attr' (A.fg c)) x
    | Bg (c, x) -> go (attr' (A.bg c)) x
    | Bold x -> go (attr' @@ A.st A.bold) x
    | Italic x -> go (attr' @@ A.st A.italic) x
    | Underline x -> go (attr' @@ A.st A.underline) x
    | Marked (carats, x) ->
        let content_img = go attr x in
        let carats_img = go attr carats in
        I.(carats_img <-> content_img)
    | Boxed (box, xs) ->
        match box with
        | HBox -> List.fold_left I.(<|>) I.empty (List.map (go attr) xs)
        | VBox -> List.fold_left I.(<->) I.empty (List.map (go attr) xs)
        | HVBox -> List.fold_left I.(<|>) I.empty (List.map (go attr) xs))

    let show x = go Notty.A.empty x
  let markup x = show x
  let rec fmt ppf = function
    | Space n | NonbreakingSpace n ->
        Format.pp_print_string ppf (String.make n ' ')
    | Cut n ->
        for _ = 1 to n do Format.pp_force_newline ppf () done
    | Exact s -> Format.pp_print_string ppf s
    | Empty -> ()
    | Concat xs -> List.iter (fmt ppf) xs
    | Fg (_, x) | Bg (_, x) | Bold x | Italic x | Underline x -> fmt ppf x
    | Marked (_, x) -> fmt ppf x
    | Custom f -> f ppf ()
    | Boxed (box, xs) ->
        (match box with
         | HBox  -> Format.pp_open_hbox ppf ()
         | VBox  -> Format.pp_open_vbox ppf 0
         | HVBox -> Format.pp_open_hvbox ppf 0);
        List.iter (fmt ppf) xs;
        Format.pp_close_box ppf ()

  let header ~level:_ x = x
  let custom f = Custom f
end
   