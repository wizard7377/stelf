open! Basis;;
(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 *
 * MLton is released under the GNU General Public License (GPL).
 * Please see the file MLton-LICENSE for license information.
 *);;
module Layout : LAYOUT =
  struct
    (*    structure Out = Outstream0   *);;
    let detailed = ref false;;
    let rec switch { detailed = d; normal = n} x = begin
      if ! detailed then d x else n x end;;
    type t = | T of { length: int ; tree: tree } 
    and tree =
      | Empty 
      | String of string 
      | Sequence of t list 
      | Align of { force: bool ; rows: t list } 
      | Indent of t * int ;;
    type nonrec layout = t;;
    let rec length (T { length}) = length;;
    let empty = (T { length = 0; tree = Empty} );;
    let rec isEmpty = function 
                               | T { length = 0} -> true
                               | _ -> false;;
    let rec str s =
      begin
      match s
      with 
           | "" -> empty
           | _ -> (T { length = String.size s; tree = (String s)} )
      end;;
    let rec fold (l, b, f) = foldl f b l;;
    let rec seq ts =
      let len = fold (ts, 0, function 
                                      | (t, n) -> n + (length t))
        in begin
           match len
           with 
                | 0 -> empty
                | _ -> (T { length = len; tree = (Sequence ts)} )
           end;;
    (* XXX mayalign should do 'partial spill', so that a long list of
       short elements displays as
       [1, 2, 3
        4, 5, 6]
       
       instead of
       
       [1,
        2,
        3,
        4,
        5,
        6] *);;
    open!
      struct
        let rec make force ts =
          let rec loop ts =
            begin
            match ts
            with 
                 | [] -> (ts, 0)
                 | (t :: ts)
                     -> let (ts, n) = loop ts
                          in begin
                             match length t
                             with 
                                  | 0 -> (ts, n)
                                  | n' -> ((t :: ts), (n + n') + 1)
                             end
            end
            in let (ts, len) = loop ts
                 in begin
                    match len
                    with 
                         | 0 -> empty
                         | _
                             -> (T
                                 {
                                 length = len - 1;
                                 tree = (Align { force; rows = ts} )}
                                 )
                    end;;
        end;;
    let align = make true;;
    let mayAlign = make false;;
    let rec indent (t, n) = (T { length = length t; tree = (Indent (t, n))} );;
    let tabSize : int = 8;;
    let rec k_ x _ = x;;
    let rec blanks ((n : int)) =
      (concat
       [CharVector.tabulate (div n tabSize, k_ 't');
        CharVector.tabulate (n mod tabSize, k_ ' ')] : string);;
    (*
    fun outputTree (t, out) =
        let val print = Out.outputc out
            fun loop (T {tree, length}) =
                (print ""(length ""
                 ; print (Int.toString length)
                 ; print "")""
                 ; (case tree of
                        Empty => print ""Empty""
                      | String s => (print ""(String ""; print s; print "")"")
                      | Sequence ts => loops (""Sequence"", ts)
                      | Align {force, rows} => loops (""Align"", rows)
                      | Indent (t, n) => (print ""(Indent ""
                                          ; print (Int.toString n)
                                          ; print "" ""
                                          ; loop t
                                          ; print "")"")))
            and loops (s, ts) = (print ""(""
                                 ; print s
                                 ; app (fn t => (print "" "" ; loop t)) ts
                                 ; print "")"")
        in loop t
        end
*);;
    (* doesn't include newlines. new version below - tom *);;
    (*
    fun tostring t =
        let
            fun loop (T {tree, ...}, accum) =
                case tree of
                    Empty => accum
                  | String s => s :: accum
                  | Sequence ts => fold (ts, accum, loop)
                  | Align {rows, ...} =>
                        (case rows of
                             [] => accum
                           | t :: ts =>
                                 fold (ts, loop (t, accum), fn (t, ac) =>
                                       loop (t, "" "" :: ac)))
                  | Indent (t, _) => loop (t, accum)
        in
            String.concat (rev (loop (t, [])))
        end
*);;
    let rec layout_print
      { tree = (tree : t); print = (print : string -> unit);
       lineWidth = (lineWidth : int)}
      =
      let rec newline () = print "\n"
        in let rec outputCompact (t, { at; printAt}) =
             let rec loop (T { tree}) =
               begin
               match tree
               with 
                    | Empty -> ()
                    | String s -> print s
                    | Sequence ts -> (App_ (loop, ts))
                    | Indent (t, _) -> loop t
                    | Align { rows}
                        -> begin
                           match rows
                           with 
                                | [] -> ()
                                | (t :: ts)
                                    -> begin
                                         loop t;
                                         (App_
                                          (function 
                                                    | t
                                                        -> begin
                                                             print " ";loop t
                                                             end,
                                           ts))
                                         
                                         end
                           end
               end
               in let at = at + (length t)
                    in begin
                         loop t;{ at; printAt = at} 
                         end
             in let rec loop
                  ((T { length; tree} as t), ({ at; printAt} as state)) =
                  let rec prePrint () = begin
                    if at >= printAt then () else
                    print (blanks (printAt - at)) end (* can't back up *)
                    in begin
                       match tree
                       with 
                            | Empty -> state
                            | Indent (t, n)
                                -> loop (t, { at; printAt = printAt + n} )
                            | Sequence ts -> fold (ts, state, loop)
                            | String s
                                -> begin
                                     prePrint ();
                                     begin
                                       print s;
                                       let at = printAt + length
                                         in { at; printAt = at} 
                                       
                                       end
                                     
                                     end
                            | Align { force; rows} -> begin
                                if
                                (not force) &&
                                  ((printAt + length) <= lineWidth)
                                then
                                begin
                                  prePrint ();outputCompact (t, state)
                                  end
                                else
                                begin
                                match rows
                                with 
                                     | [] -> state
                                     | (t :: ts)
                                         -> fold
                                            (ts, loop (t, state),
                                             function 
                                                      | (t, _)
                                                          -> begin
                                                               newline ();
                                                               loop
                                                               (t,
                                                                {
                                                                at = 0;
                                                                printAt}
                                                                )
                                                               
                                                               end)
                                end end
                       end
                    (*Out.print (concat [""at "", Int.toString at,
                * ""  printAt "", Int.toString printAt,
                * ""\n""]);
                *)(*outputTree (t, Out.error)*)
                  in begin
                       loop (tree, { at = 0; printAt = 0} );()
                       end
                  (*val _ = outputTree (t, out)*);;
    let defaultWidth : int = 80;;
    let rec tostringex wid l =
      let acc = (ref [] : string list ref)
        in let rec pr s = acc := ((s :: ! acc))
             in begin
                  layout_print { tree = l; lineWidth = wid; print = pr} ;
                  String.concat (rev (! acc))
                  end;;
    let tostring = tostringex defaultWidth;;
    (*
    fun outputWidth (t, width, out) =
    layout_print {tree = t,
               lineWidth = width,
               print = Out.outputc out}
*);;
    (*        fun output (t, out) = outputWidth (t, defaultWidth, out) *);;
    let print =
      function 
               | (t, p)
                   -> layout_print
                      { tree = t; lineWidth = defaultWidth; print = p} ;;
    (*
    fun outputl (t, out) = (output (t, out); Out.newline out)
*);;
    (*     fun makeOutput layoutX (x, out) = output (layoutX x, out)
 *);;
    let rec ignore _ = empty;;
    let rec separate (ts, s) =
      begin
      match ts
      with 
           | [] -> []
           | (t :: ts)
               -> (t
                   :: let s = str s
                        in let rec loop =
                             function 
                                      | [] -> []
                                      | (t :: ts) -> (s :: t :: loop ts)
                             in loop ts)
      end;;
    let rec separateLeft (ts, s) =
      begin
      match ts
      with 
           | [] -> []
           | (t :: []) -> ts
           | (t :: ts) -> (t :: map (function 
                                              | t -> seq [str s; t]) ts)
      end;;
    let rec separateRight (ts, s) =
      rev
      (let ts = rev ts
         in begin
            match ts
            with 
                 | [] -> []
                 | (t :: []) -> ts
                 | (t :: ts)
                     -> (t :: map (function 
                                            | t -> seq [t; str s]) ts)
            end);;
    let rec alignPrefix (ts, prefix) =
      begin
      match ts
      with 
           | [] -> empty
           | (t :: ts)
               -> mayAlign
                  [t;
                   indent
                   (mayAlign (map (function 
                                            | t -> seq [str prefix; t]) ts),
                    - (String.size prefix))]
      end;;
    open!
      struct
        let rec sequence (start, finish, sep) ts =
          seq [str start; mayAlign (separateRight (ts, sep)); str finish];;
        end;;
    let list = sequence ("[", "]", ",");;
    let rec listex start finish sep = sequence (start, finish, sep);;
    let schemeList = sequence ("(", ")", " ");;
    let tuple = sequence ("(", ")", ",");;
    let rec record fts =
      sequence
      ("{", "}", ",")
      (map (function 
                     | (f, t) -> seq [str (f ^ " = "); t]) fts);;
    let rec recordex sep fts =
      sequence
      ("{", "}", ",")
      (map (function 
                     | (f, t) -> seq [str (((f ^ " ") ^ sep) ^ " "); t]) fts);;
    let rec vector v = tuple (Vector.foldr ( :: ) [] v);;
    let rec array x = list (Array.foldr ( :: ) [] x);;
    let rec namedRecord (name, fields) =
      seq [str name; str " "; record fields];;
    let rec paren t = seq [str "("; t; str ")"];;
    let rec tuple2 (l1, l2) (x1, x2) = tuple [l1 x1; l2 x2];;
    let rec tuple3 (l1, l2, l3) (x1, x2, x3) = tuple [l1 x1; l2 x2; l3 x3];;
    let rec tuple4 (l1, l2, l3, l4) (x1, x2, x3, x4) =
      tuple [l1 x1; l2 x2; l3 x3; l4 x4];;
    let rec tuple5 (l1, l2, l3, l4, l5) (x1, x2, x3, x4, x5) =
      tuple [l1 x1; l2 x2; l3 x3; l4 x4; l5 x5];;
    let indent = function 
                          | x -> function 
                                          | y -> indent (y, x);;
    end;;