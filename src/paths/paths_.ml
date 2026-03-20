(* # 1 "src/paths/paths_.sig.ml" *)
open! Basis

(* Paths, Occurrences, and Error Locations *)
(** Author: Frank Pfenning *)
module type PATHS = sig
  type region = Reg of int * int [@@deriving show]


  (** r ::= (i,j) is interval [i,j) *)
  type location = Loc of string * region

  (* loc ::= (filename, region) *)
  (** line numbering, used when printing regions *)
  type nonrec linesInfo

  (** mapping from character positions to lines in a file *)
  val resetLines : unit -> unit

  (** reset line numbering *)
  val newLine : int -> unit

  (** new line starts at character i *)
  val getLinesInfo : unit -> linesInfo

  (** get lines info for current file *)
  val join : region * region -> region

  (** join(r1,r2) = smallest region enclosing r1 and r2 *)
  val toString : region -> string

  (** line1.col1-line2.col2, parsable by Emacs *)
  val wrap : region * string -> string

  (** add region to error message, parsable by Emacs *)
  val wrapLoc : location * string -> string

  (** add location to error message, also parsable *)
  val wrapLoc' : location * linesInfo option * string -> string

  (* add location to error message in line.col format *)
  (* Paths, occurrences and occurrence trees only work well for normal forms *)
  (* In the general case, regions only approximate true source location *)
  (** Follow path through a term to obtain subterm *)
  type path =
    | Label of path
    | Body of path
    | Head
    | Arg of int * path
    | Here

  (* [x:#] U or {x:#} V *)
  (* [x:V] # or {x:V} # *)
  (* # @ S, term in normal form *)
  (* H @ S1; ...; #; ...; Sn; Nil *)
  (* #, covers Uni, EVar, Redex(?) *)
  (**
     Construct an occurrence when traversing a term.
     The resulting occurrence can be translated to a region
     via an occurrence tree stored with the term.

     An occurrence is a path in reverse order.
  *)
  type nonrec occ

  val top : occ
  val label : occ -> occ
  val body : occ -> occ
  val head : occ -> occ
  val arg : int * occ -> occ

  (**
     An occurrence tree is a data structure mapping occurrences in a term
     to regions in an input stream.  Occurrence trees are constructed during parsing.
  *)
  type nonrec occExp
  and occSpine

  (* occurrence tree for u expressions *)
  (** occurrence tree for s spines *)
  val leaf : region -> occExp

  (** could be _ or identifier *)
  val bind : region * occExp option * occExp -> occExp
  val root : region * occExp * int * int * occSpine -> occExp
  val app : occExp * occSpine -> occSpine
  val nils : occSpine

  type nonrec occConDec

  (** occurrence tree for constant declarations *)
  val dec : int * occExp -> occConDec

  (** (#implicit, v) in c : V *)
  val def : int * occExp * occExp option -> occConDec

  (** (#implicit, u, v) in c : V = U *)
  val toRegion : occExp -> region
  val toRegionSpine : occSpine * region -> region
  val posToPath : occExp -> int -> path
  val occToRegionExp : occExp -> occ -> region
  val occToRegionDec : occConDec -> occ -> region

  (** into v for c : V *)
  val occToRegionDef1 : occConDec -> occ -> region

  (** into u for c : V = U *)
  val occToRegionDef2 : occConDec -> occ -> region

  (** into v for c : V = U *)
  val occToRegionClause : occConDec -> occ -> region
end
(* into v for c : V ... *)
(* signature PATHS *)

(* # 1 "src/paths/paths_.fun.ml" *)
open! Basis;;
(* Paths, Occurrences, and Error Locations *);;
(* Author: Frank Pfenning *);;
module MakePaths() : PATHS =
  struct
    type pos = int [@@deriving show];;
    (* characters, starting at 0 *);;
    type region = | Reg of pos * pos [@@deriving show] ;;
    (* r ::= (i,j) is interval [i,j) *);;
    type location = | Loc of string * region [@@deriving show] ;;
    (* loc ::= (filename, region) *);;
    type nonrec linesInfo = pos list;;
    let rec posToLineCol' (linesInfo, i) =
      let rec ptlc =
        function 
                 | (j :: js) -> begin
                     if i >= j then (List.length js, i - j) else ptlc js end
                 | [] -> (0, i)(* nil means first ""line"" was not terminated by <newline> *)(* first line should start at 0 *)
        in ptlc linesInfo;;
    open! struct
            let linePosList = (ref [] : pos list ref);;
            end;;
    (* !linePosList is a list of starting character positions for each input line *);;
    (* used to convert character positions into line.column format *);;
    (* maintained with state *);;
    let rec resetLines () = linePosList := [];;
    let rec newLine i = linePosList := ((i :: ! linePosList));;
    let rec getLinesInfo () = ! linePosList;;
    (* posToLineCol (i) = (line,column) for character position i *);;
    let rec posToLineCol i = posToLineCol' (! linePosList, i);;
    (* join (r1, r2) = r
     where r is the  smallest region containing both r1 and r2
  *);;
    let rec join (Reg (i1, j1), Reg (i2, j2)) =
      (Reg (Int.min (i1, i2), Int.max (j1, j2)));;
    (* The right endpoint of the interval counts IN RANGE *);;
    let rec posInRegion (k, Reg (i, j)) = (i <= k) && (k <= j);;
    let rec lineColToString (line, col) =
      ((Int.toString (line + 1)) ^ ".") ^ (Int.toString (col + 1));;
    (* toString r = ""line1.col1-line2.col2"", a format parsable by Emacs *);;
    let rec toString (Reg (i, j)) =
      ((lineColToString (posToLineCol i)) ^ "-") ^
        (lineColToString (posToLineCol j));;
    (* wrap (r, msg) = msg' which contains region *);;
    let rec wrap (r, msg) = ((toString r) ^ " Error: \n") ^ msg;;
    (* wrapLoc ((loc, r), msg) = msg' which contains region and filename
     This should be used for locations retrieved from origins, where
     the region is given in character positions, rather than lines and columns
  *);;
    let rec wrapLoc0 (Loc (filename, Reg (i, j)), msg) =
      ((((((filename ^ ":") ^ (Int.toString (i + 1))) ^ "-") ^
           (Int.toString (j + 1)))
          ^ " ")
         ^ "Error: \n")
        ^ msg;;
    (* wrapLoc' ((loc, r), linesInfo, msg) = msg'
     like wrapLoc, but converts character positions to line.col format based
     on linesInfo, if possible
  *);;
    let rec wrapLoc' =
      function 
               | (Loc (filename, Reg (i, j)), Some linesInfo, msg)
                   -> let lcfrom = posToLineCol' (linesInfo, i)
                        in let lcto = posToLineCol' (linesInfo, j)
                             in let regString =
                                  ((lineColToString lcfrom) ^ "-") ^
                                    (lineColToString lcto)
                                  in ((((filename ^ ":") ^ regString) ^ " ")
                                        ^ "Error: \n")
                                       ^ msg
               | (loc, None, msg) -> wrapLoc0 (loc, msg);;
    let rec wrapLoc (loc, msg) =
      wrapLoc' (loc, (Some (getLinesInfo ())), msg);;
    (* Paths, occurrences and occurrence trees only work well for normal forms *);;
    (* In the general case, regions only approximate true source location *);;
    (* Follow path through a term to obtain subterm *);;
    type path =
      | Label of path 
      | Body of path 
      | Head 
      | Arg of int * path 
      | Here ;;
    (* [x:#] U or {x:#} V *);;
    (* [x:V] # or {x:V} # *);;
    (* # @ S, term in normal form *);;
    (* C @ S1; ...; #; ...; Sn; Nil *);;
    (* #, covers Uni, EVar, Redex(?) *);;
    (* Occurrences: paths in reverse order *);;
    (* could also be: type occ = path -> path *);;
    type occ =
      | Top_ 
      | Label_ of occ 
      | Body_ of occ 
      | Head_ of occ 
      | Arg_ of int * occ ;;
    (* Occurrence trees for expressions and spines *);;
    (* Maps occurrences to regions *);;
    (* Simple-minded implementation *);;
    (* A region in an intermediate node encloses the whole expression *);;
    type occExp =
      | Leaf_ of region 
      | Bind_ of region * occExp option * occExp 
      | Root_ of region * occExp * int * int * occSpine 
    and occSpine = | App_ of occExp * occSpine 
                   | Nils_ ;;
    (* occurrences in expressions *);;
    (* _ or identifier *);;
    (* [x:vOpt] u or {x:vOpt} v' *);;
    (* h @ s, # of implicit arguments, # of arguments actually input (as opposed to generated by eta-expansion) *);;
    (* occurrences in spines *);;
    (* u;s *);;
    (* nil *);;
    (* occToPath (occ, p) = p'(p) and occ corresponds to p' *);;
    let rec occToPath =
      function 
               | (Top_, path) -> path
               | (Label_ occ, path) -> occToPath (occ, (Label path))
               | (Body_ occ, path) -> occToPath (occ, (Body path))
               | (Head_ occ, path) -> occToPath (occ, Head)
               | (Arg_ (n, occ), path) -> occToPath (occ, (Arg (n, path)))(* path = Here by invariant *);;
    type occConDec =
      | Dec_ of int * occExp 
      | Def_ of int * occExp * occExp option ;;
    (* occurrence tree for constant declarations *);;
    (* (#implicit, v) in c : V *);;
    (* (#implicit, u, v) in c : V = U *);;
    (* val posToPath : occExp -> pos -> Path *);;
    (* posToPath (u, k) = p
     where p is the path to the innermost expression in u enclosing position i.

     This includes the position immediately at the end of a region [i,j).
     For example, in ""f (g x) y"",
     0,1 => ""f""
     2   => ""(g x)""
     3,4 => ""g""
     5,6 => ""x""
     8,9 => ""y""
  *);;
    let rec posToPath u k =
      let rec inside =
        function 
                 | Leaf_ r -> posInRegion (k, r)
                 | Bind_ (r, _, _) -> posInRegion (k, r)
                 | Root_ (r, _, _, _, _) -> posInRegion (k, r)
        in let rec toPath =
             function 
                      | Leaf_ (Reg (i, j)) -> Here
                      | Bind_ (Reg (i, j), None, u) -> begin
                          if inside u then (Body (toPath u)) else Here end
                      | Bind_ (Reg (i, j), Some u1, u2) -> begin
                          if inside u1 then (Label (toPath u1)) else begin
                          if inside u2 then (Body (toPath u2)) else Here end
                          end
                      | Root_ (Reg (i, j), h, imp, actual, s) -> begin
                          if inside h then Head else
                          begin
                          match toPathSpine (s, 1)
                          with 
                               | None -> Here
                               | Some (n, path) -> (Arg (n + imp, path))
                          end end(* check? mark? *)
           and toPathSpine =
             function 
                      | (Nils_, n) -> None
                      | (App_ (u, s), n) -> begin
                          if inside u then (Some (n, toPath u)) else
                          toPathSpine (s, n + 1) end
             in toPath u
             (* local functions refer to k but not u *)(* in some situations, whitespace after subexpressions *)(* might give a larger term than anticipated *);;
    (* toRegion (u) = r, the region associated with the whole occurrence tree u *);;
    let rec toRegion =
      function 
               | Leaf_ r -> r
               | Bind_ (r, _, _) -> r
               | Root_ (r, _, _, _, _) -> r;;
    (* toRegionSpine (s, r) = r', the join of all regions in s and r *);;
    let rec toRegionSpine =
      function 
               | (Nils_, r) -> r
               | (App_ (u, s), r) -> join (toRegion u, toRegionSpine (s, r));;
    (* order? *);;
    (* pathToRegion (u, p) = r,
     where r is the region identified by path p in occurrence tree u
  *);;
    let rec pathToRegion =
      function 
               | (u, Here) -> toRegion u
               | (Bind_ (r, None, u), Label path) -> r
               | (Bind_ (r, Some u1, u2), Label path)
                   -> pathToRegion (u1, path)
               | (Bind_ (r, _, u), Body path) -> pathToRegion (u, path)
               | (Root_ (r, _, _, _, _), Label path) -> r
               | ((Root_ _ as u), Body path) -> pathToRegion (u, path)
               | (Root_ (r, h, imp, actual, s), Head) -> toRegion h
               | (Root_ (r, h, imp, actual, s), Arg (n, path)) -> begin
                   if n <= imp then toRegion h else begin
                   if (n - imp) > actual then r else
                   pathToRegionSpine (s, n - imp, path) end
                   (* addressing argument created by eta expansion
                approximate by the whole root *)
                   end
                   (* addressing implicit argument returns region of head *)
               | (Leaf_ r, _) -> r(* bypassing binder introduced as the result of eta expansion *)(* addressing binder introduced as the result of eta expansion
           approximate as the eta-expanded root *)(* addressing implicit type label returns region of binder and its scope *)
    and pathToRegionSpine =
      function 
               | (App_ (u, s), 1, path) -> pathToRegion (u, path)
               | (App_ (u, s), n, path) -> pathToRegionSpine (s, n - 1, path);;
    (* possible if leaf was _ (underscore) *);;
    (* other combinations should be impossible *);;
    (* anything else should be impossible *);;
    (* occToRegionExp u occ = r,
     where r is the closest region including occ in occurrence tree u
  *);;
    let rec occToRegionExp u occ = pathToRegion (u, occToPath (occ, Here));;
    let rec skipImplicit =
      function 
               | (0, path) -> path
               | (n, Body path) -> skipImplicit (n - 1, path)
               | (n, Label path) -> Here
               | (n, Here) -> Here(* addressing body including implicit arguments: approximate by body *)(* implicit argument: approximate as best possible *);;
    (* anything else should be impossible *);;
    (* occToRegionDec d occ = r
     where r is the closest region in v including occ for declaration c : V
  *);;
    let rec occToRegionDec (Dec_ (n, v)) occ =
      pathToRegion (v, skipImplicit (n, occToPath (occ, Here)));;
    (* occToRegionDef1 d occ = r
     where r is the closest region in u including occ for declaration c : V = U
  *);;
    let rec occToRegionDef1 (Def_ (n, u, vOpt)) occ =
      pathToRegion (u, skipImplicit (n, occToPath (occ, Here)));;
    (* occToRegionDef2 d occ = r
     where r is the closest region in V including occ for declaration c : V = U
  *);;
    let rec occToRegionDef2 arg__0 arg__1 =
      begin
      match (arg__0, arg__1)
      with 
           | (Def_ (n, u, Some v), occ)
               -> pathToRegion (v, skipImplicit (n, occToPath (occ, Here)))
           | (Def_ (n, u, None), occ) -> pathToRegion (u, Here)
      end;;
    (* occToRegionClause d occ = r
     where r is the closest region in V including occ for declaration
     c : V or c : V = U.
  *);;
    let rec occToRegionClause arg__2 arg__3 =
      begin
      match (arg__2, arg__3)
      with 
           | ((Dec_ _ as d), occ) -> occToRegionDec d occ
           | ((Def_ _ as d), occ) -> occToRegionDef2 d occ
      end;;
    let top = Top_;;
    let label occ = Label_ occ;;
    let body occ = Body_ occ;;
    let head occ = Head_ occ;;
    let arg (n, occ) = Arg_ (n, occ);;
    let leaf r = Leaf_ r;;
    let bind (r, v, u) = Bind_ (r, v, u);;
    let root (r, h, i, a, s) = Root_ (r, h, i, a, s);;
    let app (u, s) = App_ (u, s);;
    let nils = Nils_;;
    let dec (n, v) = Dec_ (n, v);;
    let def (n, u, v) = Def_ (n, u, v);;
    end;;
(* functor Paths *);;
module Paths = (MakePaths)(struct
                         
                         end);;
(* # 1 "src/paths/paths_.sml.ml" *)
open! Basis
(* Now in paths.fun *)
(*
structure Paths = Paths ();
*)
(* Commented out to break dependency cycle with origins
module Origins = (Origins)(struct
                             module Global = Global;;
                             module Table = StringHashTable;;
                             end);;
*)
(*! structure IntSyn' = IntSyn !*)
(*! structure Paths' = Paths !*)
