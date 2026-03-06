open! Basis;;
(* Paths, Occurrences, and Error Locations *);;
(* Author: Frank Pfenning *);;
module type PATHS = sig
                    type region = | Reg of int * int 
                    (* r ::= (i,j) is interval [i,j) *)
                    type location = | Loc of string * region 
                    (* loc ::= (filename, region) *)
                    (* line numbering, used when printing regions *)
                    type nonrec linesInfo
                    (* mapping from character positions to lines in a file *)
                    val resetLines : unit -> unit
                    (* reset line numbering *)
                    val newLine : int -> unit
                    (* new line starts at character i *)
                    val getLinesInfo : unit -> linesInfo
                    (* get lines info for current file *)
                    val join : (region * region) -> region
                    (* join(r1,r2) = smallest region enclosing r1 and r2 *)
                    val toString : region -> string
                    (* line1.col1-line2.col2, parsable by Emacs *)
                    val wrap : (region * string) -> string
                    (* add region to error message, parsable by Emacs *)
                    val wrapLoc : (location * string) -> string
                    (* add location to error message, also parsable *)
                    val
                      wrapLoc' : (location * linesInfo option * string) ->
                                 string
                    (* add location to error message in line.col format *)
                    (* Paths, occurrences and occurrence trees only work well for normal forms *)
                    (* In the general case, regions only approximate true source location *)
                    (* Follow path through a term to obtain subterm *)
                    type path_ =
                      | Label of path_ 
                      | Body of path_ 
                      | Head 
                      | Arg of int * path_ 
                      | Here 
                    (* [x:#] U or {x:#} V *)
                    (* [x:V] # or {x:V} # *)
                    (* # @ S, term in normal form *)
                    (* H @ S1; ...; #; ...; Sn; Nil *)
                    (* #, covers Uni, EVar, Redex(?) *)
                    (*
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
                    val arg : (int * occ) -> occ
                    (*
     An occurrence tree is a data structure mapping occurrences in a term
     to regions in an input stream.  Occurrence trees are constructed during parsing.
  *)
                    type nonrec occExp
                    and occSpine
                    (* occurrence tree for u expressions *)
                    (* occurrence tree for s spines *)
                    val leaf : region -> occExp
                    (* could be _ or identifier *)
                    val bind : (region * occExp option * occExp) -> occExp
                    val
                      root : (region * occExp * int * int * occSpine) ->
                             occExp
                    val app : (occExp * occSpine) -> occSpine
                    val nils : occSpine
                    type nonrec occConDec
                    (* occurrence tree for constant declarations *)
                    val dec : (int * occExp) -> occConDec
                    (* (#implicit, v) in c : V *)
                    val def : (int * occExp * occExp option) -> occConDec
                    (* (#implicit, u, v) in c : V = U *)
                    val toRegion : occExp -> region
                    val toRegionSpine : (occSpine * region) -> region
                    val posToPath : occExp -> int -> path_
                    val occToRegionExp : occExp -> occ -> region
                    val occToRegionDec : occConDec -> occ -> region
                    (* into v for c : V *)
                    val occToRegionDef1 : occConDec -> occ -> region
                    (* into u for c : V = U *)
                    val occToRegionDef2 : occConDec -> occ -> region
                    (* into v for c : V = U *)
                    val occToRegionClause : occConDec -> occ -> region
                    end;;
(* into v for c : V ... *);;
(* signature PATHS *);;