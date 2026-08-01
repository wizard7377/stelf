open Base
(**
   The concrete syntax tree (CST) interface (in Twelf, it bore the name [ExtSyn]. 
   
   In both the original twelf and in STELF, the CST has two, distinct but related purposes.
   {ol
   {- To serve as the target for parsing. This is the primary purpose of this module, which outlines the abstract interface }
   {- To serve as the {e input} of elaboration (term reconstruction), for more on this, see {!module:Cst} and {!module:Recon} }.
   }

   We choose to implement these two purposes in the same way that Twelf did, albiet seperately (Twelf had this embeded in the elaboration).
   Thus, using only these, we should be able to {e create} any CST for any term that we may so desire.
   
   @author Asher Frost
   @see {!module:Cst} for the actual implementation of this interface.
*)

(** {2 CST} *)
module type CST = sig
  module Paths : Paths.PATHS.PATHS
  (** Module of paths and regions, which we allow to be shared *)

  type query
  (** Query payload. *)

  type define
  (** Define payload. *)

  type solve
  (** Solve payload. *)

  type strexp
  (** Structure expression. *)

  type inst
  (** Structure instantiation clause. *)

  type sigexp
  (** Signature expression. *)

  type sigdef
  (** Signature definition. *)

  type structDec
  (** Structure declaration. *)

  type structDef
  (** Structure definition. *)

  type mode
  (** Mode marker. *)

  type modeDec
  (** Mode declaration. *)

  type modeTerm
  (** Mode term. *)

  type modeSpine
  (** Mode spine. *)

  type term
  (** Term node. *)

  type conDec
  (** Top-level constant declaration node. *)

  type decl
  (** Binder declaration node. *)

  type fixity
  (** Fixity kind for %prec declarations. *)

  type block_item
  (** One item in a %block world declaration. *)

  type order [@@deriving show { with_path = false }, eq]
  (** Termination/totality order (Varg, Lex, Simul). *)

  type cmd [@@deriving show { with_path = false }, eq]
  (** Top-level command node. *)

  type loc
  (** Source location carried by CST nodes. *)

  type name = string
  (** Unqualified identifier. *)

  type namespace = string list
  (** Qualified namespace path. *)

  type symbol = namespace * name
  (** Qualified symbol as [(namespace, name)]. *)

  type qid_form =
    | Val
    | Abs
        (** Distinguishes [%val NAME] (shadow-aware lookup) from [%abs NAME]
            (toplevel-first lookup, falling back to shadow-aware). *)

  val pp_qid_form : Stdlib.Format.formatter -> qid_form -> unit
  val show_qid_form : qid_form -> string

  (** Tags for printer-internal term nodes: the parts of the internal syntax
      that have no STELF surface form, named so that resugaring can be total. A
      term containing an [Internal] node is deliberately unparseable. *)
  type internal_tag =
    | Kind_tag  (** [IntSyn.Uni Kind]: no surface syntax exists. *)
    | Subst_tag  (** Explicit substitution; children are its fronts. *)
    | Shift_tag of int  (** The [^n] tail of a substitution. *)
    | Undef_tag  (** An undefined substitution front. *)
    | Proj_tag of string  (** Block projection label, pre-rendered. *)
    | Cutoff_tag  (** [printDepth] was exceeded; prints [%%]. *)
    | Elided_tag  (** [printLength] was exceeded; prints [...]. *)
    | Opaque_tag of string  (** Verbatim token plus children; last resort. *)

  val pp_internal_tag : Stdlib.Format.formatter -> internal_tag -> unit
  val show_internal_tag : internal_tag -> string
  val equal_internal_tag : internal_tag -> internal_tag -> bool

  val equal_term : term -> term -> bool
  (** Structural equality on terms, {e including} source locations. Callers
      comparing terms from different sources normally want to erase locations
      first. *)

  val equal_decl : decl -> decl -> bool
  (** Structural equality on declarations, including source locations. *)

  val [@deprecated "Use View equivalent instead"] mk_loc : int -> int -> loc
  (** Create a location from start and end lexer positions. *)

  val [@deprecated "Use View equivalent instead"] loc_to_region :
    loc -> Paths.region
  (** Convert a source location to a Paths region. *)

  val [@deprecated "Use View equivalent instead"] ghost : loc
  (** Synthetic location used for generated nodes. *)

  (** {3 Term Syntax} *)
  module Term : sig
    type t = term

    val [@deprecated "Use View equivalent instead"] lowercase :
      ?fc:loc -> symbol -> term
    (** Lowercase identifier (does not start with [_]). *)

    val [@deprecated "Use View equivalent instead"] uppercase :
      ?fc:loc -> symbol -> term
    (** Uppercase identifier. *)

    val [@deprecated "Use View equivalent instead"] qualified :
      ?fc:loc -> ?form:qid_form -> symbol -> term
    (** Qualified identifier. *)

    val [@deprecated "Use View equivalent instead"] text :
      ?fc:loc -> string -> term
    (** Quoted text literal (currently not parsed from source). *)

    val [@deprecated "Use View equivalent instead"] exist_var :
      ?fc:loc -> string -> term
    (** Existential variable, usually written as [?x]. *)

    val [@deprecated "Use View equivalent instead"] free_var :
      ?fc:loc -> string -> term
    (** Free variable identifier. *)

    val [@deprecated "Use View equivalent instead"] pi :
      ?fc:loc -> decl list -> term -> term
    (** The pi type, which covers both kinds and types
        @param fc Optional source location for the node.
        @param decls
          List of bind declerations {!type:decl}, which introduces terms into
          the context
        @param body The body of the pi type *)

    val [@deprecated "Use View equivalent instead"] [@deprecated] lam :
      ?fc:loc -> decl list -> term -> term
    (** Lambda abstraction over a list of declarations
        @param fc Optional source location for the node.
        @param decls
          List of bind declerations {!type:decl}, which introduces terms into
          the context
        @param body The body of the lambda *)

    val [@deprecated "Use View equivalent instead"] app :
      ?fc:loc -> term -> term list -> term
    (** Application of a head term to arguments, which applies both to terms in
        normal form and not in normal form *)

    val [@deprecated "Use View equivalent instead"] has_type :
      ?fc:loc -> term -> term -> term
    (** Explicit type ascription. *)

    val [@deprecated "Use View equivalent instead"] omitted : ?fc:loc -> term
    (** Placeholder [_] for an omitted term. *)

    val [@deprecated "Use View equivalent instead"] typ :
      ?fc:loc -> unit -> term
    (** Note that while this term does not exist externally, internally, we
        translate [%sort] to use this, as to be similar to the original Twelf *)

    (** {4 Syntax Sugar} *)
    module Sugar : sig
      (** Function type constructor (not used directly). *)
      val [@deprecated "Use View equivalent instead"] arrow :
        ?fc:loc -> term -> term -> term
      (** This isn't used *)

      (* tm -> tm *)
      val [@deprecated "Use View equivalent instead"] backarrow :
        ?fc:loc -> term -> term -> term
      (** this isnt used *)
    end
  end

  (** Binder declaration constructors. *)
  module Decl : sig
    type t = decl

    val [@deprecated "Use View equivalent instead"] decl1 :
      ?fc:loc -> string option list -> term -> decl
    (** [decl1 names typ] creates a declaration that binds [names] with type
        [typ].

        The [names] list corresponds to grouped declarations such as
        [(x y z) T]. *)

    val [@deprecated "Use View equivalent instead"] decl0 :
      ?fc:loc -> string option list -> decl
    (** [decl0 names] is like {!decl1} but without an explicit type. *)
  end

  (** Top-level declaration constructors. *)
  module ConDec : sig
    type t = conDec

    val [@deprecated "Use View equivalent instead"] constant_decl :
      ?fc:loc -> decl -> t
    (** Lift a local declaration into a top-level [%term] declaration. *)

    val [@deprecated "Use View equivalent instead"] block_decl :
      ?fc:loc -> string -> decl list -> decl list -> t
    (** Block declaration.

        [%block B X Y] declares block [B] with declaration groups [X] and [Y].
    *)

    val [@deprecated "Use View equivalent instead"] block_def :
      ?fc:loc -> string -> symbol list -> t

    val [@deprecated "Use View equivalent instead"] constant_def :
      ?fc:loc -> string -> term -> term option -> t
  end

  (** Mode syntax constructors. *)
  module Mode : sig
    type mode
    type nonrec modeTerm = modeTerm

    val [@deprecated "Use View equivalent instead"] plus :
      ?fc:loc -> unit -> mode
    (** Positive mode marker. *)

    val [@deprecated "Use View equivalent instead"] star :
      ?fc:loc -> unit -> mode
    (** Star mode marker. *)

    val [@deprecated "Use View equivalent instead"] minus :
      ?fc:loc -> unit -> mode
    (** Negative mode marker. *)

    val [@deprecated "Use View equivalent instead"] minus1 :
      ?fc:loc -> unit -> mode
    (** Strict negative mode marker. *)

    type modedec = modeDec

    (** Short mode syntax. *)
    module Short : sig
      type nonrec modeTerm = modeTerm
      type nonrec modeSpine = modeSpine

      val [@deprecated "Use View equivalent instead"] mode_nil :
        ?fc:loc -> unit -> modeSpine
      (** Empty mode spine. *)

      val [@deprecated "Use View equivalent instead"] mode_app :
        ?fc:loc -> mode * string option -> modeSpine -> modeSpine
      (** Extend a mode spine with one argument mode. *)

      val [@deprecated "Use View equivalent instead"] mode_root :
        ?fc:loc -> symbol -> modeSpine -> modeTerm
      (** Build a short mode root from a symbol and spine. *)

      val [@deprecated "Use View equivalent instead"] to_modeDec :
        ?fc:loc -> modeTerm -> modeDec
      (** Convert a short mode term into a mode declaration. *)
    end

    (** Full mode syntax. *)
    module Full : sig
      val [@deprecated "Use View equivalent instead"] mode_root :
        ?fc:loc -> term -> modeTerm
      (** Root mode term from a regular term. *)

      val [@deprecated "Use View equivalent instead"] mode_pi :
        ?fc:loc -> mode -> decl -> modeTerm -> modeTerm
      (** Pi-mode binder. *)

      val [@deprecated "Use View equivalent instead"] to_modeDec :
        ?fc:loc -> modeTerm -> modeDec
      (** Convert a full mode term into a mode declaration. *)
    end
  end

  (** Module/signature syntax constructors. *)
  module Struct : sig
    type strexp

    val [@deprecated "Use View equivalent instead"] str_exp :
      ?fc:loc -> symbol -> strexp

    type inst

    val [@deprecated "Use View equivalent instead"] con_inst :
      ?fc:loc -> symbol * loc -> term -> inst

    val [@deprecated "Use View equivalent instead"] str_inst :
      ?fc:loc -> symbol * loc -> strexp -> inst

    type sigexp

    val [@deprecated "Use View equivalent instead"] thesig : ?fc:loc -> sigexp

    val [@deprecated "Use View equivalent instead"] sig_id :
      ?fc:loc -> string -> sigexp

    val [@deprecated "Use View equivalent instead"] where_sig :
      ?fc:loc -> sigexp -> inst list -> sigexp

    type sigdef

    val [@deprecated "Use View equivalent instead"] sig_def :
      ?fc:loc -> string option -> sigexp -> sigdef

    type structdec = structDec

    val [@deprecated "Use View equivalent instead"] struct_decl :
      ?fc:loc -> string option -> sigexp -> structdec

    val [@deprecated "Use View equivalent instead"] struct_def :
      ?fc:loc -> string option -> strexp -> structdec
  end

  module Query : sig
    type query

    val [@deprecated "Use View equivalent instead"] query :
      ?fc:loc -> string option -> term -> query
    (** Query declaration. *)

    type define
    (** Define declaration. *)

    val [@deprecated "Use View equivalent instead"] define :
      ?fc:loc -> string option -> term -> term option -> define
    (** Define declaration with optional right-hand side. *)

    type solve

    val [@deprecated "Use View equivalent instead"] solve :
      ?fc:loc -> string option -> term -> solve
    (** Solve declaration. *)
  end

  (** Fixity constructors. *)
  module Fixity : sig
    val [@deprecated "Use View equivalent instead"] left : fixity
    val [@deprecated "Use View equivalent instead"] right : fixity
    val [@deprecated "Use View equivalent instead"] prefix : fixity
    val [@deprecated "Use View equivalent instead"] postfix : fixity
    val [@deprecated "Use View equivalent instead"] middle : fixity
    val [@deprecated "Use View equivalent instead"] none : fixity
  end

  (** Block item constructors for %block declarations. *)
  module BlockItem : sig
    val [@deprecated "Use View equivalent instead"] some : decl -> block_item
    (** [{decl}] — existentially bound hypothesis. *)

    val [@deprecated "Use View equivalent instead"] pi : decl -> block_item
    (** [[decl]] — universally bound hypothesis. *)
  end

  (** Top-level command constructors. *)
  module Cmd : sig
    val [@deprecated "Use View equivalent instead"] query :
      ?fc:loc ->
      n:int option ->
      b:int option ->
      d:int option ->
      Query.query ->
      cmd
    (** [%query n b d expr] — logic programming query with bounds. *)

    val [@deprecated "Use View equivalent instead"] query_tabled :
      ?fc:loc ->
      n:int option ->
      b:int option ->
      d:int option ->
      Query.query ->
      cmd
    (** [%querytabled n b d expr] — tabled query with bounds. *)

    val [@deprecated "Use View equivalent instead"] adhoc_query :
      ?fc:loc -> Query.query -> cmd
    (** [%? expr] — ad-hoc REPL query. *)

    val [@deprecated "Use View equivalent instead"] unique :
      ?fc:loc -> term -> cmd
    (** [%unique expr] — assert expr has at most one inhabitant. *)

    val [@deprecated "Use View equivalent instead"] mode :
      ?fc:loc -> modeDec -> cmd
    (** [%mode hyps] — declare input/output polarity. *)

    val [@deprecated "Use View equivalent instead"] define :
      ?fc:loc -> Query.define -> cmd
    (** [%define id expr] — transparent definition. *)

    val [@deprecated "Use View equivalent instead"] decl_cmd :
      ?fc:loc -> term -> cmd
    (** [%decl expr] — raw elaboration-level declaration. *)

    val [@deprecated "Use View equivalent instead"] inline :
      ?fc:loc -> string -> term -> cmd
    (** [%inline id expr] — always-unfolded definition. *)

    val [@deprecated "Use View equivalent instead"] symbol :
      ?fc:loc -> string -> string -> cmd
    (** [%symbol id id] — associate a symbolic name. *)

    val [@deprecated "Use View equivalent instead"] freeze :
      ?fc:loc -> string list -> cmd
    (** [%freeze id_list] — freeze type families. *)

    val [@deprecated "Use View equivalent instead"] thaw :
      ?fc:loc -> string list -> cmd
    (** [%thaw id_list] — unfreeze type families. *)

    val [@deprecated "Use View equivalent instead"] sort :
      ?fc:loc -> string list -> decl list -> cmd
    (** [%sort id {decl}+] — declare a type family. *)

    val [@deprecated "Use View equivalent instead"] term :
      ?fc:loc -> decl -> cmd
    (** [%term decl] — declare a term-level constant. *)

    val [@deprecated "Use View equivalent instead"] block :
      ?fc:loc -> string -> block_item list -> cmd
    (** [%block id block_item*] — define a named context schema. *)

    val [@deprecated "Use View equivalent instead"] union :
      ?fc:loc -> string -> string list -> cmd
    (** [%union id ids] — union of block labels. *)

    val [@deprecated "Use View equivalent instead"] worlds :
      ?fc:loc -> string list -> term list -> cmd
    (** [%worlds ids exprs] — assert exprs live in the named world. *)

    val [@deprecated "Use View equivalent instead"] deterministic :
      ?fc:loc -> string list -> cmd
    (** [%deterministic id_list] — mark type families as deterministic. *)

    val [@deprecated "Use View equivalent instead"] eval :
      ?fc:loc -> cmd list -> cmd
    (** [%eval %{ cmds %}] — evaluate a command block. *)

    val [@deprecated "Use View equivalent instead"] prec :
      ?fc:loc -> fixity -> int -> string list -> cmd
    (** [%prec fixity n id_list] — set operator fixity and precedence. *)

    val [@deprecated "Use View equivalent instead"] solve :
      ?fc:loc -> Query.solve -> cmd
    (** [%solve] — solve command. *)

    val [@deprecated "Use View equivalent instead"] stop :
      ?fc:loc -> unit -> cmd
    (** [%.] — end-of-command marker. *)

    (** REPL-specific commands. *)
    module Repl : sig
      val [@deprecated "Use View equivalent instead"] quit :
        ?fc:loc -> unit -> cmd

      val [@deprecated "Use View equivalent instead"] help :
        ?fc:loc -> string option -> cmd

      val [@deprecated "Use View equivalent instead"] get :
        ?fc:loc -> string -> cmd

      val [@deprecated "Use View equivalent instead"] set :
        ?fc:loc -> string -> string -> cmd

      val [@deprecated "Use View equivalent instead"] version :
        ?fc:loc -> unit -> cmd
    end

    val [@deprecated "Use View equivalent instead"] total :
      ?fc:loc -> order list -> term list -> cmd
    (** [%total hyps modes] — declare a totality check. *)

    val [@deprecated "Use View equivalent instead"] terminates :
      ?fc:loc -> order list -> term list -> cmd
    (** [%terminates hyps modes] — declare a termination check. *)

    val [@deprecated "Use View equivalent instead"] covers :
      ?fc:loc -> modeDec -> cmd
    (** [%covers hyps modes] — declare a coverage check. *)

    val [@deprecated "Use View equivalent instead"] name :
      ?fc:loc -> string -> cmd
    (** [%name id] — declare a name for the next definition. *)

    val [@deprecated "Use View equivalent instead"] reduces :
      ?fc:loc -> string -> term list -> cmd
    (** [%reduces pred order_out order_in call_pats] — declare a reduction
        relation. *)
  end

  module Thm : sig
    (*! structure Paths : PATHS  !*)
    type order

    val [@deprecated "Use View equivalent instead"] varg :
      loc -> string list -> order

    val [@deprecated "Use View equivalent instead"] lex :
      loc -> order list -> order

    val [@deprecated "Use View equivalent instead"] simul :
      loc -> order list -> order

    type callpats

    val [@deprecated "Use View equivalent instead"] callpats :
      (string * string option list * loc) list -> callpats

    type tdecl

    val [@deprecated "Use View equivalent instead"] tdecl :
      order -> callpats -> tdecl

    (* -bp *)
    type predicate

    val [@deprecated "Use View equivalent instead"] predicate :
      string -> loc -> predicate

    (* -bp *)
    type rdecl

    val [@deprecated "Use View equivalent instead"] rdecl :
      predicate * order * order * callpats -> rdecl

    type tableddecl

    val [@deprecated "Use View equivalent instead"] tableddecl :
      string -> loc -> tableddecl

    type keepTabledecl

    val [@deprecated "Use View equivalent instead"] keepTabledecl :
      string -> loc -> keepTabledecl

    type prove

    val [@deprecated "Use View equivalent instead"] prove : int -> tdecl -> prove

    type establish

    val [@deprecated "Use View equivalent instead"] establish :
      int -> tdecl -> establish

    type assert_

    val [@deprecated "Use View equivalent instead"] assert_ :
      callpats -> assert_

    type decs
    type theorem
    type theoremdec

    val [@deprecated "Use View equivalent instead"] null : decs
    val [@deprecated "Use View equivalent instead"] decl : decs -> decl -> decs
    val [@deprecated "Use View equivalent instead"] top : theorem

    val [@deprecated "Use View equivalent instead"] exists :
      decs -> theorem -> theorem

    val [@deprecated "Use View equivalent instead"] forall :
      decs -> theorem -> theorem

    val [@deprecated "Use View equivalent instead"] forallStar :
      decs -> theorem -> theorem

    val [@deprecated "Use View equivalent instead"] forallG :
      (decs * decs) list -> theorem -> theorem

    val [@deprecated "Use View equivalent instead"] dec :
      string * theorem -> theoremdec

    (* world checker *)
    type wdecl

    val [@deprecated "Use View equivalent instead"] wdecl :
      (string list * string) list -> callpats -> wdecl
  end

  val [@deprecated "Use View equivalent instead"] show_term : term -> string
  (** Debug-print a term to a string. *)

  val [@deprecated "Use View equivalent instead"] pp_term :
    Stdlib.Format.formatter -> term -> unit
  (** Pretty-print a term to a formatter. *)

  (** {2 Views} *)

  (** Views should eventually supplant the rest of this module *)
  module View : sig
    include
      LENS.VIEW
        with type loc = loc
         and type qid_form = qid_form
         and type internal_tag = internal_tag
         and type Loc.t = loc
         and module Paths = Paths
         and type Term.t = term
         and type Decl.t = decl
         and type ConDec.t = conDec
         and type Mode.t = mode
         and type Mode.Term.t = modeTerm
         and type Mode.Dec.t = modeDec
         and type Struct.StrExp.t = strexp
         and type Struct.Inst.t = inst
         and type Struct.SigExp.t = sigexp
         and type Struct.SigDef.t = sigdef
         and type Struct.StructDec.t = structDec
         and type Query.t = query
         and type Solve.t = solve
         and type Define.t = define
         and type Fixity.t = fixity
         and type BlockItem.t = block_item
         and type Cmd.t = cmd
  end
end
