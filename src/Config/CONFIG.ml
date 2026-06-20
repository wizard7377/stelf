
module Flag = struct 
  type 'a parser = 

  (** Whether or not [A-Z] charecters are treated as uppercase*)
  | UppercaseLatin : bool parser

  (** If [->] is a valid alternative to [%->] (and the same for [<-])*)
  | ArrowAliases : bool parser


  (** Whether [|] can be used in context in a world / block *)
  | BarInContext : bool parser

  (** Whether [:] can be used in decl *)
  | ColonInDecl : bool parser

  (** Whether [=] can be used in def *)
  | EqualInDef : bool parser

  (** Whether [.] is a alternative to [.] *)
  | StopReserved : bool parser
  type 'a display = 
  UseColors : bool display
  type 'a solver = 
  DoubleCheck : bool solver 

  type 'a t = Parser of 'a parser | Solver of 'a solver | Display of 'a display
  let default : 'a t -> 'a = function 
    | Parser UppercaseLatin -> false
    | Parser ArrowAliases -> false
    | Parser BarInContext -> false
    | Parser ColonInDecl -> false
    | Parser EqualInDef -> false
    | Parser StopReserved -> false
    | Display UseColors -> true
    | Solver DoubleCheck -> false
end

module type CONFIG = sig 
  type 'a t
  val get : 'a t -> 'a 
  val set : 'a t -> 'a -> unit

end 