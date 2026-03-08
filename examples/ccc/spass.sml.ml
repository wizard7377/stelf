open! Basis

(*
  A simple traverser to generate input for the SPASS prover.
  Author: Frank Pfenning

Sample Session:

% cd /afs/cs/project/twelf/research/twelf/
% sml-cm
- CM.make ();
- use ""examples/ccc/spass.sml"";

This will print the SPASS representation for a bunch of axioms and theorems
of cartesian closed categories.  The encoding maps any morphism f : A -> B
(even compound ones) to the term mor(f,A,B) to guarantee type safety.

See

  spass.elf

for the definitions and status of various declarations.  Information on
the proofs can be found in pf.dvi (written by Andrzej Filinski) and
the other .elf files.
*)
module Spass : TRAVERSER = struct
  type tp =
    | QFProp of string
    | Prop of string * string
    | Mor of string
    | Obj
    | What of string

  (* Quantifier-free proposition *)
  (* Proposition (""xs"", ""A"") *)
  (* Morphism ""A,B"" *)
  (* Object ""A"" *)
  (* What ""?error?"" *)
  type nonrec obj = string
  type nonrec head = string
  type nonrec spine = string option
  type nonrec dec = string
  type nonrec condec = string

  let rec par s = ("(" ^ s) ^ ")"

  (* types *)
  let rec atom = function
    | "==", Some s_ -> QFProp ("equal" ^ par s_)
    | "mor", Some s_ -> Mor s_
    | "obj", None -> Obj
    | _ -> What "?atom?"
  (* | atom (""mor"", SOME(S)) = Mor (""arrow"" ^ par (S)) *)

  let rec arrow = function
    | QFProp a1_, QFProp a2_ -> QFProp ("implies" ^ par ((a1_ ^ ", ") ^ a2_))
    | _ -> What "?arrow?"
  (* ?? *)

  let rec pi = function
    | x, Prop (xs, a_) -> Prop ((xs ^ ",") ^ x, a_)
    | x, QFProp a_ -> Prop (x, "and" ^ par a_)
    | _ -> What "?pi?"

  (* terms *)
  let rec mor (f, a_) = "mor" ^ par ((f ^ ",") ^ a_)

  let rec root = function
    | "id", None, Mor a_ -> mor ("id", a_)
    | "@", Some s_, Mor a_ -> mor ("comp" ^ par s_, a_)
    | "1", None, Obj -> "one"
    | "*", Some s_, Obj -> "prod" ^ par s_
    | "drop", None, Mor a_ -> mor ("drop", a_)
    | "fst", None, Mor a_ -> mor ("fst", a_)
    | "snd", None, Mor a_ -> mor ("snd", a_)
    | "pair", Some s_, Mor a_ -> mor ("pair" ^ par s_, a_)
    | "=>", Some s_, Obj -> "func" ^ par s_
    | "app", None, Mor a_ -> mor ("app", a_)
    | "cur", Some s_, Mor a_ -> mor ("cur" ^ par s_, a_)
    | x, None, Obj -> x
    | x, None, Mor a_ -> mor (x, a_)
    | _ -> "?root?"
  (* morphism variables *)
  (* object variables *)
  (* constants *)

  let rec lam _ = "?lam?"
  let rec bvar x = x
  let rec const c = c
  let rec def d = d
  let nils = None

  let rec app = function
    | m_, None -> Some m_
    | m_, Some s_ -> Some ((m_ ^ ",") ^ s_)

  (* declarations *)
  let rec dec (x, a_) = x

  let rec objdec = function
    | c, Prop (xs, a_) ->
        (((("%% " ^ c) ^ " :\n") ^ "formula")
        ^ par ("forall" ^ par ((("[" ^ xs) ^ "],\n") ^ a_)))
        ^ ".\n"
    | c, QFProp a_ ->
        (((("%% " ^ c) ^ " :\n") ^ "formula") ^ par ("and" ^ par a_)) ^ ".\n"
    | c, _ -> ("%% " ^ c) ^ " : skipped.\n"
end

(* structure Spass *)
module Spass = Traverse (struct
  module IntSyn' = IntSyn
  module Whnf = Whnf
  module Names = Names
  module Traverser' = Spass
end)
;;

Twelf.Config.load (Twelf.Config.read "examples/ccc/spass.cfg");;

let rec ccc c =
  begin
    print (Spass.const c);
    print "\n"
  end
;;

begin
  ccc "id_l";
  begin
    ccc "id_r";
    begin
      ccc "ass";
      begin
        ccc "term_u";
        begin
          ccc "prod_l";
          begin
            ccc "prod_r";
            begin
              ccc "prod_u";
              begin
                ccc "exp_e";
                begin
                  ccc "exp_u";
                  begin
                    ccc "distp";
                    begin
                      ccc "appl";
                      begin
                        ccc "distc";
                        ()
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end
    end
  end
end
(* Equality *)
(* refl, then, sym *)
(* identity and composition *)
(* =@= *)
(* products *)
(* =pair= *)
(* exponentials *)
(* =cur= *)
(* lemmas *)
