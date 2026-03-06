open! Basis;;
(* Indexing (Constants and Skolem constants) *);;
(* Author: Carsten Schuermann *);;
(* Modified: Frank Pfenning *);;
module IndexSkolem(IndexSkolem__0: sig
                                   module Global : GLOBAL
                                   module Queue : QUEUE
                                   end) : INDEX
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    open!
      struct
        module I = IntSyn;;
        let rec cidFromHead = function 
                                       | I.Const c -> c
                                       | I.Def c -> c;;
        let indexArray : IntSyn.head_ Queue.queue Array.array =
          Array.array (Global.maxCid + 1, Queue.empty);;
        let rec reset () =
          Array.modify (function 
                                 | _ -> Queue.empty) indexArray;;
        let rec update (a, c) =
          Array.update
          (indexArray, a, Queue.insert (c, Array.sub (indexArray, a)));;
        let rec install arg__1 arg__2 =
          begin
          match (arg__1, arg__2)
          with 
               | (fromCS, (I.Const c as h_))
                   -> begin
                      match (fromCS, I.sgnLookup c)
                      with 
                           | (_, I.ConDec (_, _, _, _, a_, type_))
                               -> update (cidFromHead (I.targetHead a_), h_)
                           | (clause_, I.ConDef (_, _, _, _, a_, type_, _))
                               -> update
                                  (cidFromHead (I.targetHead a_), (I.Def c))
                           | _ -> ()
                      end
               | (fromCS, (I.Skonst c as h_))
                   -> begin
                      match I.sgnLookup c
                      with 
                           | I.SkoDec (_, _, _, a_, type_)
                               -> update (cidFromHead (I.targetHead a_), h_)
                           | _ -> ()
                      end
          end;;
        let rec remove (a, cid) =
          begin
          match Queue.deleteEnd (Array.sub (indexArray, a))
          with 
               | None -> ()
               | Some (I.Const cid', queue') -> begin
                   if cid = cid' then Array.update (indexArray, a, queue')
                   else () end
               | Some (I.Skonst cid', queue') -> begin
                   if cid = cid' then Array.update (indexArray, a, queue')
                   else () end
          end;;
        let rec uninstall cid =
          begin
          match I.sgnLookup cid
          with 
               | I.ConDec (_, _, _, _, a_, type_)
                   -> remove (cidFromHead (I.targetHead a_), cid)
               | I.SkoDec (_, _, _, a_, type_)
                   -> remove (cidFromHead (I.targetHead a_), cid)
               | _ -> ()
          end;;
        let rec resetFrom mark =
          let (limit, _) = I.sgnSize ()
            in let rec iter i = begin
                 if i < mark then () else
                 begin
                   uninstall i;Array.update (indexArray, i, Queue.empty)
                   end
                 end in iter (limit - 1);;
        let rec lookup a =
          let rec lk =
            function 
                     | (l, None) -> l
                     | (l, Some q')
                         -> begin
                              Array.update (indexArray, a, q');l
                              end
            in lk (Queue.toList (Array.sub (indexArray, a)));;
        end;;
    (* Index array

       Invariant:
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *);;
    (* reset () = ()
       Empties index array
    *);;
    (* update (a, c) = ()
       inserts c into the index queue for family a
       Invariant: a = target family of c
    *);;
    (* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *);;
    (* lookup a = [c1,...,cn] *);;
    (*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *);;
    let reset = reset;;
    let resetFrom = resetFrom;;
    let install = install;;
    let lookup = lookup;;
    end;;
(*! structure IntSyn' : INTSYN !*);;
(* local *);;
(* functor Index *);;