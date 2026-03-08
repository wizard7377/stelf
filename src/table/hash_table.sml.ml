open! Basis
open Table_

(* Hash Table *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga *)
module HashTable (HashTable__0 : sig
  type nonrec key'

  val hash : key' -> int
  val eq : key' * key' -> bool
end) : TABLE with type key = HashTable__0.key' = struct
  open HashTable__0

  type nonrec key = key'
  type nonrec 'a entry = key * 'a

  (* A hashtable bucket is a linked list of mutable elements *)
  (* A hashtable is an array of buckets containing entries paired with hash values *)
  type 'a bucket = Nil | Cons of 'a ref * 'a bucket ref
  type nonrec 'a table_ = (int * 'a entry) bucket array * int

  let rec new_ n = (Array.array (n, Nil), n)

  let rec insertShadow (a, n) ((key, datum) as e) =
    let hashVal = hash key in
    let index = hashVal mod n in
    let bucket = Array.sub (a, index) in
    let rec insertB
        (Cons (({ contents = hash', ((key', datum') as e') } as r'), br')) =
      begin if hashVal = hash' && eq (key, key') then begin
        r' := (hashVal, e);
        Some e'
      end
      else insertBR br'
      end
    and insertBR = function
      | { contents = Nil } as br -> begin
          br := Cons (ref (hashVal, e), ref Nil);
          None
        end
      | br -> insertB !br
    in
    let rec insertA = function
      | Nil -> begin
          Array.update (a, index, Cons (ref (hashVal, e), ref Nil));
          None
        end
      | bucket -> insertB bucket
    in
    insertA bucket

  let rec insert h e =
    begin
      ignore (insertShadow h e)
    end

  let rec lookup (a, n) key =
    let hashVal = hash key in
    let rec lookup' = function
      | Cons ({ contents = hash1, (key1, datum1) }, br) -> begin
          if hashVal = hash1 && eq (key, key1) then Some datum1 else lookup' !br
        end
      | Nil -> None
    in
    let bucket = Array.sub (a, hashVal mod n) in
    lookup' bucket

  let rec delete (a, n) key =
    let hashVal = hash key in
    let index = hashVal mod n in
    let bucket = Array.sub (a, index) in
    let rec deleteBR = function
      | { contents = Cons ({ contents = hash1, (key1, _) }, br1) } as br ->
        begin
          if hashVal = hash1 && eq (key, key1) then br := !br1 else deleteBR br1
        end
      | br -> ()
    in
    let rec deleteA = function
      | Nil -> ()
      | Cons ({ contents = hash1, (key1, _) }, br1) -> begin
          if hashVal = hash1 && eq (key, key1) then Array.update (a, index, !br1)
          else deleteBR br1
        end
    in
    deleteA bucket

  let rec clear (a, n) = Array.modify (function _ -> Nil) a

  let rec appBucket arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | f, Nil -> ()
    | f, Cons ({ contents = _, e }, br) -> begin
        f e;
        appBucket f !br
      end
    end

  let rec app f (a, n) = Array.app (appBucket f) a
end
(* functor HashTable *)
