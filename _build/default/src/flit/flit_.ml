# 1 "src/flit/flit_.sig.ml"
open! Basis;;
(* Flit DAG generator *);;
(* Author: Roberto Virga *);;
module type FLIT = sig
                   (* init (sym_table_file) *)
                   val init : string -> unit
                   (* initForText () *)
                   val initForText : unit -> unit
                   (* dump (symbol, dag_file) *)
                   val dump : (string * string) -> int
                   (* dumpText (outputSemant, outputChecker) *)
                   val dumpText : (string * string) -> unit
                   (* setFlag () *)
                   val setFlag : unit -> unit
                   (* setEndTcb () *)
                   val setEndTcb : unit -> unit
                   (* dumpFlagged (dag_file) *)
                   val dumpFlagged : string -> unit
                   (* dumpSynTable (start_sym, end_sym, sym_table_file) *)
                   val dumpSymTable : (string * string * string) -> unit
                   end;;
(* signature FLIT *);;
# 1 "src/flit/flit_.fun.ml"
open! Basis;;
(* Flit DAG generator *);;
(* Author: Roberto Virga *);;
module Flit(Flit__0: sig
                     module Global : GLOBAL
                     module Word : WORD
                     module Pack : PACK_WORD
                     module Whnf : WHNF
                     module Names : NAMES
                     module Table : TABLE
                     module Index : INDEX
                     module Print : PRINT
                     end) : FLIT
  =
  struct
    open!
      struct
        module W = Word;;
        module I = IntSyn;;
        module N = Names;;
        module F = Names.Fixity;;
        module Idx = Index;;
        module SHT = StringHashTable;;
        module IHT = Table;;
        exception Error of string ;;
        let size_of_expr = 3;;
        let tcb_table : (string * int) list option ref = ref None;;
        let tcb_size : int ref = ref 0;;
        let rec print_table () =
          let rec print_table' =
            function 
                     | [] -> ()
                     | ((name, addr) :: [])
                         -> print
                            (((("(\"" ^ name) ^ "\", ") ^ (Int.toString addr))
                               ^ ")\n")
                     | ((name, addr) :: pairs)
                         -> begin
                              print
                              (((("(\"" ^ name) ^ "\", ") ^
                                  (Int.toString addr))
                                 ^ "),\n");
                              print_table' pairs
                              end
            in begin
                 print "val tcb_table := [\n";
                 begin
                   print_table' (valOf (! tcb_table));print "];\n"
                   end
                 
                 end;;
        let rec print_size () =
          print (("val tcb_size = " ^ (Int.toString (! tcb_size))) ^ ";\n");;
        let rec init filename =
          let stream = TextIO.openIn filename
            in let linecount = (ref 0 : int ref)
                 in let rec get_line () =
                      begin
                        linecount := ((! linecount) + 1);
                        Compat.inputLine97 stream
                        end
                      in let rec error () =
                           raise
                           ((Error
                             ((("Error reading file '" ^ filename) ^
                                 "', line ")
                                ^ (Int.toString (! linecount)))))
                           in let rec read_size () =
                                begin
                                match Int.fromString (get_line ())
                                with 
                                     | Some tcb_size -> tcb_size
                                     | None -> error ()
                                end
                                in let () = tcb_size := (read_size ())
                                     in let () = begin
                                          if (! Global.chatter) >= 3 then
                                          print_size () else () end
                                          in let rec read_table =
                                               function 
                                                        | "" -> []
                                                        | line
                                                            -> begin
                                                               match 
                                                               String.tokens
                                                               Char.isSpace
                                                               line
                                                               with 
                                                                    | 
                                                                    (id
                                                                    :: 
                                                                    (addr
                                                                    :: []))
                                                                    -> 
                                                                    ((id,
                                                                    valOf
                                                                    (Int.fromString
                                                                    addr))
                                                                    :: 
                                                                    read_table
                                                                    (get_line
                                                                    ()))
                                                                    | 
                                                                    _
                                                                    -> 
                                                                    error
                                                                    ()
                                                               end
                                               in let () =
                                                    tcb_table :=
                                                      ((Some
                                                        (read_table
                                                         (get_line ()))))
                                                    in let () = begin
                                                         if
                                                         (! Global.chatter)
                                                           >= 3
                                                         then print_table ()
                                                         else () end
                                                         in let () =
                                                              TextIO.closeIn
                                                              stream in ();;
        let closedMask = LargeWord.fromInt 256;;
        let predicateMask = LargeWord.fromInt 512;;
        let clauseMask = LargeWord.fromInt 1024;;
        let baseAddr : int ref = ref 0;;
        let startClause : int option ref = ref None;;
        let startSemant : int option ref = ref None;;
        let tuples : int ref = ref 0;;
        let out : BinIO.outstream option ref = ref None;;
        let symTable : W.word Table.table_ = Table.new_ 32;;
        let printTable : unit Table.table_ = Table.new_ 32;;
        let shadowTable : int SHT.table_ = SHT.new_ 32;;
        let depTable : unit IHT.table_ IHT.table_ = IHT.new_ 32;;
        let recordTable : unit IHT.table_ = IHT.new_ 32;;
        let imitatesTable : int IHT.table_ = IHT.new_ 32;;
        let replaceTable : string IHT.table_ = IHT.new_ 32;;
        let rec cname cid = I.conDecName (I.sgnLookup cid);;
        let rec clookup name =
          let size = (fun (r, _) -> r) (I.sgnSize ())
            in let rec clookup' cid = begin
                 if cid = size then
                 raise ((Error (("symbol " ^ name) ^ " not found"))) else
                 begin if (cname cid) = name then cid else clookup' (cid + 1)
                 end end in clookup' 0;;
        let rec print_once cid =
          begin
          match Table.lookup printTable cid
          with 
               | None
                   -> begin
                        Table.insert printTable (cid, ());
                        print
                        ((Print.conDecToString (I.sgnLookup cid)) ^ "\n")
                        end
               | Some _ -> ()
          end;;
        let rec print_tuple (addr, code, (cld, prd, cls), arg1, arg2) =
          print
          ((((((((((((((W.fmt StringCvt.dec_ addr) ^ " : ") ^
                        (Char.toString code))
                       ^ "\t")
                      ^ (Bool.toString cld))
                     ^ "\t")
                    ^ (Bool.toString prd))
                   ^ "\t")
                  ^ (Bool.toString cls))
                 ^ "\t")
                ^ (W.fmt StringCvt.dec_ arg1))
               ^ "\t")
              ^ (W.fmt StringCvt.dec_ arg2))
             ^ "\n");;
        let rec writeArray array =
          begin
          match ! out
          with 
               | Some stream
                   -> begin
                        tuples := ((! tuples) + 1);
                        BinIO.output
                        (stream,
                         Word8ArraySlice.vector
                         (Word8ArraySlice.slice (array, 0, None)))
                        
                        end
               | None -> ()
          end;;
        let rec tuple (code, ((cld, prd, cls) as flags), arg1, arg2) =
          let addr = W.fromInt ((! tuples) + (! tcb_size))
            in let array =
                 Word8Array.array
                 (Pack.bytesPerElem * size_of_expr, Word8.fromInt 0)
                 in let opcode =
                      ref (Word8.toLargeWord (Byte.charToByte code))
                      in begin
                           begin
                           if cld then
                           opcode := (LargeWord.orb (! opcode, closedMask))
                           else () end;
                           begin
                             begin
                             if prd then
                             opcode :=
                               (LargeWord.orb (! opcode, predicateMask))
                             else () end;
                             begin
                               begin
                               if cls then
                               opcode :=
                                 (LargeWord.orb (! opcode, clauseMask))
                               else () end;
                               begin
                                 Pack.update (array, 0, ! opcode);
                                 begin
                                   Pack.update (array, 1, W.toLargeWord arg1);
                                   begin
                                     Pack.update
                                     (array, 2, W.toLargeWord arg2);
                                     begin
                                       begin
                                       if (! Global.chatter) >= 4 then
                                       print_tuple
                                       (addr, code, flags, arg1, arg2) else
                                       () end;begin
                                                writeArray array;addr
                                                end
                                       
                                       end
                                     
                                     end
                                   
                                   end
                                 
                                 end
                               
                               end
                             
                             end
                           
                           end;;
        let kd = function 
                          | () -> W.fromInt 0;;
        let ty = function 
                          | () -> W.fromInt 1;;
        let rec const arg__1 arg__2 =
          begin
          match (arg__1, arg__2)
          with 
               | (true, ty)
                   -> tuple ('c', (true, true, true), W.fromInt 0, ty)
               | (false, _) -> W.fromInt 0
          end;;
        let rec var arg__3 arg__4 =
          begin
          match (arg__3, arg__4)
          with 
               | (true, ty)
                   -> tuple ('v', (false, false, false), W.fromInt 0, ty)
               | (false, _) -> W.fromInt 0
          end;;
        let rec pi arg__5 arg__6 =
          begin
          match (arg__5, arg__6)
          with 
               | (true, (flags, var, exp)) -> tuple ('p', flags, var, exp)
               | (false, _) -> W.fromInt 0
          end;;
        let rec lam arg__7 arg__8 =
          begin
          match (arg__7, arg__8)
          with 
               | (true, (flags, var, exp)) -> tuple ('l', flags, var, exp)
               | (false, _) -> W.fromInt 0
          end;;
        let rec app arg__9 arg__10 =
          begin
          match (arg__9, arg__10)
          with 
               | (true, (flags, exp, arg)) -> tuple ('a', flags, exp, arg)
               | (false, _) -> W.fromInt 0
          end;;
        let rec annotate arg__11 arg__12 =
          begin
          match (arg__11, arg__12)
          with 
               | (true, (flags, arg, exp)) -> tuple (':', flags, arg, exp)
               | (false, _) -> W.fromInt 0
          end;;
        let rec scanNumber string =
          let rec check =
            function 
                     | ((_ :: _) as chars) -> List.all Char.isDigit chars
                     | [] -> false
            in begin
            if check (String.explode string) then
            StringCvt.scanString (W.scan StringCvt.dec_) string else None end;;
        let rec scanBinopPf oper string =
          let args = String.tokens (function 
                                             | c -> c = oper) string
            in begin
               match args
               with 
                    | (arg1 :: (arg2 :: []))
                        -> begin
                           match (StringCvt.scanString
                                  (W.scan StringCvt.dec_)
                                  arg1,
                                  StringCvt.scanString
                                  (W.scan StringCvt.dec_)
                                  arg2)
                           with 
                                | (Some d1, Some d2) -> (Some (d1, d2))
                                | _ -> None
                           end
                    | _ -> None
               end;;
        let rec scanTernopPf oper1 oper2 string =
          let args = String.tokens (function 
                                             | c -> c = oper1) string
            in begin
               match args
               with 
                    | (arg1 :: (args2 :: []))
                        -> let args' =
                             String.tokens (function 
                                                     | c -> c = oper2) args2
                             in begin
                                match args'
                                with 
                                     | (arg2 :: (arg3 :: []))
                                         -> begin
                                            match (StringCvt.scanString
                                                   (W.scan StringCvt.dec_)
                                                   arg1,
                                                   StringCvt.scanString
                                                   (W.scan StringCvt.dec_)
                                                   arg2,
                                                   StringCvt.scanString
                                                   (W.scan StringCvt.dec_)
                                                   arg3)
                                            with 
                                                 | (Some d1, Some d2, Some
                                                    d3)
                                                     -> (Some (d1, d2, d3))
                                                 | _ -> None
                                            end
                                     | _ -> None
                                end
                    | _ -> None
               end;;
        let rec isPredicate cid =
          begin
          match (! startClause, I.constUni cid)
          with 
               | (Some cid', kind_) -> cid >= cid'
               | _ -> false
          end;;
        let rec headCID =
          function 
                   | I.Const cid -> (Some cid)
                   | I.Skonst cid -> (Some cid)
                   | I.Def cid -> (Some cid)
                   | I.NSDef cid -> (Some cid)
                   | _ -> None;;
        let rec isClause cid =
          begin
          match (! startClause, I.constUni cid)
          with 
               | (Some cid', type_) -> begin
                   if cid >= cid' then
                   let a = I.targetHead (I.constType cid)
                     in let clauses =
                          List.mapPartial
                          headCID
                          (Idx.lookup (valOf (headCID a)))
                          in List.exists (function 
                                                   | x -> x = cid) clauses
                   else false end
               | _ -> false
          end;;
        let rec lookup cid =
          begin
          match Table.lookup symTable cid
          with 
               | Some idx -> idx
               | None
                   -> let idx =
                        compileConDec
                        (I.sgnLookup cid, (isPredicate cid, isClause cid))
                        in let () = Table.insert symTable (cid, idx)
                             in let () = begin
                                  if (! Global.chatter) >= 3 then
                                  print_once cid else () end in idx
          end
        and compileUni = function 
                                  | kind_ -> kd ()
                                  | type_ -> ty ()
        and compileExpN arg__13 arg__14 =
          begin
          match (arg__13, arg__14)
          with 
               | (generate, (g_, I.Uni v_, flags)) -> compileUni v_
               | (generate,
                  (g_, I.Pi ((I.Dec (_, u1_), _), u2_),
                   ((cld, _, _) as flags)))
                   -> let idxU1 =
                        compileExpN generate (g_, u1_, (cld, false, false))
                        in let idxU1var = var generate idxU1
                             in let idxU2 =
                                  compileExpN
                                  generate
                                  ((I.Decl (g_, idxU1var)), u2_,
                                   (false, false, false))
                                  in pi generate (flags, idxU1var, idxU2)
               | (generate,
                  (g_, I.Lam ((I.Dec (_, u1_) as d_), u2_),
                   ((cld, _, _) as flags)))
                   -> let idxU1 =
                        compileExpN generate (g_, u1_, (cld, false, false))
                        in let idxU1var = var generate idxU1
                             in let idxU2 =
                                  compileExpN
                                  generate
                                  ((I.Decl (g_, idxU1var)), u2_,
                                   (false, false, false))
                                  in lam generate (flags, idxU1var, idxU2)
               | (generate, (g_, (I.Root (h_, s_) as u_), flags))
                   -> let idx = compileHead generate (g_, h_)
                        in compileSpine generate (g_, idx, s_, flags)
               | (generate, (g_, I.FgnExp csfe, flags))
                   -> compileExp
                      generate
                      (g_, I.FgnExpStd.ToInternal.apply csfe (), flags)
          end
        and compileSpine arg__15 arg__16 =
          begin
          match (arg__15, arg__16)
          with 
               | (generate, (g_, idx, nil_, flags)) -> idx
               | (generate,
                  (g_, idx, I.App (u1_, nil_), ((cld, _, _) as flags)))
                   -> let idxU1 =
                        compileExpN generate (g_, u1_, (cld, false, false))
                        in app generate (flags, idx, idxU1)
               | (generate,
                  (g_, idx, I.App (u1_, s_), ((cld, _, _) as flags)))
                   -> let idxU1 =
                        compileExpN generate (g_, u1_, (cld, false, false))
                        in compileSpine
                           generate
                           (g_,
                            app generate ((cld, false, false), idx, idxU1),
                            s_, flags)
          end
        and compileHead arg__17 arg__18 =
          begin
          match (arg__17, arg__18)
          with 
               | (generate, (g_, I.BVar k)) -> I.ctxLookup (g_, k)
               | (generate, (g_, I.Const cid)) -> lookup cid
               | (generate, (g_, I.Def cid)) -> lookup cid
               | (generate, (g_, I.NSDef cid)) -> lookup cid
               | (generate, (g_, I.FgnConst (cs, conDec)))
                   -> compileFgnDec generate (g_, conDec)
          end
        and compileFgnDec arg__19 arg__20 =
          begin
          match (arg__19, arg__20)
          with 
               | (true, (g_, conDec))
                   -> let name = I.conDecName conDec
                        in let flags = (true, false, false)
                             in begin
                                match scanNumber name
                                with 
                                     | Some n
                                         -> tuple
                                            ('#', flags, n, W.fromInt 0)
                                     | None
                                         -> begin
                                            match scanBinopPf '/' name
                                            with 
                                                 | Some (n1, n2)
                                                     -> tuple
                                                        ('/', flags, n1, n2)
                                                 | None
                                                     -> begin
                                                        match scanBinopPf
                                                              '+'
                                                              name
                                                        with 
                                                             | Some (n1, n2)
                                                                 -> tuple
                                                                    ('+',
                                                                    flags,
                                                                    n1, n2)
                                                             | None
                                                                 -> begin
                                                                    match 
                                                                    scanBinopPf
                                                                    '*'
                                                                    name
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    (n1, n2)
                                                                    -> 
                                                                    tuple
                                                                    ('*',
                                                                    flags,
                                                                    n1, n2)
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    raise
                                                                    ((Error
                                                                    ("unknown foreign constant "
                                                                    ^ name)))
                                                                    end
                                                        end
                                            end
                                end
               | (false, _) -> W.fromInt 0
          end
        and compileExp generate (g_, u_, flags) =
          compileExpN generate (g_, Whnf.normalize (u_, I.id), flags)
        and compileConDec =
          function 
                   | ((I.ConDec (_, _, _, _, v_, _) as condec), (true, cls))
                       -> const
                          true
                          (compileExpN true (I.null_, v_, (true, true, cls)))
                   | ((I.ConDec (_, _, _, _, _, _) as condec), (pred, cls))
                       -> raise
                          ((Error
                            ("attempt to shadow constant " ^
                               (I.conDecName condec))))
                   | ((I.ConDef (_, _, _, u_, v_, _, _) as condec),
                      (pred, cls))
                       -> let exp =
                            compileExpN
                            true
                            (I.null_, v_, (true, false, false))
                            in let arg =
                                 compileExpN
                                 true
                                 (I.null_, u_, (true, pred, cls))
                                 in annotate
                                    true
                                    ((true, pred, cls), arg, exp)
                   | ((I.AbbrevDef (_, _, _, u_, v_, _) as condec),
                      (pred, cls))
                       -> let exp =
                            compileExpN
                            true
                            (I.null_, v_, (true, false, false))
                            in let arg =
                                 compileExpN
                                 true
                                 (I.null_, u_, (true, pred, cls))
                                 in annotate
                                    true
                                    ((true, pred, cls), arg, exp);;
        let rec initTuples () =
          let _ = tuples := 0
            in let _ = Table.clear symTable
                 in let _ = Table.clear printTable
                      in begin
                         match ! tcb_table
                         with 
                              | Some l
                                  -> List.app
                                     (function 
                                               | (name, idx)
                                                   -> Table.insert
                                                      symTable
                                                      (clookup name,
                                                       W.fromInt idx))
                                     l
                              | None
                                  -> raise
                                     ((Error "dump(...) before init(...)"))
                         end;;
        let rec dump (name, file) =
          let rec dump' cid =
            let _ = out := ((Some (BinIO.openOut file)))
              in let stream = valOf (! out)
                   in let _ = initTuples ()
                        in let idx = W.toInt (lookup cid)
                             in let _ = BinIO.closeOut stream in idx
            in let rec error msg =
                 let rec closeOut () =
                   begin
                   match ! out
                   with 
                        | Some stream -> BinIO.closeOut stream
                        | None -> ()
                   end
                   in begin
                        print (("Error: " ^ msg) ^ "\n");
                        begin
                          closeOut ();(-1)
                          end
                        
                        end
                 in begin
                    match N.constLookup (valOf (N.stringToQid name))
                    with 
                         | Some cid
                             -> try dump' cid with 
                                                   | Error msg -> error msg
                         | None
                             -> error (("symbol " ^ name) ^ " not found\n")
                    end;;
        let rec setFlag () =
          begin
          match ! startClause
          with 
               | Some cid -> print "Error: flag already set\n"
               | None
                   -> startClause :=
                        ((Some ((fun (r, _) -> r) (I.sgnSize ()))))
          end;;
        let rec setEndTcb () =
          begin
          match ! startSemant
          with 
               | Some cid -> print "Error: flag already set\n"
               | None
                   -> startSemant :=
                        ((Some ((fun (r, _) -> r) (I.sgnSize ()))))
          end;;
        let rec dumpFlagged file =
          let max = (fun (r, _) -> r) (I.sgnSize ())
            in let rec compileSeq cid = begin
                 if cid < max then begin
                                     lookup cid;compileSeq (cid + 1)
                                     end
                 else () end
                 in let rec dump' cid =
                      begin
                        out := ((Some (BinIO.openOut file)));
                        begin
                          initTuples ();
                          begin
                            compileSeq cid;BinIO.closeOut (valOf (! out))
                            end
                          
                          end
                        
                        end
                      in let rec error msg =
                           let rec closeOut () =
                             begin
                             match ! out
                             with 
                                  | Some stream -> BinIO.closeOut stream
                                  | None -> ()
                             end
                             in begin
                                  print (("Error: " ^ msg) ^ "\n");
                                  closeOut ()
                                  end
                           in begin
                              match ! startClause
                              with 
                                   | Some cid
                                       -> try dump' cid
                                          with 
                                               | Error msg -> error msg
                                   | None
                                       -> error
                                          "setFlag() has not been called yet\n"
                              end;;
        let rec dumpSymTable (name1, name2, file) =
          let stream = TextIO.openOut file
            in let F.Strength nonfixLevel = F.minPrec
                 in let rec dumpFixity cid =
                      begin
                      match N.getFixity cid
                      with 
                           | F.Infix (F.Strength level, left_) -> (level, 1)
                           | F.Infix (F.Strength level, right_) -> (level, 2)
                           | F.Infix (F.Strength level, none_) -> (level, 3)
                           | nonfix_ -> (nonfixLevel, 0)
                      end
                      in let rec dumpEntry cid =
                           begin
                           match (Table.lookup symTable cid, dumpFixity cid)
                           with 
                                | (Some idx, (level, assoc))
                                    -> TextIO.output
                                       (stream,
                                        (((((((I.conDecName (I.sgnLookup cid))
                                                ^ "\t")
                                               ^
                                               (Word.fmt StringCvt.dec_ idx))
                                              ^ "\t")
                                             ^ (Int.toString level))
                                            ^ "\t")
                                           ^ (Int.toString assoc))
                                          ^ "\n")
                                | (None, _) -> ()
                           end
                           in let rec dumpTable (cid1, cid2) = begin
                                if cid1 <= cid2 then
                                begin
                                  dumpEntry cid1;dumpTable (cid1 + 1, cid2)
                                  end
                                else () end
                                in let rec error msg =
                                     print (("Error: " ^ msg) ^ "\n")
                                     in begin
                                          begin
                                          match (N.constLookup
                                                 (valOf (N.stringToQid name1)),
                                                 N.constLookup
                                                 (valOf (N.stringToQid name2)))
                                          with 
                                               | (Some cid1, Some cid2)
                                                   -> dumpTable (cid1, cid2)
                                               | (None, _)
                                                   -> error
                                                      (name1 ^ " undefined")
                                               | (_, None)
                                                   -> error
                                                      (name2 ^ " undefined")
                                          end;
                                          begin
                                            TextIO.flushOut stream;
                                            TextIO.closeOut stream
                                            end
                                          
                                          end;;
        let rec sort cmp l =
          let rec split l =
            let rec s arg__21 arg__22 arg__23 =
              begin
              match (arg__21, arg__22, arg__23)
              with 
                   | (a1, a2, []) -> (a1, a2)
                   | (a1, a2, (h :: t)) -> s a2 ((h :: a1)) t
              end in s [] [] l
            in let rec merge arg__24 arg__25 =
                 begin
                 match (arg__24, arg__25)
                 with 
                      | (a, []) -> a
                      | ([], b) -> b
                      | (((a :: ta) as aa), ((b :: tb) as bb))
                          -> begin
                             match cmp (a, b)
                             with 
                                  | EQUAL -> (a :: b :: merge ta tb)
                                  | LESS -> (a :: merge ta bb)
                                  | GREATER -> (b :: merge aa tb)
                             end
                 end
                 in let rec ms =
                      function 
                               | [] -> []
                               | (s :: []) -> [s]
                               | (a :: (b :: [])) -> merge [a] [b]
                               | ll
                                   -> let (a, b) = split ll
                                        in merge (ms a) (ms b)
                      in ms l;;
        let rec sortedKeys t =
          let r = ref []
            in let _ = IHT.app (function 
                                         | x -> r := ((x :: ! r))) t
                 in sort Int.compare (map (fun (r, _) -> r) (! r));;
        exception NoPriorEntry_ of string ;;
        exception Error of string ;;
        let rec valOfE arg__26 arg__27 =
          begin
          match (arg__26, arg__27)
          with 
               | (e, None) -> raise e
               | (e, Some x) -> x
          end;;
        let counter = ref 0;;
        let rec isShadowedBy cid =
          let name = I.conDecName (I.sgnLookup cid)
            in let currentcid =
                 valOfE ((NoPriorEntry_ name)) (SHT.lookup shadowTable name)
                 in (name, begin
                     if currentcid <> cid then (Some currentcid) else None
                     end);;
        let rec isShadowing () =
          let _ = SHT.clear shadowTable
            in let changes = ref false
                 in let rec processDep rcid cid =
                      let rec handleProblem (currentcid, name) =
                        begin
                        match Table.lookup replaceTable cid
                        with 
                             | Some _ -> ()
                             | _
                                 -> let replacement =
                                      Option.map
                                      (fun x -> I.conDecName (I.sgnLookup x))
                                      (Table.lookup imitatesTable cid)
                                      in begin
                                         match replacement
                                         with 
                                              | None
                                                  -> raise
                                                     ((Error
                                                       (((((((("Error: " ^
                                                                 name)
                                                                ^ " (")
                                                               ^
                                                               (Int.toString
                                                                cid))
                                                              ^
                                                              ") used by cid ")
                                                             ^
                                                             (Int.toString
                                                              rcid))
                                                            ^
                                                            " but shadowed by ")
                                                           ^
                                                           (Int.toString
                                                            currentcid))
                                                          ^ ".\n")))
                                              | Some x
                                                  -> Table.insert
                                                     replaceTable
                                                     (cid, x)
                                         end
                        end
                        in let (name, sb) = isShadowedBy cid
                             in begin
                                match sb
                                with 
                                     | Some currentcid -> begin
                                         if
                                         (cid < (valOf (! startSemant))) ||
                                           (cid >= (valOf (! startClause)))
                                         then
                                         handleProblem (currentcid, name)
                                         else
                                         let newname =
                                           "shadowed_" ^
                                             (Int.toString (! counter))
                                           in begin
                                                I.rename (cid, newname);
                                                begin
                                                  SHT.insert
                                                  shadowTable
                                                  (newname, cid);
                                                  begin
                                                    counter :=
                                                      ((! counter) + 1);
                                                    changes := true
                                                    end
                                                  
                                                  end
                                                
                                                end
                                         end
                                     | None -> ()
                                end
                      in let rec processCid cid =
                           let name = I.conDecName (I.sgnLookup cid)
                             in begin
                                  try List.app
                                      (processDep cid)
                                      (sortedKeys
                                       (valOf (IHT.lookup depTable cid)))
                                  with 
                                       | Option -> ();
                                  SHT.insert shadowTable (name, cid)
                                  end
                           in begin
                                try List.app
                                    processCid
                                    (sortedKeys recordTable)
                                with 
                                     | (NoPriorEntry_ s as e)
                                         -> begin
                                              print
                                              (("Error: No Prior Entry: " ^ s)
                                                 ^ "\n");
                                              raise e
                                              end;
                                ! changes
                                end;;
        let rec is_def cid =
          try begin
                I.constDef cid;true
                end with 
                         | Match -> false;;
        let rec fixityDec cid =
          begin
          match N.getFixity cid
          with 
               | (F.Infix _ as f)
                   -> (((F.toString f) ^ " ") ^
                         (I.conDecName (I.sgnLookup cid)))
                        ^ ".\n"
               | _ -> ""
          end;;
        let rec record_once k cid =
          begin
          match IHT.insertShadow recordTable (cid, ())
          with 
               | None -> k cid
               | Some _ -> ()
          end;;
        let rec recordDependency (x, y) =
          let table =
            begin
            match IHT.lookup depTable x
            with 
                 | Some y -> y
                 | None
                     -> let t = IHT.new_ 32
                          in begin
                               IHT.insert depTable (x, t);t
                               end
            end in IHT.insert table (y, ());;
        open! struct
                open I;;
                end;;
        let rec etaReduce arg__28 arg__29 =
          begin
          match (arg__28, arg__29)
          with 
               | (n, Root (h, sp)) -> begin
                   if etaReduceSpine n sp then (Some h) else None end
               | (n, Lam (_, t)) -> etaReduce (n + 1) t
               | (_, _) -> None
          end
        and etaReduceSpine arg__30 arg__31 =
          begin
          match (arg__30, arg__31)
          with 
               | (n, App (fst, sp))
                   -> begin
                      match etaReduce 0 fst
                      with 
                           | Some (BVar n')
                               -> (n = n') && (etaReduceSpine (n - 1) sp)
                           | _ -> false
                      end
               | (n, nil_) -> true
               | (n, _) -> false
          end;;
        let rec checkTrivial cid =
          begin
          match sgnLookup cid
          with 
               | AbbrevDef (_, _, _, m_, v_, _)
                   -> begin
                      match etaReduce 0 m_
                      with 
                           | Some (Const cid')
                               -> begin
                                    print
                                    (((("DX inserting " ^ (Int.toString cid'))
                                         ^ " = ")
                                        ^ (Int.toString cid))
                                       ^ "\n");
                                    Table.insert imitatesTable (cid', cid)
                                    end
                           | _ -> ()
                      end
               | _ -> ()
          end;;
        let rec travExp arg__32 arg__33 =
          begin
          match (arg__32, arg__33)
          with 
               | (cid, Uni _) -> ()
               | (cid, Pi ((d_, _), b_))
                   -> begin
                        travDec cid d_;travExp cid b_
                        end
               | (cid, Root (h_, s_))
                   -> begin
                        travHead cid h_;travSpine cid s_
                        end
               | (cid, Redex (m_, s_))
                   -> begin
                        travExp cid m_;travSpine cid s_
                        end
               | (cid, Lam (d_, m_))
                   -> begin
                        travDec cid d_;travExp cid m_
                        end
               | (cid, _) -> ()
          end
        and travDec arg__34 arg__35 =
          begin
          match (arg__34, arg__35)
          with 
               | (cid, Dec (_, a_)) -> travExp cid a_
               | (cid, BDec (_, (c, _)))
                   -> begin
                        recordDependency (cid, c);traverse c
                        end
          end
        and travSpine arg__36 arg__37 =
          begin
          match (arg__36, arg__37)
          with 
               | (cid, nil_) -> ()
               | (cid, App (m_, s_))
                   -> begin
                        travExp cid m_;travSpine cid s_
                        end
               | (cid, _) -> ()
          end
        and travHead cid h =
          Option.map
          (function 
                    | n -> begin
                             recordDependency (cid, n);traverse n
                             end)
          (headCID h)
        and traverseDescendants' arg__38 arg__39 =
          begin
          match (arg__38, arg__39)
          with 
               | (cid, ConDec (_, _, _, _, v_, _)) -> travExp cid v_
               | (cid, ConDef (_, _, _, m_, v_, _, _))
                   -> begin
                        travExp cid m_;travExp cid v_
                        end
               | (cid, AbbrevDef (_, _, _, m_, v_, _))
                   -> begin
                        travExp cid m_;travExp cid v_
                        end
               | (cid, _) -> ()
          end
        and traverseDescendants cid =
          traverseDescendants' cid (I.sgnLookup cid)
        and traverse cid =
          let name = conDecName (sgnLookup cid)
            in record_once traverseDescendants cid;;
        let rec initForText () =
          begin
            startClause := None;
            begin
              startSemant := None;
              begin
                Table.clear depTable;
                begin
                  Table.clear recordTable;
                  begin
                    Table.clear imitatesTable;Table.clear replaceTable
                    end
                  
                  end
                
                end
              
              end
            
            end;;
        exception InfixWithImplicitArgs ;;
        let rec appRange f min max = begin
          if min < max then begin
                              f min;appRange f (min + 1) max
                              end else ()
          end;;
        let rec dumpAll (max, first, outputSemant, outputChecker) =
          let streamSemant = TextIO.openOut outputSemant
            in let streamChecker = TextIO.openOut outputChecker
                 in let streamTcb = TextIO.openOut "dumptcb"
                      in let rec waitUntilFalse f = begin
                           if f () then waitUntilFalse f else () end
                           in let rec outputCid cid =
                                let s =
                                  (Print.conDecToString (I.sgnLookup cid)) ^
                                    "\n"
                                  in let s' = begin
                                       if
                                       (cid >= (valOf (! startClause))) &&
                                         (is_def cid)
                                       then begin
                                       if isClause cid then "%clause " ^ s
                                       else s end else s end
                                       in let stream = begin
                                            if cid < (valOf (! startSemant))
                                            then streamTcb else begin
                                            if cid >= (valOf (! startClause))
                                            then streamChecker else
                                            streamSemant end end
                                            in TextIO.output
                                               (stream, s' ^ (fixityDec cid))
                                in begin
                                     appRange checkTrivial 0 max;
                                     begin
                                       appRange traverse first max;
                                       begin
                                         appRange
                                         (function 
                                                   | cid
                                                       -> Table.insert
                                                          recordTable
                                                          (cid, ()))
                                         0
                                         (valOf (! startSemant));
                                         begin
                                           waitUntilFalse isShadowing;
                                           begin
                                             Table.app
                                             IntSyn.rename
                                             replaceTable;
                                             begin
                                               List.app
                                               outputCid
                                               (sortedKeys recordTable);
                                               begin
                                                 TextIO.closeOut streamSemant;
                                                 begin
                                                   TextIO.closeOut
                                                   streamChecker;
                                                   TextIO.closeOut streamTcb
                                                   end
                                                 
                                                 end
                                               
                                               end
                                             
                                             end
                                           
                                           end
                                         
                                         end
                                       
                                       end
                                     
                                     end;;
        let rec dumpText (outputSemant, outputChecker) =
          let max = (fun (r, _) -> r) (I.sgnSize ())
            in let rec correctFixities cid = begin
                 if cid < max then
                 begin
                   let fixity = N.getFixity cid
                     in let imp = I.constImp cid
                          in let name = I.conDecName (I.sgnLookup cid)
                               in let inSemant =
                                    (cid >= (valOf (! startSemant))) &&
                                      (cid < (valOf (! startClause)))
                                    in let makeNonfix =
                                         begin
                                         match (fixity, imp, inSemant)
                                         with 
                                              | (F.Infix _, _, true) -> true
                                              | (F.Infix _, 0, false)
                                                  -> false
                                              | (F.Infix _, _, false)
                                                  -> raise
                                                     InfixWithImplicitArgs
                                              | (_, _, _) -> false
                                         end in begin
                                         if makeNonfix then
                                         N.installFixity (cid, F.nonfix_)
                                         else () end;
                   correctFixities (cid + 1)
                   end
                 else () end
                 in let _ = correctFixities 0
                      in let rec error msg = print (("Error: " ^ msg) ^ "\n")
                           in begin
                              match ! startClause
                              with 
                                   | Some cid
                                       -> try dumpAll
                                              (max, cid, outputSemant,
                                               outputChecker)
                                          with 
                                               | Error msg -> error msg
                                   | None
                                       -> error
                                          "setFlag() has not been called yet\n"
                              end;;
        end;;
    (* currently unused *);;
    (* returns a tuple of the name of the cid and SOME of the shadowing cid if any *);;
    (* returns true if it changed any names *);;
    (* val _ = print ""clearing table...\n"" *);;
    (* Option.mapPartial
                                                    (fn x => (case isShadowedBy x of
                                                    (_, SOME _) => NONE
                                                      | (x, NONE) => SOME x)) *);;
    (* XXX worrying - jcreed 7/05 *);;
    (* print (""DX planning to subtly rename "" ^ Int.toString cid ^ "" to "" ^ x ^ ""\n"");  *);;
    (* problematic shadowing *);;
    (* nonproblematic shadowing - change its name *);;
    (* print (""DX renaming "" ^ Int.toString cid ^ "" to "" ^ newname ^ ""\n""); *);;
    (* val _ = print (""DX processing cid "" ^ Int.toString cid ^ "" which has name ["" ^ name ^ ""].\n"") *);;
    (* print(""DX Recording "" ^ Int.toString cid ^ "".\n"") ; *);;
    (*        val msg = ""DX dep "" ^ Int.toString x ^ "" on "" ^ Int.toString y ^ ""\n"" *);;
    (* val message = ""DX Traversing cid = "" ^ Int.toString cid ^ "" name = "" ^ name ^ ""\n"" *);;
    (* DX *);;
    (* if cid < (valOf(!startSemant)) then () else *);;
    (* DX *);;
    (* DX *);;
    (* DX *);;
    (* val _ = print (""DX startSemant = "" ^ Int.toString(valOf(!startSemant)) ^ ""\n"") *);;
    (* val _ = print (""DX startClause = "" ^ Int.toString(valOf(!startClause)) ^ ""\n"") *);;
    (* val _ = case fixity of F.Infix _ => print (""DX Infix "" ^ Int.toString cid ^ "" "" ^ name ^ "" "" ^ Int.toString imp ^ "" \n"") | _ => () *);;
    (*print (""DX setting nonfix "" ^ Int.toString cid ^ ""\n""); *);;
    let init = init;;
    let initForText = initForText;;
    let dump = dump;;
    let dumpText = dumpText;;
    let setFlag = setFlag;;
    let setEndTcb = setEndTcb;;
    let dumpFlagged = dumpFlagged;;
    let dumpSymTable = dumpSymTable;;
    end;;
(* functor Flit *);;
# 1 "src/flit/flit_.sml.ml"
open! Basis;;
module Flit = (Flit)(struct
                       module Global = Global;;
                       module Word = Word32;;
                       module Pack = PackWord32Little;;
                       module IntSyn = IntSyn;;
                       module Whnf = Whnf;;
                       module Print = Print;;
                       module Names = Names;;
                       module Index = Index;;
                       module Table = IntRedBlackTree;;
                       end);;