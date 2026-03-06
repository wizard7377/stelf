open! Basis;;
module ModSyn(ModSyn__0: sig
                         (* Syntax for elaborated modules *)
                         (* Author: Kevin Watkins *)
                         module Global : GLOBAL
                         (*! structure IntSyn' : INTSYN !*)
                         module Names' : NAMES
                         (*! sharing Names'.IntSyn = IntSyn' !*)
                         (*! structure Paths' : PATHS !*)
                         module Origins : ORIGINS
                         (*! sharing Origins.Paths = Paths' !*)
                         module Whnf : WHNF
                         (*! sharing Whnf.IntSyn = IntSyn' !*)
                         module Strict : STRICT
                         (*! sharing Strict.IntSyn = IntSyn' !*)
                         module IntTree : TABLE
                         module HashTable : TABLE
                         end) : MODSYN
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    module Names = Names';;
    (*! structure Paths = Paths' !*);;
    module I = IntSyn;;
    exception Error of string ;;
    type constInfo_ =
      | ConstInfo of
        IntSyn.conDec_ *
        Names.Fixity.fixity *
        (string list * string list)
        option *
        (string * Paths.occConDec option) ;;
    type structInfo_ = | StructInfo of IntSyn.strDec_ ;;
    (* A module consists of:
     1. a map from cids to constant entries containing
          a. a constant declaration entry (IntSyn.ConDec)
          b. the fixity of the constant
          c. the name preference for the constant (if any)
     2. a map from mids to structure entries containing
          a. a structure declaration entry (IntSyn.StrDec)
          b. the namespace of the structure
     3. the top-level namespace of the module *);;
    type nonrec module_ =
      structInfo_
      IntTree.table_ *
      constInfo_
      IntTree.table_ *
      Names.namespace;;
    type nonrec action =
      (IntSyn.cid * (string * Paths.occConDec option)) -> unit;;
    type nonrec transform = (IntSyn.cid * IntSyn.conDec_) -> IntSyn.conDec_;;
    (* invariant: U in nf, result in nf *);;
    let rec mapExpConsts f u_ =
      (let open IntSyn in 
       let rec trExp =
         function 
                  | Uni l_ -> (Uni l_)
                  | Pi ((d_, p_), v_) -> (Pi ((trDec d_, p_), trExp v_))
                  | Root (h_, s_) -> (Root (trHead h_, trSpine s_))
                  | Lam (d_, u_) -> (Lam (trDec d_, trExp u_))
                  | (FgnExp csfe as u_) -> FgnExpStd.Map.apply csfe trExp
       and trDec (Dec (name, v_)) = (Dec (name, trExp v_))
       and trSpine =
         function 
                  | Nil -> Nil
                  | App (u_, s_) -> (App (trExp u_, trSpine s_))
       and trHead =
         function 
                  | BVar n -> (BVar n)
                  | Const cid -> trConst cid
                  | Skonst cid -> trConst cid
                  | Def cid -> trConst cid
                  | NSDef cid -> trConst cid
                  | FgnConst (csid, Condec_)
                      -> (FgnConst (csid, mapConDecConsts f Condec_))
       and trConst cid =
         let cid' = f cid
           in begin
              match IntSyn.sgnLookup cid'
              with 
                   | IntSyn.ConDec _ -> (Const cid')
                   | IntSyn.SkoDec _ -> (Skonst cid')
                   | IntSyn.ConDef _ -> (Def cid')
                   | IntSyn.AbbrevDef _ -> (NSDef cid')
              end
         in Whnf.normalize (trExp u_, IntSyn.id))
    and mapConDecConsts arg__1 arg__2 =
      begin
      match (arg__1, arg__2)
      with 
           | (f, IntSyn.ConDec (name, parent, i, status, v_, l_))
               -> (IntSyn.ConDec
                   (name, parent, i, status, mapExpConsts f v_, l_))
           | (f, IntSyn.ConDef (name, parent, i, u_, v_, l_, Anc))
               -> (IntSyn.ConDef
                   (name, parent, i, mapExpConsts f u_, mapExpConsts f v_,
                    l_, Anc))
           | (f, IntSyn.AbbrevDef (name, parent, i, u_, v_, l_))
               -> (IntSyn.AbbrevDef
                   (name, parent, i, mapExpConsts f u_, mapExpConsts f v_,
                    l_))
           | (f, IntSyn.SkoDec (name, parent, i, v_, l_))
               -> (IntSyn.SkoDec (name, parent, i, mapExpConsts f v_, l_))
      end(* reconstruct Anc?? -fp *);;
    let rec mapStrDecParent f (IntSyn.StrDec (name, parent)) =
      (IntSyn.StrDec (name, f parent));;
    let rec mapConDecParent arg__3 arg__4 =
      begin
      match (arg__3, arg__4)
      with 
           | (f, IntSyn.ConDec (name, parent, i, status, v_, l_))
               -> (IntSyn.ConDec (name, f parent, i, status, v_, l_))
           | (f, IntSyn.ConDef (name, parent, i, u_, v_, l_, Anc))
               -> (IntSyn.ConDef (name, f parent, i, u_, v_, l_, Anc))
           | (f, IntSyn.AbbrevDef (name, parent, i, u_, v_, l_))
               -> (IntSyn.AbbrevDef (name, f parent, i, u_, v_, l_))
           | (f, IntSyn.SkoDec (name, parent, i, v_, l_))
               -> (IntSyn.SkoDec (name, f parent, i, v_, l_))
      end(* reconstruct Anc?? -fp *);;
    let rec strictify =
      function 
               | (IntSyn.AbbrevDef (name, parent, i, u_, v_, type_) as
                   condec)
                   -> try begin
                            Strict.check ((u_, v_), None);
                            (IntSyn.ConDef
                             (name, parent, i, u_, v_, IntSyn.type_,
                              IntSyn.ancestor u_))
                            
                            end
                      with 
                           | Strict.Error _ -> Condec_
               | (IntSyn.AbbrevDef _ as condec) -> Condec_;;
    let rec abbrevify (cid, Condec_) =
      begin
      match Condec_
      with 
           | I.ConDec (name, parent, i, _, v_, l_)
               -> let u_ =
                    Whnf.normalize ((I.Root ((I.Const cid), I.nil_)), I.id)
                    in (I.AbbrevDef (name, parent, i, u_, v_, l_))
           | I.SkoDec (name, parent, i, v_, l_)
               -> let u_ =
                    Whnf.normalize ((I.Root ((I.Skonst cid), I.nil_)), I.id)
                    in (I.AbbrevDef (name, parent, i, u_, v_, l_))
           | I.ConDef (name, parent, i, u_, v_, l_, Anc)
               -> (I.AbbrevDef (name, parent, i, u_, v_, l_))
           | I.AbbrevDef data -> (I.AbbrevDef data)
      end;;
    (* In order to install a module, we walk through the mids in preorder,
     assigning global mids and building up a translation map from local
     mids to global mids.  Then we walk through the cids in dependency
     order, assigning global cids, building up a translation map from
     local to global cids, and replacing the cids contained in the terms
     with their global equivalents.

     NOTE that a module might not be closed with respect to the local
     cids; that is, it might refer to global cids not defined by the
     module.  It is a global invariant that such cids will still be in
     scope whenever a module that refers to them is installed. *);;
    let rec installModule
      ((structTable, constTable, namespace), topOpt, nsOpt, installAction,
       transformConDec)
      =
      let structMap : IntSyn.mid IntTree.table_ = IntTree.new_ 0
        in let constMap : IntSyn.cid IntTree.table_ = IntTree.new_ 0
             in let rec mapStruct mid = valOf (IntTree.lookup structMap mid)
                  in let rec mapParent =
                       function 
                                | None -> topOpt
                                | Some parent -> (Some (mapStruct parent))
                       in let rec mapConst cid =
                            begin
                            match IntTree.lookup constMap cid
                            with 
                                 | None -> cid
                                 | Some cid' -> cid'
                            end
                            in let rec doStruct (mid, StructInfo strdec) =
                                 let strdec' =
                                   mapStrDecParent mapParent strdec
                                   in let mid' = IntSyn.sgnStructAdd strdec'
                                        in let parent =
                                             IntSyn.strDecParent strdec'
                                             in let nsOpt =
                                                  begin
                                                  match parent
                                                  with 
                                                       | None -> nsOpt
                                                       | Some mid
                                                           -> (Some
                                                               (Names.getComponents
                                                                mid))
                                                  end
                                                  in let _ =
                                                       begin
                                                       match nsOpt
                                                       with 
                                                            | Some ns
                                                                -> Names.insertStruct
                                                                   (ns, mid')
                                                            | _ -> ()
                                                       end
                                                       in let _ =
                                                            begin
                                                            match parent
                                                            with 
                                                                 | None
                                                                    -> 
                                                                    Names.installStructName
                                                                    mid'
                                                                 | _ -> ()
                                                            end
                                                            in let ns =
                                                                 Names.newNamespace
                                                                 ()
                                                                 in let _ =
                                                                    Names.installComponents
                                                                    (mid',
                                                                    ns)
                                                                    in 
                                                                    IntTree.insert
                                                                    structMap
                                                                    (mid,
                                                                    mid')
                                 in let rec doConst
                                      (cid, ConstInfo
                                       (Condec_, fixity, namePrefOpt, origin))
                                      =
                                      let condec1 =
                                        mapConDecParent mapParent Condec_
                                        in let condec2 =
                                             mapConDecConsts mapConst condec1
                                             in let condec3 =
                                                  transformConDec
                                                  (cid, condec2)
                                                  in let cid' =
                                                       IntSyn.sgnAdd condec3
                                                       in let parent =
                                                            IntSyn.conDecParent
                                                            condec3
                                                            in let nsOpt =
                                                                 begin
                                                                 match parent
                                                                 with 
                                                                 
                                                                 | None
                                                                    -> nsOpt
                                                                 | Some mid
                                                                    -> 
                                                                    (Some
                                                                    (Names.getComponents
                                                                    mid))
                                                                 end
                                                                 in let _ =
                                                                    begin
                                                                    match nsOpt
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some ns
                                                                    -> 
                                                                    Names.insertConst
                                                                    (ns,
                                                                    cid')
                                                                    | 
                                                                    _ -> ()
                                                                    end
                                                                    in 
                                                                    let _ =
                                                                    begin
                                                                    match parent
                                                                    with 
                                                                    
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    Names.installConstName
                                                                    cid'
                                                                    | 
                                                                    _ -> ()
                                                                    end
                                                                    in 
                                                                    let _ =
                                                                    installAction
                                                                    (cid',
                                                                    origin)
                                                                    in 
                                                                    let _ =
                                                                    begin
                                                                    match fixity
                                                                    with 
                                                                    
                                                                    | 
                                                                    nonfix_
                                                                    -> ()
                                                                    | 
                                                                    _
                                                                    -> 
                                                                    Names.installFixity
                                                                    (cid',
                                                                    fixity)
                                                                    end
                                                                    in 
                                                                    let _ =
                                                                    begin
                                                                    match namePrefOpt
                                                                    with 
                                                                    
                                                                    | 
                                                                    None
                                                                    -> ()
                                                                    | 
                                                                    Some
                                                                    (n1, n2)
                                                                    -> 
                                                                    Names.installNamePref
                                                                    (cid',
                                                                    (n1, n2))
                                                                    end
                                                                    in 
                                                                    IntTree.insert
                                                                    constMap
                                                                    (cid,
                                                                    cid')
                                      in begin
                                           IntTree.app doStruct structTable;
                                           IntTree.app doConst constTable
                                           end;;
    let decToDef x = strictify (abbrevify x);;
    let rec installStruct (strdec, module_, nsOpt, installAction, isDef) =
      let transformConDec = begin
        if isDef then decToDef else function 
                                             | (_, Condec_) -> Condec_
        end
        in let mid = IntSyn.sgnStructAdd strdec
             in let _ =
                  begin
                  match nsOpt
                  with 
                       | Some namespace
                           -> Names.insertStruct (namespace, mid)
                       | _ -> ()
                  end
                  in let _ = Names.installStructName mid
                       in let ns = Names.newNamespace ()
                            in let _ = Names.installComponents (mid, ns)
                                 in installModule
                                    (module_, (Some mid), None,
                                     installAction, transformConDec);;
    let rec installSig (module_, nsOpt, installAction, isDef) =
      let transformConDec = begin
        if isDef then decToDef else function 
                                             | (_, Condec_) -> Condec_
        end
        in installModule
           (module_, None, nsOpt, installAction, transformConDec);;
    let rec abstractModule (namespace, topOpt) =
      let structTable : structInfo_ IntTree.table_ = IntTree.new_ 0
        in let constTable : constInfo_ IntTree.table_ = IntTree.new_ 0
             in let mapParent =
                  begin
                  match topOpt
                  with 
                       | None -> function 
                                          | parent -> parent
                       | Some mid
                           -> function 
                                       | Some mid' -> begin
                                           if mid = mid' then None else
                                           (Some mid') end
                  end
                  in let rec doStruct (_, mid) =
                       let strdec = IntSyn.sgnStructLookup mid
                         in let strdec' = mapStrDecParent mapParent strdec
                              in let ns = Names.getComponents mid
                                   in begin
                                        IntTree.insert
                                        structTable
                                        (mid, (StructInfo strdec'));doNS ns
                                        end
                     and doConst (_, cid) =
                       let Condec_ = IntSyn.sgnLookup cid
                         in let condec' = mapConDecParent mapParent Condec_
                              in let fixity = Names.getFixity cid
                                   in let namePref = Names.getNamePref cid
                                        in let origin =
                                             Origins.originLookup cid
                                             in IntTree.insert
                                                constTable
                                                (cid,
                                                 (ConstInfo
                                                  (condec', fixity, namePref,
                                                   origin)))
                     and doNS ns =
                       begin
                         Names.appStructs doStruct ns;
                         Names.appConsts doConst ns
                         end
                       in begin
                            doNS namespace;
                            (structTable, constTable, namespace)
                            end;;
    let rec instantiateModule (((_, _, namespace) as module_), transform) =
      let transformConDec = transform namespace
        in let mid =
             IntSyn.sgnStructAdd ((IntSyn.StrDec ("wheresubj", None)))
             in let ns = Names.newNamespace ()
                  in let _ = Names.installComponents (mid, ns)
                       in let _ =
                            installModule
                            (module_, (Some mid), None, function 
                                                                 | _ -> (),
                             transformConDec)
                            in abstractModule (ns, (Some mid));;
    open!
      struct
        let defList : string list ref = ref [];;
        let defCount : int ref = ref 0;;
        let defs : module_ HashTable.table_ = HashTable.new_ 4096;;
        let rec defsClear () = HashTable.clear defs;;
        let defsInsert = HashTable.insertShadow defs;;
        let defsLookup = HashTable.lookup defs;;
        let defsDelete = HashTable.delete defs;;
        end;;
    let rec reset () =
      begin
        defList := [];begin
                        defCount := 0;defsClear ()
                        end
        end;;
    let rec resetFrom mark =
      let rec ct (l, i) = begin
        if i <= mark then l else
        let (h :: t) = l in begin
                              defsDelete h;ct (t, i - 1)
                              end
        end
        in begin
             defList := (ct (! defList, ! defCount));defCount := mark
             end;;
    let rec sigDefSize () = ! defCount;;
    let rec installSigDef (id, module_) =
      begin
      match defsInsert (id, module_)
      with 
           | None
               -> begin
                    defList := ((id :: ! defList));
                    defCount := ((! defCount) + 1)
                    end
           | Some entry
               -> begin
                    raise
                    ((Error
                      (("Shadowing: A signature named " ^ id) ^
                         "\nhas already been declared")));
                    begin
                      defsInsert entry;()
                      end
                    
                    end
      end;;
    let lookupSigDef = defsLookup;;
    end;;