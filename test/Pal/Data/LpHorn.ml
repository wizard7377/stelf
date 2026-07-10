(* Positive fragment of first-order logic with natural deduction.
   Ported from twelf/examples/lp_horn/natded.elf.
   Operator declarations: imp with %prec %right 10, and with %prec %right 11.
*)
let lp_horn_nd =
  {|
%sort i
%name i T
%sort o
%name o A
%sort p
%name p P

%term atom {_ p} o
%term and {_ o} {_ o} o
%prec %right 11 and
%term imp {_ o} {_ o} o
%prec %right 10 imp
%term true o
%term forall {_ {_ i} o} o

%sort pf {_ o}
%name pf D
%term andi {{A B}} {_ pf A} {_ pf B} pf (A and B)
%term andel {{A B}} {_ pf (A and B)} pf A
%term ander {{A B}} {_ pf (A and B)} pf B
%term impi {{A B}} {_ {_ pf A} pf B} pf (A imp B)
%term impe {{A B}} {_ pf (A imp B)} {_ pf A} pf B
%term truei pf true
%term foralli {{A}} {_ {a i} pf (A a)} pf (forall A)
%term foralle {{A}} {_ pf (forall A)} {T i} pf (A T)
|}

(* LP-HORN canon: canonical forms for natural deduction proofs.
   Ported from twelf/examples/lp_horn/canon.elf.
   Builds on lp_horn_nd (o, pf, atom, and, imp, true, forall, andi, andel, ander,
                          impi, impe, truei, foralli, foralle).
   Names introduced: can, atm and constructors.
   Omitted: can_impi, can_foralli (require full %block worlds for higher-order premises).
*)
let lp_horn_sources_2 =
  {|
%sort can {A o} {_ pf A}
%name can CN
%sort atm {_ pf _}
%name atm AT

%term can_andi {{A B D E}} {_ can A D} {_ can B E} can (A and B) (andi D E)
%term can_truei {{D}} can true truei
%term can_atm {{P D}} {_ atm D} can (atom P) D

%term atm_andel {{D}} {_ atm D} atm (andel D)
%term atm_ander {{D}} {_ atm D} atm (ander D)
%term atm_impe {{A B D E}} {_ atm D} {_ can B E} atm (impe D E)
%term atm_foralle {{A D T}} {_ atm D} atm (foralle D T)

%worlds () (can _ _) (atm _)
|}

(* LP-HORN conv: conversion to canonical/atomic form.
   Ported from twelf/examples/lp_horn/conv.elf.
   Builds on lp_horn_nd + lp_horn_sources_2 (can, atm in scope).
   Names introduced: whr, tocan, toatm and constructors.
*)
let lp_horn_sources_3 =
  {|
%sort whr {_ pf A} {_ pf A}
%name whr WHR

%term whr_andl {{A B D E}} whr (andel (andi D E)) D
%term whr_andr {{A B D E}} whr (ander (andi D E)) E
%term whr_imp {{A B D E}} whr (impe (impi D) E) (D E)
%term whr_forall {{A D T}} whr (foralle (foralli D) T) (D T)
%term whr_andel {{D D'}} {_ whr D D'} whr (andel D) (andel D')
%term whr_ander {{D D'}} {_ whr D D'} whr (ander D) (ander D')
%term whr_impe {{A B D D' E}} {_ whr D D'} whr (impe D E) (impe D' E)
%term whr_foralle {{A D D' T}} {_ whr D D'} whr (foralle D T) (foralle D' T)

%sort tocan {A o} {_ pf A} {_ pf A}
%name tocan TC
%sort toatm {_ pf A} {_ pf A}
%name toatm TA

%term tc_and {{A B D D1' D2'}} {_ tocan A (andel D) D1'} {_ tocan B (ander D) D2'} tocan (A and B) D (andi D1' D2')
%term tc_imp {{A B D D'}} {_ {u pf A} {_ toatm u u} tocan B (impe D u) (D' u)} tocan (A imp B) D (impi D')
%term tc_true {{D}} tocan true D truei
%term tc_atom {{P D D'}} {_ toatm D D'} tocan (atom P) D D'
%term tc_whr {{A D D' D''}} {_ whr D D'} {_ tocan A D' D''} tocan A D D''

%term ta_atom {{P D}} {_ atm D} toatm D D
%term ta_whr {{D D' D''}} {_ whr D D'} {_ toatm D' D''} toatm D D''
|}
