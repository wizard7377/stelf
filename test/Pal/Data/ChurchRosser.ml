(* Untyped lambda-calculus terms.
   Ported from twelf/examples/church_rosser/lam.elf.
   This is just the term syntax — no reduction or typing.
*)
let church_rosser_lam =
  {|
%sort term
%name term M
%term lam {_ {_ term} term} term
%term app {_ term} {_ term} term
|}

(* CHURCH-ROSSER ord-red: ordinary reduction relations on untyped lambda terms.
   Ported from twelf/examples/church_rosser/ord-red.elf.
   Builds on church_rosser_lam (term/lam/app already in scope).
   Names introduced: -->, id1, step1, -->*, refl/sym/trans/red, <->
*)
let church_rosser_sources_2 =
  {|
%sort --> {_ term} {_ term}
%prec %none 10 -->

%term beta1 {{M1 M2}} (app (lam M1) M2) --> (M1 M2)
%term lm1 {{M M'}} {_ {x term} (M x) --> (M' x)} (lam M) --> (lam M')
%term apl1 {{M1 M1' M2}} {_ M1 --> M1'} (app M1 M2) --> (app M1' M2)
%term apr1 {{M1 M2 M2'}} {_ M2 --> M2'} (app M1 M2) --> (app M1 M2')

%sort -->* {_ term} {_ term}
%prec %none 10 -->*

%term id1 {{M}} M -->* M
%term step1 {{M M' M''}} {_ M --> M'} {_ M' -->* M''} M -->* M''

%sort <-> {_ term} {_ term}
%prec %none 10 <->

%term ord-refl {{M}} M <-> M
%term ord-sym {{M M'}} {_ M' <-> M} M <-> M'
%term ord-trans {{M M' M''}} {_ M <-> M'} {_ M' <-> M''} M <-> M''
%term ord-red {{M M'}} {_ M -->* M'} M <-> M'
|}

(* CHURCH-ROSSER par-red: parallel reduction relations on untyped lambda terms.
   Ported from twelf/examples/church_rosser/par-red.elf.
   Builds on church_rosser_lam (term/lam/app in scope).
   Names introduced: =>, =>*, <=>
   Note: par-beta's first premise is higher-order:
     {x:term}{idx:x=>x} (M1 x idx) => (M1' x idx)
   Simplified here with {{M1 M1'}} implicit for the higher-order functions.
*)
let church_rosser_sources_3 =
  {|
%sort => {_ term} {_ term}
%prec %none 10 =>

%term par-beta {{M2 M2'}} {_ {x term} {_ x => x} (M1 x) => (M1' x)} {_ M2 => M2'} (app (lam M1) M2) => (M1' M2')
%term par-ap {{M1 M1' M2 M2'}} {_ M1 => M1'} {_ M2 => M2'} (app M1 M2) => (app M1' M2')
%term par-lm {{M M'}} {_ {x term} {_ x => x} (M x) => (M' x)} (lam M) => (lam M')

%sort =>* {_ term} {_ term}
%prec %none 10 =>*

%term par-id {{M}} M =>* M
%term par-step {{M M' M''}} {_ M => M'} {_ M' =>* M''} M =>* M''

%sort <=> {_ term} {_ term}
%prec %none 10 <=>

%term par-reduce {{M M'}} {_ M =>* M'} M <=> M'
%term par-expand {{M M'}} {_ M =>* M'} M' <=> M
|}
