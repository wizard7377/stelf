(* Direct-style CPS BNF term syntax.
   Ported from twelf/examples/cpsocc/dsBNF.elf.
   Simple type declarations only — no infix operators.
*)
let cpsocc_dsbnf =
  {|
%sort droot
%name droot DROOT
%sort dexp
%name dexp DEXP
%sort dtriv
%name dtriv DTRIV

%term dexp->droot {_ dexp} droot
%term dapp {_ dexp} {_ dexp} dexp
%term dtriv->dexp {_ dtriv} dexp
%term dlam {_ {_ dtriv} droot} dtriv
|}

(* CPSOCC cpsBNF: BNF of continuation-passing style terms.
   Ported from twelf/examples/cpsocc/cpsBNF.elf.
   Builds on cpsocc_dsbnf (droot/dexp/dtriv already in scope).
   Fresh names introduced: croot, cexp, ctriv, ccont, klam, capp, cret, xlam, vlam.
   %name hints omitted (not needed for test correctness).
*)
let cpsocc_cpsBNF =
  {|
%sort croot
%sort cexp
%sort ctriv
%sort ccont
%term klam {_ {_ ccont} cexp} croot
%term capp {_ ctriv} {_ ctriv} {_ ccont} cexp
%term cret {_ ccont} {_ ctriv} cexp
%term xlam {_ {_ ctriv} croot} ctriv
%term vlam {_ {_ ctriv} cexp} ccont
|}
