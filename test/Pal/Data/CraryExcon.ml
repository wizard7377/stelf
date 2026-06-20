(* Explicit contexts in LF: types, expressions, and natural numbers.
   Ported from twelf/examples/crary/explicit/excon.elf (first part only —
   typing rules and nat up through leq).
*)
let crary_excon =
  {|
%sort tp
%sort exp

%term o tp
%term p {_ exp} tp
%term pi {_ tp} {_ {_ exp} tp} tp

%term b exp
%term lam {_ tp} {_ {_ exp} exp} exp
%term app {_ exp} {_ exp} exp

%sort of {_ exp} {_ tp}
%term of/b of b o
%term of/lam {{A B M}} {_ {x exp} {_ of x A} of (M x) (B x)} of (lam A M) (pi A B)
%term of/app {{A B M N}} {_ of M (pi A B)} {_ of N A} of (app M N) (B N)

%sort nat
%term 0 nat
%term s {_ nat} nat

%sort nat-eq {_ nat} {_ nat}
%term nat-eq/i {{N}} nat-eq N N

%sort leq {_ nat} {_ nat}
%term leq/z {{N}} leq 0 N
%term leq/s {{N1 N2}} %if (leq (s N1) (s N2)) %<- (leq N1 N2)
|}

(* CRARY-EXCON-REV: excon-rev.elf (explicit contexts, reversed variant)
   Ported from twelf/examples/crary/explicit/excon-rev.elf (syntax-only chunk).
   The `-` family (isvar dependency decl) is a Twelf quirk; omitted.
*)
let crary_excon_rev_syntax =
  {|
%sort tp
%sort exp

%term o tp
%term p {_ exp} tp
%term pi {_ tp} {_ {_ exp} tp} tp

%term b exp
%term lam {_ tp} {_ {_ exp} exp} exp
%term app {_ exp} {_ exp} exp

%sort of {_ exp} {_ tp}
%term of/b of b o
%term of/lam {{A B M}} {_ {x exp} {_ of x A} of (M x) (B x)} of (lam A M) (pi A B)
%term of/app {{A B M N}} {_ of M (pi A B)} {_ of N A} of (app M N) (B N)

%sort nat
%term 0 nat
%term s {_ nat} nat

%sort nat-eq {_ nat} {_ nat}
%term nat-eq/i {{N}} nat-eq N N

%sort lt {_ nat} {_ nat}
%term lt/z {{N}} lt 0 (s N)
%term lt/s {{N1 N2}} %if (lt (s N1) (s N2)) %<- (lt N1 N2)

%sort ctx
%term nil ctx
%term cons {_ ctx} {_ exp} {_ tp} ctx
|}
