(* CRARY-LINEAR (syntax-only): linear substructural types.
   Ported from twelf/examples/crary/substruct/linear.elf (syntax block only).
   Type `!` in Twelf = the bang/of-course modality. Trying `!` as identifier verbatim.
   `with` is a keyword in OCaml but it's inside a raw string — should be fine in the parser.
*)
let crary_linear_syntax =
  {|
%sort atom
%sort tp
%sort term

%term atomic {_ atom} tp
%term lolli {_ tp} {_ tp} tp
%term tensor {_ tp} {_ tp} tp
%term with {_ tp} {_ tp} tp
%term plus {_ tp} {_ tp} tp
%term one tp
%term zero tp
%term top tp
%term bang {_ tp} tp

%term llam {_ {_ term} term} term
%term lapp {_ term} {_ term} term

%term tpair {_ term} {_ term} term
%term lett {_ term} {_ {_ term} {_ term} term} term

%term pair {_ term} {_ term} term
%term pi1 {_ term} term
%term pi2 {_ term} term

%term in1 {_ term} term
%term in2 {_ term} term
%term case {_ term} {_ {_ term} term} {_ {_ term} term} term

%term star term
%term leto {_ term} {_ term} term

%term any {_ term} term
%term unit term

%term bang_tm {_ term} term
%term letb {_ term} {_ {_ term} term} term

%term a atom
%term b atom
|}

(* CRARY-LINEAR-atoms: the a/b atoms for linear are declared in crary_linear_syntax above,
   but crary_modal_syntax re-declares its own a/b below.  Those in crary_linear_syntax
   therefore come first and are the ones in scope for CRARY-LINEAR tests.
*)

(* CRARY-LINEAR (linearity sort and basic terms):
   The `linear` family from linear.elf.
*)
let crary_linear_linear =
  {|
%sort linear {_ {_ term} term}
%term linear/var linear ([x] x)
%term linear/llam {{M}} {_ {y term} linear ([x] M x y)} linear ([x] llam ([y] M x y))
%term linear/lapp1 {{M N}} {_ linear ([x] M x)} linear ([x] lapp (M x) N)
%term linear/lapp2 {{M N}} {_ linear ([x] N x)} linear ([x] lapp M (N x))
%term linear/tpair1 {{M N}} {_ linear ([x] M x)} linear ([x] tpair (M x) N)
%term linear/tpair2 {{M N}} {_ linear ([x] N x)} linear ([x] tpair M (N x))
%term linear/pair {{M N}} {_ linear ([x] M x)} {_ linear ([x] N x)} linear ([x] pair (M x) (N x))
%term linear/pi1 {{M}} {_ linear ([x] M x)} linear ([x] pi1 (M x))
%term linear/pi2 {{M}} {_ linear ([x] M x)} linear ([x] pi2 (M x))
%term linear/in1 {{M}} {_ linear ([x] M x)} linear ([x] in1 (M x))
%term linear/in2 {{M}} {_ linear ([x] M x)} linear ([x] in2 (M x))
%term linear/unit linear ([x] unit)
|}

(* CRARY-LINEARD (syntax-only): dual linear type system.
   Ported from twelf/examples/crary/substruct/lineard.elf (syntax only).
   Similar to linear.elf but adds `constant`, `pi` (dependent type), `ulam`/`uapp`.
*)
let crary_lineard_syntax =
  {|
%sort constant
%sort tp
%sort term

%term const {_ constant} {_ term} tp
%term pi {_ tp} {_ {_ term} tp} tp
%term lolli {_ tp} {_ tp} tp
%term tensor {_ tp} {_ tp} tp
%term with {_ tp} {_ tp} tp
%term plus {_ tp} {_ tp} tp
%term one tp
%term zero tp
%term top tp
%term bang {_ tp} tp

%term ulam {_ {_ term} term} term
%term uapp {_ term} {_ term} term

%term llam {_ {_ term} term} term
%term lapp {_ term} {_ term} term

%term tpair {_ term} {_ term} term
%term lett {_ term} {_ {_ term} {_ term} term} term

%term pair {_ term} {_ term} term
%term pi1 {_ term} term
%term pi2 {_ term} term

%term in1 {_ term} term
%term in2 {_ term} term
%term case {_ term} {_ {_ term} term} {_ {_ term} term} term

%term star term
%term leto {_ term} {_ term} term

%term any {_ term} term
%term unit term

%term bang_tm {_ term} term
%term letb {_ term} {_ {_ term} term} term
|}

(* CRARY-MODAL (syntax-only): modal substructural types.
   Ported from twelf/examples/crary/substruct/modal.elf (syntax block only).
   Dropped: `local/bx : local ([x] bx M) = local/closed.` definitional equality form.
*)
let crary_modal_syntax =
  {|
%sort atom
%sort tp
%sort term
%sort exp

%term atomic {_ atom} tp
%term arrow {_ tp} {_ tp} tp
%term box {_ tp} tp
%term diamond {_ tp} tp

%term lam {_ {_ term} term} term
%term app {_ term} {_ term} term

%term bx {_ term} term
%term letbx {_ term} {_ {_ term} term} term

%term di {_ exp} term

%term here {_ term} exp
%term eletbx {_ term} {_ {_ term} exp} exp
%term letdi {_ term} {_ {_ term} exp} exp

%term a atom
%term b atom
|}
