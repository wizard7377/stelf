# Grammar

The syntax is as follows:

## Outer Language

The "outer language" (inspired by Isabelle/HOL), is quite simple. 
There are three lexical classes in it, whitespace, certain keywords all starting with `%`, and everything else. 
The list of valid keywords is as follows:
- `%.`: not very useful in the outer language. This signals the start of a section in the outer language 
- `%type NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to declare that `NAME` has type `...` 
- `%decl NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to declare that `NAME` is a term with type `...` 
- `%sort NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to declare that `NAME` is a sort defined as `...`
- `%[...]`, `%[[ ... ]]` etc: Any code that shouldn't appear, a comment 
- `%{ ... }`, `%{{ ... }}` etc: Group outer code together, or have it inline but in a block 
- `%def NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to define `NAME` as `...`
- `%sym NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to declare that `NAME` is a symbol with precedence and associativity defined by `...`
- `%infixl NAME ...`, `%infixr NAME ...`, `%infix NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to declare that `NAME` is an infix operator with precedence and associativity defined by `...`
- `%prefix NAME ...`, `%postfix NAME ...`: where name is a sequence of non-whitespace charecters, and the `...` is any sequeunce of charecters until the next outer language keyword. This is used to declare that `NAME` is a prefix/postfix operator with precedence defined by `...`
- `%( ... )`, `%(( ... ))` etc: Marks a typesetting command

## Inner Languages

There are mutiple different inner languages, each of which has its own syntax.

A couple common things about them:
- A "word" is a sequence of any non-whitespace charecters, except for `%` `{`, `}`, `(`, `)`, `[`, `]`.
- A "keyword" is a word (see previous) that is prefixed by `%` and is not one of the keyword in the outer language. 

### Value Language 

This is the language used by types, terms, and sorts.
1. `[ _ ] ...` (the `_` is literal) marks a "constant lambda", that is, `\_. ...`
2. `[ VAR _ ]` variable lambda with type explicity ommited 
3. `[ VAR ] ...` marks a "variable lambda", that is, `\VAR. ...`
4. `[ VAR TYPE ] ...` also marks a "variable lambda", but with type `TYPE`, that is, `\VAR: TYPE. ...`
5. `[ VAR1 VAR2 VARN TYPE ] ...` is syntatic sugar for `[ VAR1 TYPE ] [ VAR2 TYPE ] ... [ VARN TYPE ] ...`. Note that this *is* syntatic sugar, so that `[A B C _]` is `[A _] [B _] [C _] ...`, where the types may be disjoint
6. `{ _ }` marks a "constant pi", that is, `forall _. ...`
7. `{ VAR _ }` marks a "variable pi" with type explicity ommited, that is, `forall VAR. ...`
8. `{ VAR }` marks a "variable pi", that is, `forall VAR. ...`
9. `{ VAR TYPE }` also marks a "variable pi", but with type `TYPE`, that is, `forall VAR: TYPE. ...`
10. `{ VAR1 VAR2 VARN TYPE }` is syntatic sugar for `{ VAR1 TYPE } { VAR2 TYPE } ... { VARN TYPE } ...`. Note that this *is* syntatic sugar, so that `{A B C _}` is `{A _} {B _} {C _} ...`, where the types may be disjoint
11. `( e0 e1 ... en )` is an application of `e0` to `e1`, ..., `en`. Note that this is left associative, so that `(f x y z)` is `(((f x) y) z)`
12. `%the T X`, coerces `X` to type `T` (this terminology is borrowed from Idris, such that we have `%the nat (succ zero)`)
## Example 

```
%sort type %star %. 
%type nat type %.
The type of natural numbers 
%decl zero nat %.
The zero natural number
%decl succ {_ nat} nat %.
The successor function, which takes a natural number and returns the next one
%sym 0 zero %.
%sym 1 succ zero %.
%sym 2 succ succ zero %.
%type add {_ nat} {_ nat} {_ nat} nat %.
%decl add/zero add zero _A _A %.
%decl add/succ {A B C _} {_ (add A B C)} add (succ A) B (succ C) %.
%query 1 add 1 2 3 %.
```