= Future Plans

#align(center, [
  Note that all changes presented here are proposals, and are not yet implemented.
])
While not getting ahead of myself, there are a couple changes I will probably make once I've gotton the rest of the issues down#footnote[Whenever that may be]

== Removing Reserved Syntax

Firstly, remove the `:`, `=`, `->`, `type`.
Of these, the simpler to explain are the first two.
Firstly, let us consider each and every instance where `:` or `=` are used:

1. In a decleration/assertion
2. In a definition
3. Type ascription
4. #sym.Lambda binders
5. #sym.Pi types
The first three of these all have the same solution... keywords!
Namely, we just define three keywords, `%decl`, `%define`, and `%the`.
`%decl NAME TYPE` is the same as `NAME : TYPE` is now.
`%define NAME VALUE` is `NAME = VALUE`, and `%the TYPE VALUE` is `VALUE : TYPE` (`%the nat z`)

We have thus removed the first two.
The next, `type`, is even easier, as it is just `%sort` .
For `->`, and to tie the rest of these together, we need to explain the new system of macros and keywords:

== Macros and Keywords

While Twelf's syntax is quite powerful, it had a number of shortcomings:

1. The arrows `->`, despite being conceptually just aliases, have to be defined as per of the language core
2. The word `type`, oft deseriable in a *metalogic*, is resereved.
3. Poor unicode support
To fix all these problems, we expand on the partial solution of `%abbrev` (forced δ reduction), with parametric abbreviations.

The basic form of these are `%macro NAME [NUM] [CONTEXT] (VALUE)`, where context is either `kind` (the default) or `value`, and where if `NAME` does not start with `0-9`, and if `NUM` is not provided, then `NUM` defaults to `0`.
The `NUM` is the number of parameters, and the `VALUE` is the body of the macro, where the parameters are denototated by keywords `%1`, `%2`, and so on, including double digits#footnote[Though why you'd need 10 parameters is beyond me].

Then, every usage of `NAME` must contain `NUM` or more instance of application. 
The first `NUM` arguments are substituted into the body, and then the macro is expanded (this happens before typechecking).
The context is needed to make sure that `VALUE` is parsed correctly. 
The way we define the syntax for macros is that if `CONTEXT` is `kind`, then `VALUE` is a AST of kinds and variables of `%1`, which may appear anywhere. 
Similarly, if `CONTEXT` is `value`, then `VALUE` is an AST of terms and variables of `%1`, which may appear anywhere.

This allows us to define `->` as a macro, `%macro kind 2 -> ({_ : %1} %2)`, and `type` as `%macro kind 0 type %sort`, and so on.

=== Usage Notes 

Given that `NUM` defines the arity of a macro, it seems quite reasonable that this is the best possible usage of macros: 
``` 
%macro 2 → ({_ : %1} %2)
%macro 0 sort %sort
%type ℕ sort
%type ℕ/0 ℕ
%type ℕ/S ℕ → ℕ
%macro 0 nat ℕ
%macro 0 nat/zero ℕ/0
%macro 1 nat/succ (ℕ/S %1) 
```

However, while this does work, `nat/succ` is overly restrictive. 
Namely, by performaing a simple transformation, we can transform it into `%macro 0 nat/succ ℕ/S`. 
Not only is this simpler, but it also allows us to use `nat/succ` as an function, which we can't do with the first definition (it would be under applied)

== Lexical Anaylisis, Simplicity and Unicode

Another change is to the lexer and parser.
The major change is making the grammar and lexicon simpler, and with less keywords.
To do this, we divide the syntax conceptually into "sublanguages".
The "toplevel" sublaungage, which we start in, has only two syntactic groups predefined, whitespace and non-whitespace strings. 
Each non-whitespace string must start with exactly one `%`, which introduces all special symbols here. 

Each one of the keywords must then be a valid directive, for instance, `%type`. 
Each of these directives has arguements, which are parsed according to the directive.
For instance, `%type` takes two arguements, a name and a type, so we switch to parsing a name and a type. 

What is the conceptual grouping, then? 
We define that each "sub-language" be unambiguously parsable as a unit, and to do be able to do with only one token of lookahead.

