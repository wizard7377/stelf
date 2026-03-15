# Future Plans

While not getting ahead of myself, there are a couple changes I will probably make once I've gotton the rest of the issues down[^1]

## Removing Reserved Syntax

Firstly, remove the `:`, `=`, `->`, `type`.
Of these, the simpler to explain are the first two.
Firstly, let us consider each and every instance where `:` or `=` are used:

1. In a decleration/assertion
2. In a definition
3. Type ascription
4. Lambdas
5. Pi types
The first three of these all have the same solution... keywords!
Namely, we just define three keywords, `%decl`, `%define`, and `%the`.
`%decl NAME TYPE` is the same as `NAME : TYPE` is now.
`%define NAME VALUE` is `NAME = VALUE`, and `%the TYPE VALUE` is `VALUE : TYPE` (`%the nat z`)

We have thus removed the first two.
The next, `type`, is even easier, as it is just `%sort` .
For `->`, and to tie the rest of these together, we need to explain the new system of macros and keywords:

## Macros and Keywords

While Twelf's syntax is quite powerful, it had a number of shortcomings:

1. The arrows `->`, despite being conceptually just aliases, have to be defined as per of the language core
2. The word `type`, oft deseriable in a *metalogic*, is resereved.
3. Poor unicode support
To fix all these problems, we expand on the partial solution of `%abbrev` (forced δ reduction), with parametric abbreviations.

The basic form of these are `%macro [NUM] NAME VALUE`, where
<!-- TODO Finish -->
