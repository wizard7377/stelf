# Style Guide 

> [!NOTE] This list is not exhaustive. Also, a number of these are not yet correctly used.

Avoid names ending in underscores, esspecially if they don't conflict with another name.
Use `snake_case` for lowercase names, and `CamelCase` for uppercase names. The only exception to this is that `Make_` should be used as a prefix for functors, as `Make_HashMap`

A module `Foo` should be of module type `FOO`.
Each library should have a top level interface, `*.mli`.

If there is a module `Foo`, then it should be defined in `Foo.ml`, and its interface should be defined in `FOO.ml`, prefer `Foo.ml` to `foo.ml`, and `FOO.ml` to `Foo_intf.ml` or `foo_intf.ml`.

In this case, the module should look like this 

```ocaml
module type FOO = FOO.FOO
module Foo : FOO = struct 
  (* Implementation here *)
end
```

All module types should be documented 