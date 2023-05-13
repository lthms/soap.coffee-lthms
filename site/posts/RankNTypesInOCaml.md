---
published: 2022-08-07
modified: 2022-08-12
tags: ['ocaml']
abstract: |
    In OCaml, it is not possible to write a function whose argument is a
    polymorphic function. Trying to write such a function results in the
    type-checker complaining back at you. The trick to be able to write such a
    function is to use records.
---

# Writing a Function Whose Argument is a Polymorphic Function in OCaml

In OCaml, it is not possible to write a function whose argument is a
polymorphic function. Trying to write such a function results in the
type-checker complaining back at you.

```ocaml
let foo (type a b) id (x : a) (y : b) = (id x, id y)
```

```
Line 1, characters 50-51:
1 | let foo (type a b) id (x : a) (y : b) = (id x, id y);;
                                                      ^
Error: This expression has type b but an expression was expected
of type a
```

When OCaml tries to type-check `foo`{.ocaml}, it infers `id`{.ocaml} expects an
argument of type `a`{.ocaml} because of `id x`{.ocaml}, then fails when trying
to type-check `id y`{.ocaml}.

The trick to be able to write `foo`{.ocaml} is to use records. Indeed, while
the argument of a function cannot be polymorphic, the field of a record can.
This effectively makes it possible to write `foo`{.ocaml}, at the cost of a
level of indirection.

```ocaml
type id = {id : 'a. 'a -> 'a}

let foo {id} x y = (id x, id y)
```

From a runtime perspective, it is possible to tell OCaml to remove the
introduced indirection with the `unboxed`{.ocaml} annotation. There is nothing
we can do in the source, though. We need to destruct `id`{.ocaml} in
`foo`{.ocaml}, and we need to construct it at its call-site.

```ocaml
g {id = fun x -> x}
```

As a consequence, this solution is not a silver bullet, but it is an option
that is worth considering if, *e.g.*, it allows to export a cleaner API to the
consumer of a module. Personally, I have been considering this trick recently
to remove the need for a library to be implemented as a functor.
