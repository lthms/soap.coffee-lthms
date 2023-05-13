---
published: 2020-12-10
modified: 2023-04-29
tags: ['coq', 'ocaml', 'coqffi']
abstract: |
    For each entry of a cmi file, coqffi tries to generate an equivalent (from
    the extraction mechanism perspective) Coq definition. In this article, we
    walk through how coqffi works.
---

# `coqffi.1.0.0` In A Nutshell

For each entry of a `cmi` file (a *compiled* `mli` file), `coqffi`
tries to generate an equivalent (from the extraction mechanism
perspective) Coq definition. In this article, we walk through how
`coqffi` works.

Note that we do not dive into the vernacular commands `coqffi`
generates. They are of no concern for users of `coqffi`.

## Getting Started

### Requirements

The latest version of `coqffi` (`1.0.0~beta8`)
is compatible with OCaml `4.08` up to `4.14`, and Coq `8.12` up top
`8.13`.  If you want to use `coqffi`, but have incompatible
requirements of your own, feel free to
[submit an issue](https://github.com/coq-community/coqffi/issues).

### Installing `coqffi`

The recommended way to install `coqffi` is through the
[Opam Coq Archive](https://coq.inria.fr/opam/www), in the `released`
repository.  If you haven’t activated this repository yet, you can use the
following bash command.

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

Then, installing `coqffi` is as simple as

```bash
opam install coq-coqffi
```

You can also get the source from [the upstream `git`
repository](https://github.com/coq-community/coqffi). The `README` provides the
necessary pieces of information to build it from source.

### Additional Dependencies

One major difference between Coq and OCaml is that the former is pure,
while the latter is not. Impurity can be modeled in pure languages,
and Coq does not lack of frameworks in this respect. `coqffi` currently
supports two of them:
[`coq-simple-io`](https://github.com/Lysxia/coq-simple-io) and
[FreeSpec](https://github.com/ANSSI-FR/FreeSpec). It is also possible to use it
with [Interaction Trees](https://github.com/DeepSpec/InteractionTrees), albeit
in a less direct manner.

### Primitive Types

`coqffi` supports a set of primitive types, *i.e.*, a set of OCaml
types for which it knows an equivalent type in Coq. The list is the
following (the Coq types are fully qualified in the table, but not in
the generated Coq module as the necessary `Import` statement are
generated too).

| OCaml type        | Coq type                      |
| ----------------- | ----------------------------- |
| `bool`{.ocaml}            | `Coq.Init.Datatypes.bool`     |
| `char`{.ocaml}            | `Coq.Strings.Ascii.ascii`     |
| `int`{.ocaml}             | `CoqFFI.Data.Int.i63`         |
| `'a list`{.ocaml}         | `Coq.Init.Datatypes.list a`   |
| `'a Seq.t`{.ocaml}        | `CoqFFI.Data.Seq.t`           |
| `'a option`{.ocaml}       | `Coq.Init.Datatypes.option a` |
| `('a, 'e) result`{.ocaml} | `Coq.Init.Datatypes.sum`      |
| `string`{.ocaml}          | `Coq.Strings.String.string`   |
| `unit`{.ocaml}            | `Coq.Init.Datatypes.unit`     |
| `exn`{.ocaml}             | `CoqFFI.Exn`                  |

The `i63`{.coq} type is introduced by the `CoqFFI`{.coq} theory to provide
signed primitive integers to Coq users. They are implemented on top of the
(unsigned) Coq native integers introduced in Coq `8.13`. The `i63` type will be
deprecated once the support for [signed primitive
integers](https://github.com/coq/coq/pull/13559) is implemented[^compat].

[^compat]: This is actually one of the sources of incompatibilities of `coqffi`
    with most recent versions of Coq.

When processing the entries of a given interface model, `coqffi` will
check that they only use these types, or types introduced by the
interface module itself.

Sometimes, you may encounter a situation where you have two interface
modules `b.mli` and `b.mli`, such that `b.mli` uses a type introduced
in `a.mli`.  To deal with this scenario, you can use the `--witness`
flag to generate `A.v`.  This will tell `coqffi` to also generate
`A.ffi`; this file can then be used when generating `B.v` thanks to
the `-I` option.  Furthermore, for `B.v` to compile the `--require`
option needs to be used to ensure the `A` Coq library (`A.v`) is
required.

To give a more concrete example, given ~a.mli~

```ocaml
type t
```

and `b.mli`

```ocaml
type a = A.t
```

To generate `A.v`, we can use the following commands:

```bash
ocamlc a.mli
coqffi --witness -o A.v a.cmi
```

Which would generate the following axiom for `t`.

```coq
Axiom t : Type.
```

Then, generating `B.v` can be achieved as follows:

```bash
ocamlc b.mli
coqffi -I A.ffi -ftransparent-types -r A -o B.v b.cmi
```

which results in the following output for `v`:

```coq
Require A.

Definition u : Type := A.t.
```

## Code Generation

`coqffi` distinguishes five types of entries: types, pure values,
impure primitives, asynchronous primitives, exceptions, and
modules. We now discuss how each one of them is handled.

### Types

By default, `coqffi` generates axiomatized definitions for each type defined in
a `.cmi` file. This means that `type t`{.ocaml} becomes `Axiom t : Type`{.coq}.
Polymorphism is supported, *i.e.*, `type 'a t`{.ocaml} becomes `Axiom t :
forall (a : Type), Type`{.coq}.

It is possible to provide a “model” for a type using the `coq_model`
annotation, for instance for reasoning purposes. For instance, we can specify
that a type is equivalent to a `list`.

```ocaml
type 'a t [@@coq_model "list"]
```

This generates the following Coq definition.

```coq
Definition t : forall (a : Type), Type := list.
```

It is important to be careful when using the =coq_model= annotation. More
precisely, the fact that `t` is a `list` in the “Coq universe” shall not be
used while the implementation phase, only the verification phase.

Unamed polymorphic type parameters are also supported. In presence of
such parameters, `coqffi` will find it a name that is not already
used. For instance,

```ocaml
type (_, 'a) ast
```

becomes

```coq
Axiom ast : forall (b : Type) (a : Type), Type.
```

Finally, `coqffi` has got an experimental feature called `transparent-types`
(enabled by using the `-ftransparent-types` command-line argument). If the type
definition is given in the module interface, then `coqffi` tries to generates
an equivalent definition in Coq. For instance,

```ocaml
type 'a llist =
  | LCons of 'a * (unit -> 'a llist)
  | LNil
```

becomes

```coq
Inductive llist (a : Type) : Type :=
| LCons (x0 : a) (x1 : unit -> llist a) : llist a
| LNil : llist a.
```

Mutually recursive types are supported, so

```ocaml
type even = Zero | ESucc of odd
and odd = OSucc of even
```

becomes

```coq
Inductive odd : Type :=
| OSucc (x0 : even) : odd
with even : Type :=
| Zero : even
| ESucc (x0 : odd) : even.
```

Besides, `coqffi` supports alias types, as suggested in this write-up
when we discuss witness files.

The `transparent-types` feature is **experimental**, and is currently
limited to variant types. It notably does not support records. Besides, it may
generate incorrect Coq types, because it does not check whether or not the
[positivity
condition](https://coq.inria.fr/refman/language/core/inductive.html#positivity-condition)
is satisfied.

### Pure values

`coqffi` decides whether or not a given OCaml values is pure or impure
with the following heuristics:

- Constants are pure
- Functions are impure by default
- Functions with a `coq_model` annotation are pure
- Functions marked with the `pure` annotation are pure
- If the `pure-module` feature is enabled (`-fpure-module`), then synchronous
  functions (which do not live inside the
  [~Lwt~](https://ocsigen.org/lwt/5.3.0/manual/manual) monad) are pure

Similarly to types, `coqffi` generates axioms (or definitions, if the
`coq_model` annotation is used) for pure values. Then,

```ocaml
val unpack : string -> (char * string) option [@@pure]
```

becomes

```ocaml
Axiom unpack : string -> option (ascii * string).
```

Polymorphic values are supported.

```ocaml
val map : ('a -> 'b) -> 'a list -> 'b list [@@pure]
```

becomes

```coq
Axiom map : forall (a : Type) (b : Type), (a -> b) -> list a -> list b.
```

Again, unamed polymorphic type are supported, so

```ocaml
val ast_to_string : _ ast -> string [@@pure]
```

becomes

```coq
Axiom ast_to_string : forall (a : Type), string.
```

### Impure Primitives

`coqffi` reserves a special treatment for /impure/ OCaml functions.
Impurity is usually handled in pure programming languages by means of
monads, and `coqffi` is no exception to the rule.

Given the set of impure primitives declared in an interface module,
`coqffi` will (1) generate a typeclass which gathers these primitives,
and (2) generate instances of this typeclass for supported backends.

We illustrate the rest of this section with the following impure
primitives.

```ocaml
val echo : string -> unit
val scan : unit -> string
```

where `echo` allows writing something the standard output, and `scan`
to read the standard input.

Assuming the processed module interface is named `console.mli`, the
following Coq typeclass is generated.

```coq
Class MonadConsole (m : Type -> Type) := { echo : string -> m unit
                                         ; scan : unit -> m string
                                         }.
```

Using this typeclass and with the additional support of an additional
`Monad` typeclass, we can specify impure computations which interacts
with the console. For instance, with the support of `ExtLib`, one can
write.

```coq
Definition pipe `{Monad m, MonadConsole m} : m unit :=
  let* msg := scan () in
  echo msg.
```

There is no canonical way to model impurity in Coq, but over the years
several frameworks have been released to tackle this challenge.

`coqffi` provides three features related to impure primitives.

#### `simple-io`

When this feature is enabled, `coqffi` generates an instance of the
typeclass for the =IO= monad introduced in the `coq-simple-io` package

```coq
Axiom io_echo : string -> IO unit.
Axiom io_scan : unit -> IO string.

Instance IO_MonadConsole : MonadConsole IO := { echo := io_echo
                                              ; scan := io_scan
                                              }.
```

It is enabled by default, but can be disabled using the
`-fno-simple-io` command-line argument.

#### `interface`

When this feature is enabled, `coqffi` generates an inductive type which
describes the set of primitives available, to be used with frameworks like
[FreeSpec](https://github.com/lthms/FreeSpec) or [Interactions
Trees](https://github.com/DeepSpec/InteractionTrees).

```coq
Inductive CONSOLE : Type -> Type :=
| Echo : string -> CONSOLE unit
| Scan : unit -> CONSOLE string.

Definition inj_echo `{Inject CONSOLE m} (x0 : string) : m unit :=
  inject (Echo x0).

Definition inj_scan `{Inject CONSOLE m} (x0 : unit) : m string :=
  inject (Scan x0).

Instance Inject_MonadConsole `{Inject CONSOLE m} : MonadConsole m :=
  { echo := inj_echo
  ; scan := inj_scan
  }.
```

Providing an instance of the form `forall i, Inject i M`{.coq} is enough for
your monad `M` to be compatible with this feature[^example].

[^example]: See for instance [how FreeSpec implements
    it](https://github.com/lthms/FreeSpec/blob/master/theories/FFI/FFI.v)).

#### `freespec`

When this feature in enabled, `coqffi` generates a semantics for the
inductive type generated by the `interface` feature.

```coq
Axiom unsafe_echo : string -> unit.
Axiom unsafe_scan : uint -> string.

Definition console_unsafe_semantics : semantics CONSOLE :=
  bootstrap (fun a e =>
    local match e in CONSOLE a return a with
          | Echo x0 => unsafe_echo x0
          | Scan x0 => unsafe_scan x0
          end).
```

### Asynchronous Primitives

`coqffi` also reserves a special treatment for *asynchronous*
primitives —*i.e.*, functions which live inside the `Lwt` monad— when
the `lwt` feature is enabled.

The treatment is very analoguous to the one for impure primitives: (1)
a typeclass is generated (with the `_Async` suffix), and (2) an
instance for the `Lwt` monad is generated. Besides, an instance for
the “synchronous” primitives is also generated for `Lwt`. If the
`interface` feature is enabled, an interface datatype is generated,
which means you can potentially use Coq to reason about your
asynchronous programs (using FreeSpec and alike, although the
interleaving of asynchronous programs in not yet supported in
FreeSpec).

By default, the type of the `Lwt` monad is `Lwt.t`. You can override
this setting using the `--lwt-alias` option.  This can be useful when
you are using an alias type in place of `Lwt.t`.

### Exceptions

OCaml features an exception mechanism. Developers can define their
own exceptions using the `exception` keyword, whose syntax is similar
to constructors definition. For instance,

```ocaml
exception Foo of int * bool
```

introduces a new exception `Foo` which takes two parameters of type `int`{.ocaml} and
`bool`{.ocaml}. `Foo (x, y)` constructs of value of type `exn`{.ocaml}.

For each new exceptions introduced in an OCaml module, `coqffi`
generates (1) a so-called “proxy type,” and (2) conversion functions
to and from this type.

Coming back to our example, the “proxy type” generates by `coqffi` is

```coq
Inductive FooExn : Type :=
| MakeFooExn (x0 : i63) (x1 : bool) : FooExn.
```

Then, `coqffi` generates conversion functions.

```coq
Axiom exn_of_foo : FooExn -> exn.
Axiom foo_of_exn : exn -> option FooExn.
```

Besides, `coqffi` also generates an instance for the `Exn` typeclass
provided by the `CoqFFI` theory:

```coq
Instance FooExn_Exn : Exn FooExn :=
  { to_exn := exn_of_foo
  ; of_exn := foo_of_exn
  }.
```

Under the hood, `exn`{.ocaml} is an
[extensible
datatype](https://caml.inria.fr/pub/docs/manual-ocaml/extensiblevariants.html),
and how `coqffi` supports it will probably be generalized in future releases.

Finally, `coqffi` has a minimal support for functions which may raise
exceptions. Since OCaml type system does not allow to identify such
functions, they need to be annotated explicitely, using the
=may_raise= annotation. In such a case, `coqffi` will change the
return type of the function to use the =sum= Coq inductive type.

For instance,

```ocaml
val from_option : 'a option -> 'a [@@may_raise] [@@pure]
```

becomes

```coq
Axiom from_option : forall (a : Type), option a -> sum a exn.
```

### Modules

Lastly, `coqffi` supports OCaml modules described within `mli` files,
when they are specify as `module T : sig ... end`{.ocaml}. For instance,

```ocaml
module T : sig
  type t

  val to_string : t -> string [@@pure]
end
```

becomes

```coq
Module T.
  Axiom t : Type.

  Axiom to_string : t -> string.
End T.
```

As of now, the following construction is unfortunately *not*
supported, and will be ignored by `coqffi`:

```ocaml
module S = sig
  type t

  val to_string : t -> string [@@pure]
end

module T : S
```

## Moving Forward

`coqffi` comes with a comprehensive man page. In addition, the
interested reader can proceed to the next article of this series,
which explains how [`coqffi` can be used to easily implement an echo
server in Coq](/posts/CoqffiEcho.html).
