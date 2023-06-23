---
published: 2023-06-20
tags:
- ocaml
abstract: |
    We show how it is possible to use `dmap` to implement extensible records
    (that is, records which can be extended with new fields after they have
    been defined) in OCaml.
---

# Extensible Records in OCaml Using `dmap`

[`dmap`](https://ocaml.org/p/dmap/latest/) is a library to create and
manipulate heterogeneous maps. It features a very straightforward API which
leverages the common trick of tagging the type of the keys with a parameter
specifying the types of the associated values[^gadt]. That is, given `'a
key`{.ocaml} the type of keys of a heterogeneous map `t`{.ocaml}, then the
value associated to a key `k`{.ocaml} of type `bool key`{.ocaml} is expected to
be of type `bool`{.ocaml}.

[^gadt]: This article assumes readers are familiar with GADTs.

In this write-up, we show how it is possible to use `dmap` to implement
extensible records (that is, records which can be extended with new fields
after they have been defined) in OCaml. I have also published on GitHub [a
repository containing the implementation presented in this
article](https://github.com/lthms/extensible-records-minimal). While `dmap` is
far from being the only available solution for this use case[^sota], it is the
one I happened to use for implementing a “plugin system” in a library where
each plugin can manipulate a shared state in a type-safe way.

[^sota]: For heterogeneous maps, [`gmap`](https://ocaml.org/p/gmap/latest) is
    apparently a popular alternative, and so is
    [`hmap`](https://ocaml.org/p/hmap/latest). For extensible records,
    [`orec`](https://ocaml.org/p/orec/latest) looks like a very interesting
    library I should probably take a long look at.

## Encoding Extensible Records

The (simplified) module type of a heterogeneous map built using `dmap` is as
follows.

```ocaml
module type S = sig
  type t
  
  type 'a key

  type binding = Binding : 'a key * 'a -> binding

  val empty : t

  val add : 'a key -> 'a -> t -> t

  val find_opt : 'a key -> t -> 'a option

  val fold_left : ('a -> binding -> a) -> 'a -> t -> 'a
end
```

The use case for heterogeneous maps I’ve been interested in recently is
encoding records. More precisely, constructors of keys encode fields containing
collections of values. In such approach, a constructor `Foo : int key`{.ocaml}
encodes a field of type `int option`, while a constructor `Bar : string -> bool
key`{.ocaml} encodes a field of type `bool StringMap.t`. That is, the
heterogeneous map `HMap.t`, such as

```ocaml
type _ key = Foo : int key | Bar : string -> bool key

module HMap : S with type 'a key  = 'a key
```

can be used to encode values of a record type

```ocaml
type t = {
  foo : int option;
  bar : bool StringMap.t;
}
```

as the following conversion functions demonstrates.

```ocaml
let of_record {foo; bar} =
  let res = HMap.empty in
  let res = HMap.add Foo foo res in
  StringMap.fold_left
    (fun res (key, value) -> HMap.add (Bar key) value res)
    res
    bar

let of_hmap map =
  {
    foo = HMap.find_opt Foo map;
    bar = HMap.fold_left
            (fun smap (Binding binding) ->
               match binding with
               | (Bar k, v) -> StringMap.add k v smap
               | _ -> smap)
            StringMap.empty
            map;
  }
```

As a consequence, to construct a heterogeneous map whose type of keys is
extensible is a way to get extensible records in OCaml.

To that end, `dmap` only asks for a function to compare two arbitrary keys.
More precisely, given the type

```ocaml
type _ key = ..
```

the challenge is to write the function `compare` of type

```ocaml
val compare : 'a key -> 'b key -> ('a, 'b) Dmap.cmp
```

with `Dmap.cmp`{.ocaml} being defined[^cmp] as

[^cmp]: This definition of `cmp`{.ocaml} enforces that two keys can only be
    equal if and only if the values associated to them are of the same type.

```ocaml
type (_, _) cmp =
  | Lt : ('a, 'b) cmp
  | Eq  : ('a, 'a) cmp
  | Gt : ('a, 'b) cmp
```

## The Solution

To use extensible types in this kind of setting, the trick I am aware of is to
use a registration mechanism[^error-monad]. 

[^error-monad]: For instance, this is what the `tezos-error-monad` package is
    using for being able to [print the values of its extensible error
    type](https://ocaml.org/p/tezos-error-monad/13.0/doc/Tezos_error_monad/Error_monad/index.html#val-register_error_kind).

The `compare`{.ocaml} function will work as follows.

1. We assign an integer to each constructor of the type `key`{.ocaml}.
2. We compare these integers when the arguments of `compare` are constructed
   from different constructors.
3. We implement one comparison function per constructors, to be called when the
   two arguments of `compare` are the same.

The exercise is being made a bit more complicated than what the previous
paragraph suggests due to the fact that both `key` and `cmp` are GADTs. As a
consequence, the rest of the article will proceed as follows. First, we will
implement the overall logic of the `compare`{.ocaml} function implemented with
a registration mechanism, and only then will we tackle the OCaml compiler
errors GADTs so often bring.

### Step 1: Forget About GADTs

To implement our registration mechanism, we rely on a good old reference to a
list[^encapsulation]. The position of a registered object within the list will
determine the integer attributed to it.

[^encapsulation]: It is a good idea to hide this implementation “details”
    behind a nice API, using a `mli` file.

```ocaml
let registered_keys = ref []

let register_key key =
  registered_keys := key :: !registered_keys
```

In this list, we store a collection of first-class modules which provide
us everything we need to compare two `'a key`{.ocaml} values obtained from the
same constructors.

```ocaml
module type KEY = sig
  type t

  val proj : 'a key -> t option
  val compare : t -> t -> int
end
```

The type `t`{.ocaml} of the module type `KEY`{.ocaml} is the type of one
constructor’s arguments. The simplest definition of `t`{.ocaml} is
`unit`{.ocaml}, which means the field encoded with the related constructor
points to a singleton value (as `foo`{.ocaml} did in the previous section).

However, it is also possible to have keys’ constructors taking arguments, which
would translate into a field pointing to collections of value. This was the case
for `bar`, which was pointing to a mapping of strings to booleans.

The `compare` function will consist in iterating over the first-class modules
registered in `registered_keys`, in order to determine to which ones the two
arguments belong to.

This means that considering a call `compare left right`, for each first-class module
of `registered_keys`, either

1. both `left` and `right` have not yet been associated to a first-class module,
2. or `left` has, but `right hasn’t
3. or `right` has, but `left` hasn’t
4. or both `left` and `right have been associated to a first-class module.

Only when the fourth stage has been reached can we provide the expected result
of `compare`, whose type we have simplified in this section to return a `int`
instead of the GADT `Dmap.cmp`.

To encode these stages, we introduce a dedicated accumulator type.

```ocaml
type ('a, 'b) acc =
  | Init : 'a key * 'b key -> ('a, 'b) acc
  | Compare_left_with : 'a key * int -> ('a, 'b) acc
  | Compare_right_with : int * 'b key -> ('a, 'b) acc
  | Res : int -> ('a, 'b) acc
```

This allows us to implement `compare`[^seq].

[^seq]: Note the use of the `Seq` module here. It is motivated by the fact that
    `List.fold_lefti` does not exist.

    We need to know the position of the current first-class module we are
    testing the keys against, hence the need for a `fold_lefti`. Of course, we
    could have added the current position to the `acc` type, but the function
    is already cumbersome enough, and using `Seq.t` is mostly free.

```ocaml
let compare : type a b. a key -> b key -> int =
 fun left right ->
  List.to_seq !registered_keys
  |> Seq.fold_lefti
       (fun (acc : (a, b) acc) i (module K : KEY) ->
         match acc with
         | Init (left, right) -> (
             match (K.proj left, K.proj right) with
             | Some left, Some right -> Res (K.compare left right)
             | Some _, None -> Compare_right_with (i, right)
             | None, Some _ -> Compare_left_with (left, i)
             | None, None -> acc)
         | Compare_right_with (j, right) -> (
             match K.proj right with
             | Some _ -> Res (Int.compare j i)
             | None -> acc)
         | Compare_left_with (left, j) -> (
             match K.proj left with
             | Some _ -> Res (Int.compare i j)
             | None -> acc)
         | _ -> acc)
       (Init (left, right))
  |> function
  | Res x -> x
  | _ ->
      raise
        (Invalid_argument
           "comparison with at least one unregistered key variant")
```

This function gives us the overall structure and logic of `compare`, but of
course we are not done yet.

### Step 2: Deal with GADTs

In practice and as hinted in the introduction of this section, `dmap` is not
expected a comparison function of type `'a key -> 'b key -> ('a, 'b)
Dmap.cmp`{.ocaml}, not `'a key -> 'b key -> int`{.ocaml}.

The first step is to update `acc` accordingly.

```patch
type ('a, 'b) acc =
   | Init : 'a key * 'b key -> ('a, 'b) acc
   | Compare_left_with : 'a key * int -> ('a, 'b) acc
   | Compare_right_with : int * 'b key -> ('a, 'b) acc
-  | Res : int -> ('a, 'b) acc
+  | Res : ('a, 'b) Dmap.cmp -> ('a, 'b) acc
```

Then, we focus our attention to modifying `compare`{.ocaml}, by modifying its
type signature, and by updating its definition to make use of the new
`acc`{.ocaml} type.

```patch
-let compare : type a b. a key -> b key -> int =
+let compare : type a b. a key -> b key -> (a, b) Dmap.cmp =
  fun left right ->
   List.to_seq !registered_keys
   |> Seq.fold_lefti
       (fun (acc : (a, b) acc) i (module K : KEY) ->
          match acc with
          | Init (left, right) -> (
              match (K.proj left, K.proj right) with
-             | Some left, Some right -> Res (K.compare left right)
+             | Some left, Some right ->
+                 let x = K.compare left right in
+                 Res (if x = 0 then Eq else if x < 0 then Lt else Gt)
              | Some _, None -> Compare_right_with (i, right)
              | None, Some _ -> Compare_left_with (left, i)
              | None, None -> acc)
          | Compare_right_with (j, right) -> (
              match K.proj right with
-             | Some _ -> Res (Int.compare j i)
+             | Some _ ->
+                 let x = Int.compare j i in
+                 Res (if x < 0 then Lt else Gt)
              | None -> acc)
          | Compare_left_with (left, j) -> (
              match K.proj left with
-             | Some _ -> Res (Int.compare i j)
+             | Some _ ->
+                 let x = Int.compare j i in
+                 Res (if x < 0 then Lt else Gt)
              | None -> acc)
          | _ -> acc)
        (Init (left, right))
```

At this point, we are remembered that the OCaml compiler is not that easy to
please when GADTs are involved. In particular, it complains for our use
of `Eq`.

```
46 |               Res (if x = 0 then Eq else if x < 0 then Lt else Gt)
                                      ^^
Error: This expression has type (a, a) Dmap.cmp
       but an expression was expected of type (a, b) Dmap.cmp
       Type a is not compatible with type b
```

This error message is the result of a tragedy in two acts:

1. The `Eq` constructor of `cmp` is of type `('a, 'a) cmp`. That is, only two
   keys associated with values of the same type can be equal.
2. `compare` takes two keys whose types can be different, and even if `proj` is
   expected to return a `Some` only when both keys are constructed with the
   same constructor, *nothing* in its type enforces that invariant.

As such, OCaml is not convinced with our code alone that `a = b`, and rejects
it.

One possible trick here is to rely on an equality witness type[^stdlib], and
refine `proj` in order to convince OCaml our code is type-safe.

[^stdlib]: This is *the* trick to keep in mind when playing with GADTs, to a
    point where `eq`{.ocaml} could arguably be added to the OCaml’s standard
    library.

```ocaml
type (_, _) eq = Refl : ('a, 'a) eq
```

We then modify `KEY`{.ocaml} to have `proj`{.ocaml} not only return the
arguments of the constructor, but also a type equality witness to unify the
polymorphic argument of `key` to the expected value type of said constructor.

```patch
 module type KEY = sig
   type t
+  type r
 
-  val proj : 'a key -> t option
+  val proj : 'a key -> (t * ('a, r) eq) option
   val compare : t -> t -> int
 end
```

This is enough to convince OCaml that `a = b`, because it gets a proof that `a
= K.r` and `b = K.r`[^match].

[^match]: But only if you actually match `Refl` explicitly, meaning the
    pattern `Some (left, _), Some (right, _)` would still lead to the same
    error as not returning `Refl` at all.

```patch
           match (K.proj left, K.proj right) with
-          | Some left, Some right ->
+          | Some (left, Refl), Some (right, Refl) ->
               let x = K.compare left right in
               Res (if x = 0 then Eq else if x < 0 then Lt else Gt)
           | Some _, None -> Compare_right_with (i, right)
           | None, Some _ -> Compare_left_with (left, i)
```

That’s it. `compare` is done, compiles, and satisfies the expectations of
`dmap`. We can instantiate its functor with our `key`{.ocaml} extensible
type[^sharing].

[^sharing]: This approach will lead every value of type `Extensible_record.t`
    to share the same fields, which might not be you need.

    One can imagine embedding the `registered_keys` list of known keys inside
    the extensible records values, along with a heterogeneous map. This
    would allow each value to have its own dynamic set of fields.

```ocaml
module Extensible_record = Dmap.Make (struct
  type 'a t = 'a key

  let compare = compare
end)
```

### Step 3: Profit

To wrap up this article, we can come back to our initial example of a record
with two fields `foo`{.ocaml} and `bar`{.ocaml}.

Here is how we can extend `key` to have a `Foo`{.ocaml} constructor.

```ocaml
type _ key += Foo : int key

let () =
  register_key
    (module struct
      type t = unit
      type r = int

      let proj : type a. a key -> (t * (a, r) eq) option = function
        | Foo -> Some ((), Refl)
        | _ -> None

      let compare () () = 0
    end)
```

Similarly, here is how we can register `Bar`{.ocaml}.

```ocaml
type _ key += Bar : string -> bool key

let () =
  register_key
    (module struct
      type t = string
      type r = bool

      let proj : type a. a key -> (t * (a, r) eq) option = function
        | Bar arg -> Some (arg, Refl)
        | _ -> None

      let compare = String.compare
    end)
```

Once registered, these two fields/keys can be used to populate an
`Extensible_record.t` value with values of the expected types.

```ocaml
let () =
  let record = Extensible_record.empty in
  let record = Extensible_record.add Foo 3 record in
  let record = Extensible_record.add (Bar "foobar") true record in
  assert (Extensible_record.find Foo record = 3) ;
  assert (Extensible_record.find (Bar "foobar") record)
```

A nice happy consequence of this approach is that it allows us to register
private fields only a given module can manipulate. Indeed, if this module does
not expose the constructor of the key it relies on, then only it can interact
with this part of the extensible record.
