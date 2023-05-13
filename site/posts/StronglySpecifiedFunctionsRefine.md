---
published: 2015-01-11
tags: ['coq']
series:
  parent: series/StronglySpecifiedFunctions.html
  next: posts/StronglySpecifiedFunctionsProgram.html
abstract: |
    We see how to implement strongly-specified list manipulation functions in
    Coq. Strong specifications are used to ensure some properties on functions'
    arguments and return value. It makes Coq type system very expressive.
---

# Implementing Strongly-Specified Functions with the `refine`{.coq} Tactic

I started to play with Coq, the interactive theorem prover
developed by Inria, a few weeks ago. It is a very powerful tool,
yet hard to master. Fortunately, there are some very good readings
if you want to learn (I recommend the Coq'Art). This article is
not one of them.

In this article, we will see how to implement strongly-specified
list manipulation functions in Coq. Strong specifications are used
to ensure some properties on functions' arguments and return
value. It makes Coq type system very expressive. Thus, it is
possible to specify in the type of the function `pop`{.coq} that the return
value is the list passed in argument in which the first element has been
removed for example.

## Is This List Empty?

It's the first question to deal with when manipulating
lists. There are some functions that require their arguments not
to be empty. It's the case for the `pop`{.coq} function, for instance:
it is not possible to remove the first element of a list that does
not have any elements in the first place.

When one wants to answer such a question as “Is this list empty?”,
he has to keep in mind that there are two ways to do it: by a
predicate or by a boolean function. Indeed, `Prop`{.coq} and `bool`{.coq} are
two different worlds that do not mix easily. One solution is to
write two definitions and to prove their equivalence.  That is
`forall args, predicate args <-> bool_function args = true`{.coq}.

Another solution is to use the `sumbool`{.coq} type as middleman. The
scheme is the following:

- Defining `predicate : args → Prop`{.coq}
- Defining `predicate_dec : args -> { predicate args } + { ~predicate args }`{.coq}
- Defining `predicate_b`{.coq}:

```coq
Definition predicate_b (args) :=
  if predicate_dec args then true else false.
```

### Defining the `empty`{.coq} Predicate *)

A list is empty if it is `[]`{.coq} (`nil`{.coq}). It's as simple as that!

```coq
Definition empty {a} (l : list a) : Prop := l = [].
```

### Defining a decidable version of `empty`{.coq}

A decidable version of `empty`{.coq} is a function which takes a list
`l`{.coq} as its argument and returns either a proof that `l`{.coq} is empty,
or a proof that `l`{.coq} is not empty. This is encoded in the Coq
standard library with the `sumbool`{.coq} type, and is written as
follows: `{ empty l } + { ~ empty l }`{.coq}.

```coq
Definition empty_dec {a} (l : list a)
  : { empty l } + { ~ empty l }.
Proof.
  refine (match l with
          | [] => left _ _
          | _ => right _ _
          end);
    unfold empty; trivial.
  unfold not; intro H; discriminate H.
Defined.
```

In this example, I decided to use the `refine`{.coq} tactic which is
convenient when we manipulate the `Set`{.coq} and `Prop`{.coq} sorts at the
same time.

### Defining `empty_b`{.coq}

With `empty_dec`{.coq}, we can define `empty_b`{.coq}.

```coq
Definition empty_b {a} (l : list a) : bool :=
  if empty_dec l then true else false.
```

Let's try to extract `empty_b`{.coq}:

```ocaml
type bool =
| True
| False

type sumbool =
| Left
| Right

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val empty_dec : 'a1 list -> sumbool **)

let empty_dec = function
| Nil -> Left
| Cons (a, l0) -> Right

(** val empty_b : 'a1 list -> bool **)

let empty_b l =
  match empty_dec l with
  | Left -> True
  | Right -> False
```

In addition to `'a list`{.ocaml}, Coq has created the `sumbool`{.ocaml} and
`bool`{.ocaml} types and `empty_b`{.ocaml} is basically a translation from the
former to the latter. We could have stopped with `empty_dec`{.ocmal}, but
`Left`{.ocaml} and `Right`{.ocaml} are less readable that `True`{.ocaml} and
`False`{.ocaml}. Note that it is possible to configure the Extraction mechanism
to use primitive OCaml types instead, but this is out of the scope of this
article.

## Defining Some Utility Functions

### Defining `pop`{.coq} *)

There are several ways to write a function that removes the first
element of a list. One is to return `nil` if the given list was
already empty:

```coq
Definition pop {a} ( l :list a) :=
  match l with
  | _ :: l => l
  | [] => []
  end.
```

But it's not really satisfying. A `pop` call over an empty list should not be
possible. It can be done by adding an argument to `pop`: the proof that the
list is not empty.

```coq
Definition pop {a} (l : list a) (h : ~ empty l)
  : list a.
```

There are, as usual when it comes to lists, two cases to
consider.

- `l = x :: rst`{.coq}, and therefore `pop (x :: rst) h`{.coq} is `rst`{.coq}
- `l = []`{.coq}, which is not possible since we know `l`{.coq} is not empty.

The challenge is to convince Coq that our reasoning is
correct. There are, again, several approaches to achieve that.  We
can, for instance, use the `refine`{.coq} tactic again, but this time we
need to know a small trick to succeed as using a “regular” `match`{.coq}
will not work.

From the following goal:

```
  a : Type
  l : list a
  h : ~ empty l
  ============================
  list a
```

Using the `refine`{.coq} tactic naively, for instance this way:

```coq
  refine (match l with
          | _ :: rst => rst
          | [] => _
          end).
```

leaves us the following goal to prove:

```
  a : Type
  l : list a
  h : ~ empty l
  ============================
  list a
```

Nothing has changed! Well, not exactly. See, `refine`{.coq} has taken
our incomplete Gallina term, found a hole, done some
type-checking, found that the type of the missing piece of our
implementation is `list a`{.coq} and therefore has generated a new
goal of this type.  What `refine`{.coq} has not done, however, is
remember that we are in the case where `l = []`{.coq}.

We need to generate a goal from a hole wherein this information is
available. It is possible using a long form of `match`{.coq}. The
general approach is this: rather than returning a value of type
`list a`{.coq}, our match will return a function of type [l = ?l' ->
list a], where `?l`{.coq} is value of `l`{.coq} for a given case (that is,
either `x :: rst`{.coq} or `[]`{.coq}). Of course, As a consequence, the type
of the `match`{.coq} in now a function which awaits a proof to return
the expected result. Fortunately, this proof is trivial: it is
`eq_refl`{.coq}.

```coq
  refine (match l as l'
                return l = l' -> list a
          with
          | _ :: rst => fun _ => rst
          | [] => fun equ => _
          end eq_refl).
```

For us to conclude the proof, this is way better.

```
  a : Type
  l : list a
  h : ~ empty l
  equ : l = []
  ============================
  list a
```

We conclude the proof, and therefore the definition of `pop`{.coq}.

```coq
  rewrite equ in h.
  exfalso.
  now apply h.
Defined.
```

It's better and yet it can still be improved. Indeed, according to its type,
`pop`{.coq} returns “some list”. As a matter of fact, `pop`{.coq} returns “the
same list without its first argument”. It is possible to write
such precise definition thanks to sigma-types, defined as:

```coq
Inductive sig (A : Type) (P : A -> Prop) : Type :=
  exist : forall (x : A), P x -> sig P.
```

Rather that `sig A p`{.coq}, sigma-types can be written using the
notation `{ a | P }`{.coq}. They express subsets, and can be used to constraint
arguments and results of functions.

We finally propose a strongly-specified definition of `pop`{.coq}.

```coq
Definition pop {a} (l : list a | ~ empty l)
  : { l' | exists a, proj1_sig l = cons a l' }.
```

If you think the previous use of `match`{.coq} term was ugly, brace yourselves.

```coq
  refine (match proj1_sig l as l'
                return proj1_sig l = l'
                       -> { l' | exists a, proj1_sig l = cons a l' }
          with
          | [] => fun equ => _
          | (_ :: rst) => fun equ => exist _ rst _
          end eq_refl).
```

This leaves us two goals to tackle.

First, we need to discard the case where `l`{.coq} is the empty list.

```
  a : Type
  l : {l : list a | ~ empty l}
  equ : proj1_sig l = []
  ============================
  {l' : list a | exists a0 : a, proj1_sig l = a0 :: l'}
```

```coq
  + destruct l as [l nempty]; cbn in *.
    rewrite equ in nempty.
    exfalso.
    now apply nempty.
```

Then, we need to prove that the result we provide (`rst`{.coq}) when the
list is not empty is correct with respect to the specification of
`pop`{.coq}.

```
  a : Type
  l : {l : list a | ~ empty l}
  a0 : a
  rst : list a
  equ : proj1_sig l = a0 :: rst
  ============================
  exists a1 : a, proj1_sig l = a1 :: rst
```

```coq
  + destruct l as [l nempty]; cbn in *.
    rewrite equ.
    now exists a0.
Defined.
```

Let's have a look at the extracted code:

```ocaml
(** val pop : 'a1 list -> 'a1 list **)

let pop = function
| Nil -> assert false (* absurd case *)
| Cons (a, l0) -> l0
```

If one tries to call `pop nil`{.coq}, the `assert`{.coq} ensures the call fails. Extra
information given by the sigma-type have been stripped away. It can be
confusing, and in practice it means that, we you rely on the extraction
mechanism to provide a certified OCaml module, you _cannot expose
strongly-specified functions in its public interface_ because nothing in the
OCaml type system will prevent a miseuse which will in practice leads to an
`assert false`{.ocaml}. *)

## Defining `push`{.coq}

It is possible to specify `push`{.coq} the same way `pop`{.coq} has been. The only
difference is `push`{.coq} accepts lists with no restriction at all. Thus, its
definition is a simpler, and we can write it without `refine`{.coq}.

```coq
Definition push {a} (l : list a) (x : a)
  : { l' | l' = x :: l } :=
  exist _ (x :: l) eq_refl.
```

And the extracted code is just as straightforward.

```ocaml
let push l a =
  Cons (a, l)
```

## Defining `head`{.coq}

Same as `pop`{.coq} and `push`{.coq}, it is possible to add extra information in the
type of `head`{.coq}, namely the returned value of `head`{.coq} is indeed the firt value
of `l`{.coq}.

```coq
Definition head {a} (l : list a | ~ empty l)
  : { x | exists r, proj1_sig l = x :: r }.
```

It's not a surprise its definition is very close to `pop`{.coq}.

```coq
  refine (match proj1_sig l as l'
                return proj1_sig l = l' -> _
          with
          | [] => fun equ => _
          | x :: _ => fun equ => exist _ x _
          end eq_refl).
```

The proof are also very similar, and are left to read as an exercise for
passionate readers.

```coq
  + destruct l as [l falso]; cbn in *.
    rewrite equ in falso.
    exfalso.
    now apply falso.
  + exists l0.
    now rewrite equ.
Defined.
```

Finally, the extracted code is as straightforward as it can get.

```ocaml
let head = function
| Nil -> assert false (* absurd case *)
| Cons (a, l0) -> a
```

## Conclusion

Writing strongly-specified functions allows for reasoning about the result
correctness while computing it. This can help in practice. However, writing
these functions with the `refine`{.coq} tactic does not enable a very idiomatic
Coq code.

To improve the situation, the `Program`{.coq} framework distributed with the
Coq standard library helps, but it is better to understand what `Program`{.coq}
achieves under its hood, which is basically what we have done in this article.
