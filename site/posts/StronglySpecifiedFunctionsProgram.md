---
published: 2017-01-01
tags: ['coq']
series:
  parent: series/StronglySpecifiedFunctions.html
  prev: posts/StronglySpecifiedFunctionsRefine.html
abstract: |
    `Program`{.coq} is the heir of the `refine`{.coq} tactic. It gives you a
    convenient way to embed proofs within functional programs that are supposed
    to fade away during code extraction.
---

# Implementing Strongly-Specified Functions with the `Program`{.coq} Framework

## The Theory

If I had to explain `Program`{.coq}, I would say `Program`{.coq} is the heir of
the `refine`{.coq} tactic. It gives you a convenient way to embed proofs within
functional programs that are supposed to fade away during code extraction.  But
what do I mean when I say "embed proofs" within functional programs? I found
two ways to do it.

### Invariants

First, we can define a record with one or more fields of type
`Prop`{.coq}. By doing so, we can constrain the values of other fields. Put
another way, we can specify invariant for our type. For instance, in
[SpecCert](https://github.com/lthms/SpecCert), I have defined the memory
controller's SMRAMC register as follows:

```coq
Record SmramcRegister := {
  d_open: bool;
  d_lock: bool;
  lock_is_close: d_lock = true -> d_open = false;
}.
```

So `lock_is_closed`{.coq} is an invariant I know each instance of
`SmramcRegister` will have to comply with, because every time I
will construct a new instance, I will have to prove
`lock_is_closed`{.coq} holds true. For instance:

```coq
Definition lock (reg: SmramcRegister)
  : SmramcRegister.
  refine ({| d_open := false; d_lock := true |}).
```

Coq leaves us this goal to prove.

```
reg : SmramcRegister
============================
true = true -> false = false
```

This sound reasonable enough.

```coq
Proof.
  trivial.
Defined.
```

We have seen in my previous article about strongly specified
functions that mixing proofs and regular terms may lead to
cumbersome code.

From that perspective, `Program`{.coq} helps. Indeed, the `lock`{.coq} function
can also be defined as follows:

```coq
From Coq Require Import Program.

#[program]
Definition lock' (reg: SmramcRegister)
  : SmramcRegister :=
  {| d_open := false
   ; d_lock := true
   |}.
```

### Pre and Post Conditions

Another way to "embed proofs in a program" is by specifying pre-
and post-conditions for its component. In Coq, this is done using
sigma types.

On the one hand, a precondition is a proposition a function input has to
satisfy in order for the function to be applied.  For instance, a precondition
for `head : forall {a}, list a -> a`{.coq} the function that returns the first
element of a list `l`{.coq} requires `l`{.coq} to contain at least one element.
We can write that using a sigma-type. The type of `head`{.coq} then becomes
`forall {a} (l: list a | l <> []) : a`{.coq}.

On the other hand, a post condition is a proposition a function
output has to satisfy in order for the function to be correctly
implemented. In this way, `head` should in fact return the first
element of `l`{.coq} and not something else.

`Program`{.coq} makes writing this specification straightforward.

```coq
#[program]
Definition head {a} (l : list a | l <> [])
  : { x : a | exists l', x :: l' = l }.
```

We recall that because `{ l: list a | l <> [] }`{.coq} is not the same as `list
a`{.coq}, in theory we cannot just compare `l`{.coq} with `x :: l'`{.coq} (we need to
use `proj1_sig`{.coq}). One advantage of `Program`{.coq} is to deal with it using
an implicit coercion.

Note that for the type inference to work as expected, the
unwrapped value (here, `x :: l'`{.coq}) needs to be the left operand of
`=`{.coq}.

Now that `head`{.coq} have been specified, we have to implement it.

```coq
#[program]
Definition head {a} (l: list a | l <> [])
  : { x : a | exists l', cons x l' = l } :=
  match l with
  | x :: l' => x
  | [] => !
  end.

Next Obligation.
  exists l'.
  reflexivity.
Qed.
```

I want to highlight several things here:

- We return `x`{.coq} (of type `a`{.coq}) rather than a sigma-type, then
  `Program`{.coq} is smart enough to wrap it. To do so, it tries to prove the post
  condition and because it fails, we have to do it ourselves (this is the
  Obligation we solve after the function definition.)
- The `[]`{.coq} case is absurd regarding the precondition, we tell Coq that
  using the bang (`!`{.coq}) symbol.

We can have a look at the extracted code:

```ocaml
(** val head : 'a1 list -> 'a1 **)
let head = function
| Nil -> assert false (* absurd case *)
| Cons (a, _) -> a
```

The implementation is pretty straightforward, but the pre- and
post conditions have faded away. Also, the absurd case is
discarded using an assertion. This means one thing: [head] should
not be used directly from the Ocaml world. "Interface" functions
have to be total. *)

## The Practice

```coq
From Coq Require Import Lia.
```

I have challenged myself to build a strongly specified library. My goal was to
define a type `vector : nat -> Type -> Type`{.coq} such as `vector a n`{.coq}
is a list of `n`{.coq} instance of `a`{.coq}.

```coq
Inductive vector (a : Type) : nat -> Type :=
| vcons {n} : a -> vector a n -> vector a (S n)
| vnil : vector a O.

Arguments vcons [a n] _ _.
Arguments vnil {a}.
```

I had three functions in mind: `take`{.coq}, `drop`{.coq} and `extract`{.coq}.
I learned a few lessons. My main takeaway remains: do not use sigma types,
`Program`{.coq} and dependent types together. From my point of view, Coq is not
yet ready for this. Maybe it is possible to make those three work together, but
I have to admit I did not find out how. As a consequence, my preconditions are
defined as extra arguments.

To be able to specify the post conditions of my three functions and
some others, I first defined `nth`{.coq} to get the _nth_ element of a
vector.

My first attempt to write `nth`{.coq} was a failure.

```coq
#[program]
Fixpoint nth {a n}
    (v : vector a n) (i : nat) {struct v}
  : option a :=
  match v, i with
  | vcons x _, O => Some x
  | vcons x r, S i => nth r i
  | vnil, _ => None
  end.
```

raised an anomaly.

```coq
#[program]
Fixpoint nth {a n}
    (v : vector a n) (i : nat) {struct v}
  : option a :=
  match v with
  | vcons x r =>
    match i with
    | O => Some x
    | S i => nth r i
    end
  | vnil => None
  end.
```

With `nth`{.coq}, it is possible to give a very precise definition of
`take`{.coq}:

```coq
#[program]
Fixpoint take {a n}
    (v : vector a n) (e : nat | e <= n)
  : { u : vector a e | forall i : nat,
        i < e -> nth u i = nth v i } :=
  match e with
  | S e' => match v with
            | vcons x r => vcons x (take r e')
            | vnil => !
            end
  | O => vnil
  end.

Next Obligation.
  now apply le_S_n.
Defined.

Next Obligation.
  induction i.
  + reflexivity.
  + apply e0.
    now apply Lt.lt_S_n.
Defined.

Next Obligation.
  now apply PeanoNat.Nat.nle_succ_0 in H.
Defined.

Next Obligation.
  now apply PeanoNat.Nat.nlt_0_r in H.
Defined.
```

As a side note, I wanted to define the post condition as follows:
`{ v': vector A e | forall (i : nat | i < e), nth v' i = nth v i
}`{.coq}. However, this made the goals and hypotheses become very hard
to read and to use. Sigma types in sigma types: not a good
idea.

```ocaml
(** val take : 'a1 vector -> nat -> 'a1 vector **)

let rec take v = function
| O -> Vnil
| S e' ->
  (match v with
   | Vcons (_, x, r) -> Vcons (e', x, (take r e'))
   | Vnil -> assert false (* absurd case *))
```

Then I could tackle `drop` in a very similar manner:

```coq
#[program]
Fixpoint drop {a n}
    (v : vector a n) (b : nat | b <= n)
  : { v': vector a (n - b) | forall i,
        i < n - b -> nth v' i = nth v (b + i) } :=
  match b with
  | 0 => v
  | S n => (match v with
           | vcons _ r => (drop r n)
           | vnil => !
           end)
  end.

Next Obligation.
  now rewrite <- Minus.minus_n_O.
Defined.

Next Obligation.
  induction n;
    rewrite <- eq_rect_eq;
    reflexivity.
Defined.

Next Obligation.
  now apply le_S_n.
Defined.

Next Obligation.
  now apply PeanoNat.Nat.nle_succ_0 in H.
Defined.
```

The proofs are easy to write, and the extracted code is exactly what one might
want it to be:

```ocaml
(** val drop : 'a1 vector -> nat -> 'a1 vector **)
let rec drop v = function
| O -> v
| S n ->
  (match v with
   | Vcons (_, _, r) -> drop r n
   | Vnil -> assert false (* absurd case *))
```

But `Program`{.coq} really shone when it comes to implementing extract. I just
had to combine `take`{.coq} and `drop`{.coq}. *)

```coq
#[program]
Definition extract {a n} (v : vector a n)
    (e : nat | e <= n) (b : nat | b <= e)
  : { v': vector a (e - b) | forall i,
        i < (e - b) -> nth v' i = nth v (b + i) } :=
  take (drop v b) (e - b).


Next Obligation.
  transitivity e; auto.
Defined.

Next Obligation.
  now apply PeanoNat.Nat.sub_le_mono_r.
Defined.

Next Obligation.
  destruct drop; cbn in *.
  destruct take; cbn in *.
  rewrite e1; auto.
  rewrite <- e0; auto.
  lia.
Defined.
```

The proofs are straightforward because the specifications of `drop`{.coq} and
`take`{.coq} are precise enough, and we do not need to have a look at their
implementations. The extracted version of `extract`{.coq} is as clean as we can
anticipate.

```ocaml
(** val extract : 'a1 vector -> nat -> nat -> 'a1 vector **)
let extract v e b =
  take (drop v b) (sub e b)
```

I was pretty happy, so I tried some more. Each time, using `nth`{.coq}, I managed
to write a precise post condition and to prove it holds true. For instance,
given `map`{.coq} to apply a function `f`{.coq} to each element of a vector `v`{.coq}:

```coq
#[program]
Fixpoint map {a b n} (v : vector a n) (f : a -> b)
  : { v': vector b n | forall i,
        nth v' i = option_map f (nth v i) } :=
  match v with
  | vnil => vnil
  | vcons a v => vcons (f a) (map v f)
  end.

Next Obligation.
  induction i.
  + reflexivity.
  + apply e.
Defined.
```

I also managed to specify and write `append`{.coq}:

```
#[program]
Fixpoint append {a n m}
    (v : vector a n) (u : vector a m)
  : { w : vector a (n + m) | forall i,
        (i < n -> nth w i = nth v i) /\
        (n <= i -> nth w i = nth u (i - n))
    } :=
  match v with
  | vnil => u
  | vcons a v => vcons a (append v u)
  end.

Next Obligation.
  split.
  + now intro.
  + intros _.
    now rewrite PeanoNat.Nat.sub_0_r.
Defined.

Next Obligation.
  rename wildcard' into n.
  destruct (Compare_dec.lt_dec i (S n)); split.
  + intros _.
    destruct i.
    ++ reflexivity.
    ++ cbn.
       specialize (a1 i).
       destruct a1 as [a1 _].
       apply a1.
       auto with arith.
  + intros false.
    lia.
  + now intros.
  + intros ord.
    destruct i.
    ++ lia.
    ++ cbn.
       specialize (a1 i).
       destruct a1 as [_ a1].
       apply a1.
       auto with arith.
Defined.
```

Finally, I tried to implement `map2`{.coq} that takes a vector of `a`{.coq}, a vector of
`b`{.coq} (both of the same size) and a function `f : a -> b -> c`{.coq} and returns a
vector of `c`{.coq}.

First, we need to provide a precise specification for `map2`{.coq}. To do that, we
introduce `option_app`{.coq}, a function that Haskellers know all to well as being
part of the `Applicative`{.haskell} type class.

```coq
Definition option_app {a b}
    (opf: option (a -> b))
    (opx: option a)
  : option b :=
  match opf, opx with
  | Some f, Some x => Some (f x)
  | _, _ => None
end.
```

We thereafter use `<$>`{.coq} as an infix operator for `option_map`{.coq} and `<*>`{.coq} as
an infix operator for `option_app`{.coq}. *)

```coq
Infix "<$>" := option_map (at level 50).
Infix "<*>" := option_app (at level 55).
```

Given two vectors `v`{.coq} and `u`{.coq} of the same size and a function `f`{.coq}, and given
`w`{.coq} the result computed by `map2`{.coq}, then we can propose the following
specification for `map2`{.coq}:

`forall (i : nat), nth w i = f <$> nth v i <*> nth u i`{.coq}

This reads as follows: the `i`{.coq}th element of `w`{.coq} is the result of applying
the `i`{.coq}th elements of `v`{.coq} and `u`{.coq} to `f`{.coq}.

It turns out implementing `map2`{.coq} with the `Program`{.coq} framework has
proven to be harder than I originally expected. My initial attempt was the
following:

```coq
#[program]
Fixpoint map2 {a b c n}
    (v : vector a n) (u : vector b n)
    (f : a -> b -> c) {struct v}
  : { w: vector c n | forall i,
        nth w i = f <$> nth v i <*> nth u i
    } :=
  match v, u with
  | vcons x rst, vcons x' rst' =>
      vcons (f x x') (map2 rst rst' f)
  | vnil, vnil => vnil
  | _, _ => !
  end.
```

```
Illegal application:
The term "@eq" of type "forall A : Type, A -> A -> Prop"
cannot be applied to the terms
 "nat" : "Set"
 "S wildcard'" : "nat"
 "b" : "Type"
The 3rd term has type "Type" which should be coercible
to "nat".
```

So I had to fallback to defining the function in pure Ltac.

```coq
#[program]
Fixpoint map2 {a b c n}
    (v : vector a n) (u : vector b n)
    (f : a -> b -> c) {struct v}
  : { w: vector c n | forall i,
        nth w i = f <$> nth v i <*> nth u i
    } := _.

Next Obligation.
  dependent induction v; dependent induction u.
  + remember (IHv u f) as u'.
    inversion u'.
    refine (exist _ (vcons (f a0 a1) x) _).
    intros i.
    induction i.
    * reflexivity.
    * apply (H i).
  + refine (exist _ vnil _).
    reflexivity.
Qed.
```

## Is It Usable?

This post mostly gives the "happy ends" for each function. I think I tried
too hard for what I got in return and therefore I am convinced `Program`{.coq}
is not ready (at least for a dependent type, I cannot tell for the rest). For
instance, I found at least one bug in Program logic (I still have to report
it). Have a look at the following code:

```coq
#[program]
Fixpoint map2 {a b c n}
     (u : vector a n) (v : vector b n)
     (f : a -> b -> c) {struct v}
  : vector c n :=
  match u with
  | _ => vnil
  end.
```

It gives the following error:

```
Error: Illegal application:
The term "@eq" of type "forall A : Type, A -> A -> Prop"
cannot be applied to the terms
 "nat" : "Set"
 "0" : "nat"
 "wildcard'" : "vector A n'"
The 3rd term has type "vector A n'" which should be
coercible to "nat".
```
