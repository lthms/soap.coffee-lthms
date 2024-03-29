---
published: 2020-08-28
modified: 2023-05-08
tags: ['coq']
series:
  parent: series/Ltac.html
  next: posts/LtacPatternMatching.html
abstract: |
    Ltac generates terms, therefore it is a metaprogramming language. It does
    it incrementally, by using primitives to modifying an implicit state,
    therefore it is an imperative language. Henceforth, it is an imperative
    metaprogramming language.
---

# Ltac is an Imperative Metaprogramming Language

Coq is often depicted as an _interactive_ proof assistant, thanks to its
proof environment. Inside the proof environment, Coq presents the user a
goal, and said user solves said goal by means of tactics which describes a
logical reasoning. For instance, to reason by induction, one can use the
`induction`{.coq} tactic, while a simple case analysis can rely on the
`destruct`{.coq} or `case_eq`{.coq} tactics, etc.  It is not uncommon for new
Coq users to be introduced to Ltac, the Coq default tactic language, using this
proof-centric approach. This is not surprising, since writing proofs remains
the main use case for Ltac. In practice, though, this discourse remains an
abstraction which hides away what actually happens under the hood when Coq
executes a proof script.

To really understand what Ltac is about, we need to recall ourselves that
Coq kernel is mostly a type checker. A theorem statement is expressed as a
“type” (which lives in a dedicated sort called `Prop`{.coq}), and a proof of
this theorem is a term of this type, just like the term `S (S O)`{.coq} ($2$)
is of type `nat`{.coq}.  Proving a theorem in Coq requires to construct a term
of the type encoding said theorem, and Ltac allows for incrementally
constructing this term, one step at a time.

Ltac generates terms, therefore it is a metaprogramming language. It does it
incrementally, by using primitives to modifying an implicit state, therefore
it is an imperative language. Henceforth, it is an imperative
metaprogramming language.

To summarize, a goal presented by Coq inside the environment proof is a hole
within the term being constructed. It is presented to users as:

- A list of “hypotheses,” which are nothing more than the variables
  in the scope of the hole
- A type, which is the type of the term to construct to fill the hole

We illustrate what happens under the hood of Coq executes a simple proof
script. One can use the `Show Proof`{.coq} vernacular command to exhibit
this.

We illustrate how Ltac works with the following example.

```coq
Theorem add_n_O : forall (n : nat), n + O = n.
Proof.
```

The `Proof`{.coq} vernacular command starts the proof environment. Since no
tactic has been used, the term we are trying to construct consists solely in a
hole, while Coq presents us a goal with no hypothesis, and with the exact type
of our theorem, that is `forall (n : nat), n + O = n`{.coq}.

A typical Coq course will explain to students the `intro`{.coq} tactic allows for
turning the premise of an implication into an hypothesis within the context.

$$C \vdash P \rightarrow Q$$

becomes

$$C,\ P \vdash Q$$

This is a fundamental rule of deductive reasoning, and `intro`{.coq} encodes it.
It achieves this by refining the current hole into an anonymous function.
When we use

```coq
  intro n.
```

it refines the term

```coq
  ?Goal1
```

into

```coq
  fun (n : nat) => ?Goal2
```

The next step of this proof is to reason about induction on `n`. For `nat`,
it means that to be able to prove

$$\forall n, \mathrm{P}\ n$$

we need to prove that

-  $\mathrm{P}\ 0$
-  $\forall n, \mathrm{P}\ n \rightarrow \mathrm{P}\ (S n)$

The `induction`{.coq} tactic effectively turns our goal into two subgoals. But
why is that? Because, under the hood, Ltac is refining the current goal using
the `nat_ind`{.coq} function automatically generated by Coq when `nat`{.coq}
was defined. The type of `nat_ind`{.coq} is

```coq
  forall (P : nat -> Prop),
    P 0
    -> (forall n : nat, P n -> P (S n))
    -> forall n : nat, P n
```

Interestingly enough, `nat_ind`{.coq} is not an axiom. It is a regular Coq
function, whose definition is

```coq
  fun (P : nat -> Prop) (f : P 0)
      (f0 : forall n : nat, P n -> P (S n)) =>
  fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
    | 0 => f
    | S n0 => f0 n0 (F n0)
    end
```

So, after executing

```coq
  induction n.
```

The hidden term we are constructing becomes

```coq
  (fun n : nat =>
     nat_ind
       (fun n0 : nat => n0 + 0 = n0)
       ?Goal3
       (fun (n0 : nat) (IHn : n0 + 0 = n0) => ?Goal4)
       n)
```

And Coq presents us two goals.

First, we need to prove $\mathrm{P}\ 0$, *i.e.*,
$0 + 0 = 0$. Similarly to Coq presenting a goal when what we are actually doing
is constructing a term, the use of $=$ and $+$ (*i.e.*, the Coq notations
mechanism) hides much here. We can ask Coq to be more explicit by using the
vernacular command `Set Printing All`{.coq} to learn that when Coq presents us
a goal of the form `0 + 0 = 0`{.coq}, it is actually looking for a term of type
`@eq nat (Nat.add O O) O`{.coq}.

`Nat.add`{.coq} is a regular Coq (recursive) function.

```coq
  fix add (n m : nat) {struct n} : nat :=
    match n with
    | 0 => m
    | S p => S (add p m)
    end
```

Similarly, `eq`{.coq} is *not* an axiom. It is a regular inductive type, defined
as follows.

```coq
Inductive eq (A : Type) (x : A) : A -> Prop :=
| eq_refl : eq A x x
```

Coming back to our current goal, proving `@eq nat (Nat.add 0 0) 0`{.coq}[^equ1]
requires to construct a term of a type whose only constructor is
`eq_refl`{.coq}. `eq_refl`{.coq} accepts one argument, and encodes the proof
that said argument is equal to itself. In practice, Coq type checker will accept
the term `@eq_refl _ x`{.coq} when it expects a term of type `@eq _ x y`{.coq}
*if* it can reduce `x`{.coq} and `y`{.coq} to the same term.

[^equ1]: That is, `0 + 0 = 0`{.coq}

Is it the case for `@eq nat (Nat.add 0 0) 0`{.coq}? It is, since by definition
of `Nat.add`{.coq}, `Nat.add 0 x`{.coq} is reduced to `x`{.coq}. We can use the
`reflexivity`{.coq} tactic to tell Coq to fill the current hole with
`eq_refl`{.coq}.

```coq
  + reflexivity.
```

Suspicious readers may rely on `Show Proof`{.coq} to verify this assertion.

```coq
  (fun n : nat =>
     nat_ind
       (fun n0 : nat => n0 + 0 = n0)
       eq_refl
       (fun (n0 : nat) (IHn : n0 + 0 = n0) => ?Goal4)
       n)
```

`?Goal3`{.coq} has indeed be replaced by `eq_refl`.

One goal remains, as we need to prove that if `n + 0 = n`{.coq}, then `S n + 0
= S n`{.coq}. Coq can reduce `S n + 0`{.coq} to `S (n + 0)`{.coq} by definition
of `Nat.add`{.coq}, but it cannot reduce `S n`{.coq} more than it already is.

```coq
  + cbn.
```

We cannot just use `reflexivity`{.coq} here (*i.e.*, fill the hole with
`eq_refl`{.coq}), since `S (n + 0)`{.coq} and `S n`{.coq} cannot be reduced to
the same term.

However, at this point of the proof, we have the `IHn`{.coq} hypothesis (*i.e.*, the
`IHn`{.coq} argument of the anonymous function whose body we are trying to
construct). The `rewrite`{.coq} tactic allows for substituting in a type an
occurrence of `x`{.coq} by `y`{.coq} as long as we have a proof of `x = y`{.coq}. *)

```coq
    rewrite IHn.
```

Similarly to `induction`{.coq} using a dedicated function, `rewrite`{.coq} refines
the current hole with the `eq_ind_r`{.coq} function[^noaxiom]. Replacing `n +
0`{.coq} with `n`{.coq} transforms the goal into `S n = S n`{.coq}. Here, we
can use `reflexivity`{.coq} (i.e., `eq_refl`{.coq}) to conclude. *)

[^noaxiom]: Again, not an axiom.

```coq
    reflexivity.
```

After this last tactic, the work is done. There is no more goal to fill inside
the proof term that we have carefully constructed.

```coq
  (fun n : nat =>
     nat_ind
       (fun n0 : nat => n0 + 0 = n0)
       eq_refl
       (fun (n0 : nat) (IHn : n0 + 0 = n0) =>
          eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl IHn)
       n)
```

We can finally use `Qed`{.coq} or `Defined`{.coq} to tell Coq to type check this
term. That is, Coq does not trust Ltac, but rather type check the term to
verify it is correct. This way, in case Ltac has a bug which makes it
construct an ill-formed type, at the very least Coq can reject it.

```coq
Qed.
```

In conclusion, tactics are used to incrementally refine hole inside a term
until the latter is complete. They do it in a very specific manner, to
encode certain reasoning rules.

On the other hand, the `refine`{.coq} tactic provides a generic, low-level way
to do the same thing. Knowing how a given tactic works allows for mimicking
its behavior using the `refine`{.coq} tactic.

If we take the previous theorem as an example, we can prove it using this
alternative proof script.

```coq
Theorem add_n_O' : forall (n : nat), n + O = n.
Proof.
  refine (fun n => _).
  refine (nat_ind (fun n => n + 0 = n) _ _ n).
  + refine eq_refl.
  + refine (fun m IHm => _).
    refine (eq_ind_r (fun n => S n = S m) _ IHm).
    refine eq_refl.
Qed.
