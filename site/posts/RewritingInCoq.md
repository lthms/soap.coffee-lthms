---
published: 2017-05-13
tags: ['coq']
abstract: |
    The `rewrite`{.coq} tactics are really useful, since they are not limited
    to the Coq built-in equality relation.
---

# Rewriting in Coq

I have to confess something. In the codebase of SpecCert lies a shameful
secret, which takes the form of a set of unnecessary axioms.

I thought I couldn’t avoid them at first, but it was before I heard about
“generalized rewriting,” setoids and morphisms.  Now, I know the truth, and I
will have to update SpecCert eventually. But, in the meantime, let me try to
explain how it is possible to rewrite a term in a proof using an ad hoc
equivalence relation and, when necessary, a proper morphism.

## Case Study: Gate System

Now, why would anyone want such a thing as “generalized rewriting” when the
`rewrite`{.coq} tactic works just fine.

The thing is: it does not in some cases. To illustrate my statement, we will
consider the following definition of a gate in Coq:

```coq
Record Gate :=
  { open:           bool
  ; lock:           bool
  ; lock_is_close:  lock = true -> open = false
  }.
```

According to this definition, a gate can be either open or closed. It can also
be locked, but if it is, it cannot be open at the same time. To express this
constraint, we embed the appropriate proposition inside the Record. By doing so,
we *know* for sure that we will never meet an ill-formed `Gate`{.coq} instance.
The Coq engine will prevent it, because to construct a gate, one will have to
prove the `lock_is_close`{.coq} predicate holds.

The `program`{.coq} attribute makes it easy to work with embedded proofs. For
instance, defining the ”open gate” is as easy as:

```coq
Require Import Coq.Program.Tactics.

#[program]
Definition open_gate :=
  {| open := true
   ; lock := false
   |}.
```

Under the hood, `program`{.coq} proves what needs to be proven, that is the
`lock_is_close`{.coq} proposition. Just have a look at its output:

```
open_gate has type-checked, generating 1 obligation(s)
Solving obligations automatically...
open_gate_obligation_1 is defined
No more obligations remaining
open_gate is defined
```

In this case, using `Program`{.coq} is a bit like cracking a nut with a
sledgehammer. We can easily do it ourselves using the `refine`{.coq} tactic.

```coq
Definition open_gate': Gate.
  refine ({| open := true
           ; lock := false
          |}).
  intro Hfalse.
  discriminate Hfalse.
Defined.
```

## `Gate`{.coq} Equality

What does it mean for two gates to be equal? Intuitively, we know they have to
share the same states (`open`{.coq} and `lock`{.coq} is our case).

### Leibniz Equality Is Too Strong

When you write something like `a = b`{.coq} in Coq, the `=`{.coq} refers to the
`eq`{.coq} function and this function relies on what is called the Leibniz Equality:
`x`{.coq} and `y`{.coq} are equal iff every property on `A`{.coq} which is true
of `x`{.coq} is also true of `y`{.coq}.

As for myself, when I first started to write some Coq code, the
Leibniz Equality was not really something I cared about and I tried to
prove something like this:

```coq
Lemma open_gates_are_equal (g g': Gate)
    (equ : open g = true) (equ' : open g' = true)
  : g = g'.
```

Basically, it means that if two doors are open, then they are equal. That made
sense to me, because by definition of `Gate`{.coq}, a locked door is closed,
meaning an open door cannot be locked.

Here is an attempt to prove the `open_gates_are_equal`{.coq} lemma.

```coq
Proof.
  assert (forall g, open g = true -> lock g = false). {
    intros [o l h] equo.
    cbn in *.
    case_eq l; auto.
    intros equl.
    now rewrite (h equl) in equo.
  }
  assert (lock g = false) by apply (H _ equ).
  assert (lock g' = false) by apply (H _ equ').
  destruct g; destruct g'; cbn in *; subst.
```

The term to prove is now:

```
{| open := true; lock := false; lock_is_close := lock_is_close0 |} =
{| open := true; lock := false; lock_is_close := lock_is_close1 |}
```

The next tactic I wanted to use `reflexivity`{.coq}, because I'd basically proven
`open g = open g'`{.coq} and `lock g = lock g'`{.coq}, which meets my definition of equality
at that time.

Except Coq wouldn’t agree. See how it reacts:

```
Unable to unify "{| open := true; lock := false; lock_is_close := lock_is_close1 |}"
  with "{| open := true; lock := false; lock_is_close := lock_is_close0 |}".
```

It cannot unify the two records. More precisely, it cannot unify
`lock_is_close1`{.coq} and `lock_is_close0`{.coq}. So we abort and try something
else.

```coq
Abort.
```

### Ah-Hoc Equivalence Relation

This is a familiar pattern. Coq cannot guess what we have in mind. Giving a
formal definition of “our equality” is fortunately straightforward.

```coq
Definition gate_eq
           (g g': Gate)
  : Prop :=
  open g = open g' /\ lock g = lock g'.
```

Because “equality” means something very specific in Coq, we won't say “two
gates are equal” anymore, but “two gates are equivalent.” That is,
`gate_eq`{.coq} is an equivalence relation. But “equivalence relation” is also
something very specific. For instance, such relation needs to be symmetric (`R
x y -> R y x`{.coq}), reflexive (`R x x`{.coq}) and transitive (`R x y -> R y z
-> R x z`{.coq}).

```coq
Require Import Coq.Classes.Equivalence.

#[program]
Instance Gate_Equivalence
  : Equivalence gate_eq.

Next Obligation.
  split; reflexivity.
Defined.

Next Obligation.
  intros g g' [Hop Hlo].
  symmetry in Hop; symmetry in Hlo.
  split; assumption.
Defined.

Next Obligation.
  intros g g' g'' [Hop Hlo] [Hop' Hlo'].
  split.
  + transitivity (open g'); [exact Hop|exact Hop'].
  + transitivity (lock g'); [exact Hlo|exact Hlo'].
Defined.
```

Afterwards, the `symmetry`{.coq}, `reflexivity`{.coq} and `transitivity`{.coq}
tactics also works with `gate_eq`{.coq}, in addition to `eq`{.coq}. We can try
again to prove the `open_gate_are_the_same`{.coq} lemma and it will
work[^lemma].

[^lemma]: I know I should have proven an intermediate lemma to avoid code
    duplication. Sorry about that, it hurts my eyes too.

```coq
Lemma open_gates_are_the_same:
  forall (g g': Gate),
    open g = true
    -> open g' = true
    -> gate_eq g g'.
Proof.
  induction g; induction g'.
  cbn.
  intros H0 H2.
  assert (lock0 = false).
  + case_eq lock0; [ intro H; apply lock_is_close0 in H;
                     rewrite H0 in H;
                     discriminate H
                   | reflexivity
                   ].
  + assert (lock1 = false).
    * case_eq lock1; [ intro H'; apply lock_is_close1 in H';
                       rewrite H2 in H';
                       discriminate H'
                     | reflexivity
                     ].
    * subst.
      split; reflexivity.
Qed.
```

## Equivalence Relations and Rewriting

So here we are, with our ad hoc definition of gate equivalence. We can use
`symmetry`{.coq}, `reflexivity`{.coq} and `transitivity`{.coq} along with
`gate_eq`{.coq} and it works fine because we have told Coq `gate_eq`{.coq} is
indeed an equivalence relation for `Gate`{.coq}.

Can we do better? Can we actually use `rewrite`{.coq} to replace an occurrence
of `g`{.coq} by an occurrence of `g’`{.coq} as long as we can prove that
`gate_eq g g’`{.coq}? The answer is “yes”, but it will not come for free.

Before moving forward, just consider the following function:

```coq
Require Import Coq.Bool.Bool.

Program Definition try_open
        (g: Gate)
  : Gate :=
  if eqb (lock g) false
  then {| lock := false
        ; open := true
       |}
  else g.
```

It takes a gate as an argument and returns a new gate. If the former is not
locked, the latter is open. Otherwise the argument is returned as is.

```coq
Lemma gate_eq_try_open_eq
  : forall (g g': Gate),
    gate_eq g g'
    -> gate_eq (try_open g) (try_open g').
Proof.
  intros g g' Heq.
Abort.
```

What we could have wanted to do is: `rewrite Heq`{.coq}. Indeed, `g`{.coq} and `g’`{.coq}
“are the same” (`gate_eq g g’`{.coq}), so, _of course_, the results of `try_open g`{.coq} and
`try_open g’`{.coq} have to be the same. Except...

```
Error: Tactic failure: setoid rewrite failed: Unable to satisfy the following constraints:
UNDEFINED EVARS:
 ?X49==[g g' Heq |- relation Gate] (internal placeholder) {?r}
 ?X50==[g g' Heq (do_subrelation:=Morphisms.do_subrelation)
         |- Morphisms.Proper (gate_eq ==> ?X49@{__:=g; __:=g'; __:=Heq}) try_open] (internal placeholder) {?p}
 ?X52==[g g' Heq |- relation Gate] (internal placeholder) {?r0}
 ?X53==[g g' Heq (do_subrelation:=Morphisms.do_subrelation)
         |- Morphisms.Proper (?X49@{__:=g; __:=g'; __:=Heq} ==> ?X52@{__:=g; __:=g'; __:=Heq} ==> Basics.flip Basics.impl) eq]
         (internal placeholder) {?p0}
 ?X54==[g g' Heq |- Morphisms.ProperProxy ?X52@{__:=g; __:=g'; __:=Heq} (try_open g')] (internal placeholder) {?p1}
```

What Coq is trying to tell us here —in a very poor manner, I’d say— is actually
pretty simple. It cannot replace `g`{.coq} by `g’`{.coq} because it does not
know if two equivalent gates actually give the same result when passed as the
argument of `try_open`{.coq}. This is actually what we want to prove, so we
cannot use `rewrite`{.coq} just yet, because it needs this result so it can do
its magic. Chicken and egg problem.

In other words, we are making the same mistake as before: not telling Coq what
it cannot guess by itself.

The `rewrite`{.coq} tactic works out of the box with the Coq equality
(`eq`{.coq}, or most likely `=`{.coq}) because of the Leibniz Equality:
`x`{.coq} and `y`{.coq} are equal iff every property on `A`{.coq} which is true
of `x`{.coq} is also true of `y`{.coq}

This is a pretty strong property, and one that a lot of equivalence relations do not
have. Want an example? Consider the relation `R`{.coq} over `A`{.coq} such that
forall `x`{.coq} and `y`{.coq}, `R x y`{.coq} holds true. Such a relation is
reflexive, symmetric and reflexive. Yet, there is very little chance that given
a function `f : A -> B`{.coq} and `R’`{.coq} an equivalence relation over
`B`{.coq}, `R x y -> R' (f x) (f y)`{.coq}. Only if we have this property, we
would know that we could rewrite `f x`{.coq} by `f y`{.coq}, *e.g.*, in `R' z
(f x)`{.coq}. Indeed, by transitivity of `R’`{.coq}, we can deduce `R' z (f
y)`{.coq} from `R' z (f x)`{.coq} and `R (f x) (f y)`{.coq}.

If `R x y -> R' (f x) (f y)`{.coq}, then `f`{.coq} is a morphism because it
preserves an equivalence relation.  In our previous case, `A`{.coq} is
`Gate`{.coq}, `R`{.coq} is `gate_eq`{.coq}, `f`{.coq} is `try_open`{.coq} and
therefore `B`{.coq} is `Gate`{.coq} and `R’`{.coq} is `gate_eq`{.coq}. To make
Coq aware that `try_open`{.coq} is a morphism, we can use the following syntax:
*)

```coq
#[local]
Open Scope signature_scope.

Require Import Coq.Classes.Morphisms.

#[program]
Instance try_open_Proper
  : Proper (gate_eq ==> gate_eq) try_open.
```

This notation is actually more generic because you can deal with functions that
take more than one argument. Hence, given `g : A -> B -> C -> D`{.coq},
`R`{.coq} (respectively `R’`{.coq}, `R’’`{.coq} and `R’’’`{.coq}) an equivalent
relation of `A`{.coq} (respectively `B`{.coq}, `C`{.coq} and `D`{.coq}), we can
prove `f`{.coq} is a morphism as follows:

```coq
Add Parametric Morphism: (g)
    with signature (R) ==> (R') ==> (R'') ==> (R''')
      as <name>.
```

Back to our `try_open`{.coq} morphism. Coq needs you to prove the following
goal:

```
1 subgoal, subgoal 1 (ID 50)

  ============================
  forall x y : Gate, gate_eq x y -> gate_eq (try_open x) (try_open y)
```

Here is a way to prove that:

```coq
Next Obligation.
  intros g g' Heq.
  assert (gate_eq g g') as [Hop Hlo] by (exact Heq).
  unfold try_open.
  rewrite <- Hlo.
  destruct (bool_dec (lock g) false) as [Hlock|Hnlock]; subst.
  + rewrite Hlock.
    split; cbn; reflexivity.
  + apply not_false_is_true in Hnlock.
    rewrite Hnlock.
    cbn.
    exact Heq.
Defined.
```

Now, back to our `gate_eq_try_open_eq`{.coq}, we now can use `rewrite`{.coq}
and `reflexivity`{.coq}.

```coq
Require Import Coq.Setoids.Setoid.

Lemma gate_eq_try_open_eq
  : forall (g g': Gate),
    gate_eq g g'
    -> gate_eq (try_open g) (try_open g').
Proof.
  intros g g' Heq.
  rewrite Heq.
  reflexivity.
Qed.
```

We did it! We actually rewrite `g`{.coq} as `g’`{.coq}, even if we weren’t able
to prove `g = g’`{.coq}.
