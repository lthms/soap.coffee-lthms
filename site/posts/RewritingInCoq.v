(** #
<h1>Rewriting in Coq</h1>
<time datetime="2017-05-13">2017-05-13</time>
    # *)

(** I have to confess something. In the published codebase of SpecCert lies a
    shameful secret. It takes the form of a set of axioms which are not
    required. I thought they were when I wrote them, but it was before I heard
    about “generalized rewriting,” setoids and morphisms.

    Now, I know the truth. I will have to update SpecCert eventually. But,
    in the meantime, let me try to explain how it is possible to rewrite a
    term in a proof using a ad-hoc equivalence relation and, when
    necessary, a proper morphism. *)

(** #<div id="generate-toc"></div># *)

(** ** Gate: Our Case Study *)

(** Now, why would anyone want such a thing as “generalized rewriting” when the
    [rewrite] tactic works just fine.

    The thing is: it does not in some cases. To illustrate my statement, we will
    consider the following definition of a gate in Coq: *)

Record Gate :=
  { open:           bool
  ; lock:           bool
  ; lock_is_close:  lock = true -> open = false
  }.

(** According to this definition, a gate can be either open or closed. It can
    also be locked, but if it is, it cannot be open at the same time. To express
    this constrain, we embed the appropriate proposition inside the Record. By
    doing so, we _know_ for sure that we will never meet an ill-formed Gate
    instance. The Coq engine will prevent it, because to construct a gate, one
    will have to prove the [lock_is_close] predicate holds.

    The [program] attribute makes it easy to work with embedded proofs. For
    instance, defining the ”open gate” is as easy as: *)

Require Import Coq.Program.Tactics.

#[program]
Definition open_gate :=
  {| open := true
   ; lock := false
   |}.

(** Under the hood, [program] proves what needs to be proven, that is the
    [lock_is_close] proposition. Just have a look at its output:

<<
open_gate has type-checked, generating 1 obligation(s)
Solving obligations automatically...
open_gate_obligation_1 is defined
No more obligations remaining
open_gate is defined
>>

    In this case, using <<Program>> is a bit like cracking a nut with a
    sledgehammer. We can easily do it ourselves using the [refine] tactic. *)

Definition open_gate': Gate.
  refine ({| open := true
           ; lock := false
          |}).
  intro Hfalse.
  discriminate Hfalse.
Defined.

(** ** Gate Equality

What does it mean for two gates to be equal? Intuitively, we know they
have to share the same states ([open] and [lock] is our case).

*** Leibniz Equality Is Too Strong

When you write something like [a = b] in Coq, the [=] refers to the
[eq] function and this function relies on what is called the Leibniz
Equality: [x] and [y] are equal iff every property on [A] which is
true of [x] is also true of [y]

As for myself, when I first started to write some Coq code, the
Leibniz Equality was not really something I cared about and I tried to
prove something like this: *)

Lemma open_gates_are_equal (g g': Gate)
    (equ : open g = true) (equ' : open g' = true)
  : g = g'.

(** Basically, it means that if two doors are open, then they are equal. That
made sense to me, because by definition of [Gate], a locked door is closed,
meaning an open door cannot be locked.

Here is an attempt to prove the [open_gates_are_equal] lemmas. *)

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

(** The term to prove is now:

<<
{| open := true; lock := false; lock_is_close := lock_is_close0 |} =
{| open := true; lock := false; lock_is_close := lock_is_close1 |}
>>

The next tactic I wanted to use [reflexivity], because I'd basically proven
[open g = open g'] and [lock g = lock g'], which meets my definition of equality
at that time.

Except Coq wouldn’t agree. See how it reacts:

<<
Unable to unify "{| open := true; lock := false; lock_is_close := lock_is_close1 |}"
  with "{| open := true; lock := false; lock_is_close := lock_is_close0 |}".
>>

It cannot unify the two records. More precisely, it cannot unify
[lock_is_close1] and [lock_is_close0]. So we abort and try something
else. *)

Abort.

(** *** Ah hoc Equivalence Relation

This is a familiar pattern. Coq cannot guess what we have in mind. Giving a
formal definition of “our equality” is fortunately straightforward. *)

Definition gate_eq
           (g g': Gate)
  : Prop :=
  open g = open g' /\ lock g = lock g'.

(** Because “equality” means something very specific in Coq, we won't say “two
gates are equal” anymore, but “two gates are equivalent”. That is, [gate_eq] is
an equivalence relation. But “equivalence relation” is also something very
specific. For instance, such relation needs to be symmetric ([R x y -> R y x]),
reflexive ([R x x]) and transitive ([R x y -> R y z -> R x z]). *)

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

(** Afterwards, the [symmetry], [reflexivity] and [transitivity] tactics also
works with [gate_eq], in addition to [eq]. We can try again to prove the
[open_gate_are_the_same] lemma and it will work[fn:lemma]. *)

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

(** [fn:lemma] I know I should have proven an intermediate lemma to avoid code
duplication. Sorry about that, it hurts my eyes too.

** Equivalence Relations and Rewriting

So here we are, with our ad-hoc definition of gate equivalence. We can use
[symmetry], [reflexivity] and [transitivity] along with [gate_eq] and it works
fine because we have told Coq [gate_eq] is indeed an equivalence relation for
[Gate].

Can we do better? Can we actually use [rewrite] to replace an occurrence of [g]
by an occurrence of [g’] as long as we can prove that [gate_eq g g’]? The answer
is “yes”, but it will not come for free.

Before moving forward, just consider the following function: *)

Require Import Coq.Bool.Bool.

Program Definition try_open
        (g: Gate)
  : Gate :=
  if eqb (lock g) false
  then {| lock := false
        ; open := true
       |}
  else g.

(** It takes a gate as an argument and returns a new gate. If the former is not
locked, the latter is open. Otherwise the argument is returned as is. *)

Lemma gate_eq_try_open_eq
  : forall (g g': Gate),
    gate_eq g g'
    -> gate_eq (try_open g) (try_open g').
Proof.
  intros g g' Heq.
Abort.

(** What we could have wanted to do is: [rewrite Heq]. Indeed, [g] and [g’]
“are the same” ([gate_eq g g’]), so, _of course_, the results of [try_open g] and
[try_open g’] have to be the same. Except...

<<
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
>>

What Coq is trying to tell us here —in a very poor manner, I’d say— is actually
pretty simple. It cannot replace [g] by [g’] because it does not know if two
equivalent gates actually give the same result when passed as the argument of
[try_open]. This is actually what we want to prove, so we cannot use [rewrite]
just yet, because it needs this result so it can do its magic. Chicken and egg
problem.

In other words, we are making the same mistake as before: not telling Coq what
it cannot guess by itself.

The [rewrite] tactic works out of the box with the Coq equality ([eq], or most
likely [=]) because of the Leibniz Equality: [x] and [y] are equal iff every
property on [A] which is true of [x] is also true of [y]

This is a pretty strong property, and one a lot of equivalence relations do not
have. Want an example? Consider the relation [R] over [A] such that forall [x]
and [y], [R x y] holds true. Such relation is reflexive, symmetric and
reflexive. Yet, there is very little chance that given a function [f : A -> B]
and [R’] an equivalence relation over [B], [R x y -> R' (f x) (f y)]. Only if we
have this property, we would know that we could rewrite [f x] by [f y], e.g. in
[R' z (f x)]. Indeed, by transitivity of [R’], we can deduce [R' z (f y)] from
[R' z (f x)] and [R (f x) (f y)].

If [R x y -> R' (f x) (f y)], then [f] is a morphism because it preserves an
equivalence relation.  In our previous case, [A] is [Gate], [R] is [gate_eq],
[f] is [try_open] and therefore [B] is [Gate] and [R’] is [gate_eq]. To make Coq
aware that [try_open] is a morphism, we can use the following syntax: *)

#[local]
Open Scope signature_scope.

Require Import Coq.Classes.Morphisms.

#[program]
Instance try_open_Proper
  : Proper (gate_eq ==> gate_eq) try_open.

(** This notation is actually more generic because you can deal with functions
that take more than one argument. Hence, given [g : A -> B -> C -> D], [R]
(respectively [R’], [R’’] and [R’’’]) an equivalent relation of [A]
(respectively [B], [C] and [D]), we can prove [f] is a morphism as follows:

<<
Add Parametric Morphism: (g)
    with signature (R) ==> (R') ==> (R'') ==> (R''')
      as <name>.
>>

Back to our [try_open] morphism. Coq needs you to prove the following
goal:

<<
1 subgoal, subgoal 1 (ID 50)

  ============================
  forall x y : Gate, gate_eq x y -> gate_eq (try_open x) (try_open y)
>>

Here is a way to prove that: *)

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

(** Now, back to our [gate_eq_try_open_eq], we now can use [rewrite] and
[reflexivity]. *)

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

(** We did it! We actually rewrite [g] as [g’], even if we weren’t able to prove
[g = g’]. *)
