(** #<h1>Ltac 101</h1>#

    This article has originally been published on #<span class="time">October
    16, 2017</span>#. *)

(** In this article, I give an overview of my findings about the Ltac language,
    more precisely how it can be used to automate the construction of proof
    terms. If you never wrote a tactic in Coq and are curious about the subject,
    it might be a good starting point. *)

(** #<div id="generate-toc"></div>#

    #<div id="history">site/posts/Ltac101.v</div># *)

(** ** Tactics Aliases *)

(** The first thing you will probably want to do with Ltac is define aliases for
    recurring (sequences of) tactics.

    To take a concrete example, the very first tactic I wrote was for a project
    called SpecCert where _many_ lemmas are basically about proving a given
    property [P] is a state invariant of a given transition system. As a
    consequence, they have the very same “shape:”

    \( \forall s\ l\ s', P(s) \wedge s \overset{l\ }{\mapsto} s' \rightarrow  P(s') \),
    that is, if [P] is satisfied for [s], and there exists a transition from [s]
    to [s'], then [P] is satisfied for [s'].

    Both states and labels are encoded in record, and the first thing I was
    doing at the time with them was [destruct]ing them. Similarly, the predicate
    [P] is an aggregation of sub-predicates (using \( \wedge \)). In practice,
    most of my proofs started with something like [intros [x1 [y1 z1]] [a b] [x2
    [y2 z2]] [HP1 [HP2 [HP3 HP4]]] [R1|R2]]. Nothing copy/past cannot solve at
    first, of course, but as soon as the definitions change, you have to change
    every single [intros] and it is quite boring, to say the least.

    The solution is simple: define a new tactic to use in place of your “raw”
    [intros]: *)

Ltac my_intros_1 :=
  intros [x1 [y1 z1]] [a b] [x2 [y2 z2]] [HP1 [HP2 [HP3 HP4]]] [R1|R2].

(** As a more concrete example, we consider the following goal: *)

Goal (forall (P Q : Prop), P /\ Q -> P).

(** A typical way to move the premises of this statement from the goal to the
    context is by means of [intro], and it is possible to destruct the term [p
    /\ q] with a pattern. *)

  intros P Q [p q].

(** which leaves the following goal to prove:

<<
  P, Q : Prop
  p : P
  q : Q
  ============================
  P
>>

    Rather than having to remember the exact syntax of the intro-pattern, Coq
    users can write a specialized tactic. *)

(* begin hide *)
Undo.
(* end hide *)

Ltac and_intro := intros [p q].

(** [and_intro] is just another tactic, and therefore is straightforward to
    use. *)

  intros P Q.
  and_intro.

(** This leaves the goal to prove in the exact same state as in our previous
    attempt, which is great because it was exactly the point. However, there is
    an issue with the [and_intro] command. To demonstrate it, let us consider a
    slightly different goal.  *)

(* begin hide *)
Abort.
(* end hide *)

Goal (forall (P Q : Prop), P /\ Q -> Q /\ P -> P).

(** The statement is not very interesting from a logical standpoint, but bear
    with me while I try to prove it. *)

Proof.
  intros P Q.
  and_intro.

(** Again, the goal is as we expect it to be:

<<
  P, Q : Prop
  p : P
  q : Q
  ============================
  P /\ Q -> P
>>

    We still have a premise of the form [P /\ Q] in the current goal… but at the
    same time, we also have hypotheses named [p] and [q] (the named used by
    <<and_intro>>) in the context. If we try to use <<and_intro>> again, Coq
    legitimely complains.

<<
p is already used.
>> *)
(* begin hide *)
Reset and_intro.
(* end hide *)

(** To tackle this apparent issue, Ltac provides a mechanic to fetch “fresh”
    (unused in the current context) names. *)

Ltac and_intro :=
  let p := fresh "p" in
  let q := fresh "q" in
  intros [p q].

(** This time, using [and_intro] several time works fine. In our previous
    example, the resulting goal is the following: *)

(**
<<
  P, Q : Prop
  p : P
  q, p0 : Q
  q0 : P
  ============================
  P
>> *)

(** Finally, tactics can take a set of arguments. They can be of various forms,
    but the most common to my experience is hypothesis name. For instance, we
    can write a tactic call <<destruct_and>> to… well, destruct an hypothesis of
    type [P /\ Q]. *)

Ltac destruct_and H :=
  let p := fresh "p" in
  let q := fresh "q" in
  destruct H as [Hl Hr].

(** With that, you can already write some very useful tactic aliases. It can
    save you quite some time when refactoring your definitions, but Ltac is
    capable of much more. *)

(** ** Printing Messages *)

(** One thing that can be useful while writing/debugging a tactic is the ability
    to print a message. You have to strategies available in Ltac as far as I
    know: [idtac] and [fail], where [idtac] does not stop the proof script on an
    error whereas [fail] does. *)

(** ** It Is Just Pattern Matching, Really *)

(** If you need to remember one thing from this blogpost, it is probably this:
    Ltac pattern matching features are amazing. That is, you will try to find in
    your goal and hypotheses relevant terms and sub terms you can work with.

    You can pattern match a value as you would do in Gallina, but in Ltac, the
    pattern match is also capable of more. The first case scenario is when you
    have a hypothesis name and you want to check its type: *)

Ltac and_or_destruct H :=
  let Hl := fresh "Hl" in
  let Hr := fresh "Hr" in
  match type of H with
  | _ /\ _
    => destruct H as [Hl Hr]
  | _ \/ _
    => destruct H as [Hl|Hr]
  end.

(** For the following incomplete proof script: *)

Goal (forall P Q, P /\ Q -> Q \/ P -> True).
  intros P Q H1 H2.
  and_or_destruct H1.
  and_or_destruct H2.

(** We get two sub goals:

<<
2 subgoals, subgoal 1 (ID 20)

  P, Q : Prop
  Hl : P
  Hr, Hl0 : Q
  ============================
  True

subgoal 2 (ID 21) is:
 True
>>
 *)

Abort.

(** We are not limited to constructors with the [type of] keyword, We can
    also pattern match using our own definitions. For instance: *)

Parameter (my_predicate: nat -> Prop).

Ltac and_my_predicate_simpl H :=
  match type of H with
  | my_predicate _ /\ _
    => destruct H as [Hmy_pred _]
  | _ /\ my_predicate _
    => destruct H as [_ Hmy_pred]
  end.

(** Last but not least, it is possible to introspect the current goal of your
    proof development: *)

Ltac rewrite_something :=
  match goal with
  | H:  ?x = _ |- context[?x]
    => rewrite H
  end.

(** So once again, as an example, the following proof script: *)

Goal (forall (x :nat) (equ : x = 2), x + 2 = 4).
  intros x equ.
  rewrite_something.

(** This leaves the following goal to prove:

<<
1 subgoal, subgoal 1 (ID 6)

  x : nat
  Heq : x = 2
  ============================
  2 + 2 = 4
>> *)
(* begin hide *)
Abort.
(* end hide *)
(** The [rewrite_something] tactic will search an equality relation to use to
    modify your goal. How does it work?

      - [match goal with] tells Coq we want to pattern match on the whole proof
        state, not only a known named hypothesis
      - [ H: ?x = _ |- _ ] is a pattern to tell coq we are looking for a
        hypothesis [_ = _]
      - [?x] is a way to bind the left operand of [=] to the name [x]
      - The right side of [|-] is dedicated to the current goal
      - [context[?x]] is a way to tell Coq we don’t really want to pattern-match
        the goal as a whole, but rather we are looking for a subterm of the form
        [?x]
      - [rewrite H] will be used in case Coq is able to satisfy the constrains
        specified by the pattern, with [H] being the hypothesis selected by Coq


    Finally, there is one last thing you really need to know before writing a
    tactic: the difference between [match] and [lazymatch]. Fortunately, it is
    pretty simple. One the one hand, with [match], if one pattern matches, but
    the branch body fails, Coq will backtrack and try the next branch. On the
    other hand, [lazymatch] will stop on error.

    So, for instance, the two following tactics will print two different
    messages: *)

Ltac match_failure :=
  match goal with
  | [ |- _ ]
    => fail "fail in first branch"
  | _
    => fail "fail in second branch"
  end.

Ltac match_failure' :=
  lazymatch goal with
  | [ |- _ ]
    => fail "fail in first branch"
  | _
    => fail "fail in second branch"
  end.

(** We can try that quite easily by starting a dumb goal (eg. [Goal (True).])
    and call our tactic. For [match_failure], we get:

<<
Ltac call to "match_failure" failed.
Error: Tactic failure: fail in second branch.
>>

    On the other hand, for [lazymatch_failure], we get:

<<
Ltac call to "match_failure'" failed.
Error: Tactic failure: fail in first branch.
>> *)

(** ** Conclusion *)

(** I were able to tackle my automation needs with these Ltac features. As
    always with Coq, there is more to learn. For instance, I saw that there is a
    third kind of pattern match ([multimatch]) I know nothing about. *)
