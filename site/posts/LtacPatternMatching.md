---
published: 2020-08-28
tags: ['coq']
series:
  parent: series/Ltac.html
  prev: posts/LtacMetaprogramming.html
  next: posts/MixingLtacAndGallina.html
abstract: |
    Ltac allows for pattern matching on types and contexts. In this article, we
    give a short introduction on this feature of key importance. Ltac programs
    (“proof scripts”) generate terms, and the shape of said terms can be very
    different regarding the initial context. For instance, `induction x`{.coq}
    will refine the current goal using an inductive principle dedicated to the
    type of `x`{.coq}.
---

# Pattern Matching on Types and Contexts

In the [a previous article](/posts/LtacMetaprogramming.html) of our series on
Ltac, we have shown how tactics allow for constructing Coq terms incrementally.
Ltac programs (“proof scripts”) generate terms, and the shape of said terms can
be very different regarding the initial context. For instance, `induction
x`{.coq} will refine the current goal using an inductive principle dedicated to
the type of `x`{.coq}.

This is possible because Ltac allows for pattern matching on types and
contexts. In this article, we give a short introduction on this feature of
key importance.

## To `lazymatch`{.coq} or to `match`{.coq}

Gallina provides one pattern matching construction, whose semantics is always
the same: for a given term, the first pattern to match will always be selected.
On the contrary, Ltac provides several pattern matching constructions with
different semantics. This key difference has probably been motivated because
Ltac is not a total language: a tactic may not always succeed.

Ltac programmers can use `match`{.coq} or `lazymatch`{.coq}. One the one hand,
with `match`{.coq}, if one pattern matches, but the branch body fails, Coq will
backtrack and try the next branch. On the other hand, `lazymatch`{.coq} will
stop on error.

So, for instance, the two following tactics will print two different messages:

```coq
Ltac match_failure :=
  match goal with
  | _
    => fail "fail in first branch"
  | _
    => fail "fail in second branch"
  end.

Ltac lazymatch_failure :=
  lazymatch goal with
  | _
    => fail "fail in first branch"
  | _
    => fail "fail in second branch"
  end.
```

We can try that quite easily by starting a dumb goal (eg. `Goal (True).`{.coq})
and call our tactic. For `match_failure`{.coq}, we get:

```
Ltac call to "match_failure" failed.
Error: Tactic failure: fail in second branch.
```

On the other hand, for `lazymatch_failure`{.coq}, we get:

```
Ltac call to "match_failure'" failed.
Error: Tactic failure: fail in first branch.
```

Moreover, pattern matching allows for matching over *patterns*, not just
constants. Here, Ltac syntax differs from Gallina’s. In Gallina, if a
variable name is used in a pattern, Gallina creates a new variable in the
scope of the related branch. If a variable with the same name already
existed, it is shadowed. On the contrary, in Ltac, using a variable name
as-is in a pattern implies an equality check.

To illustrate this difference, we can take the example of the following
tactic.

```coq
Ltac successive x y :=
  lazymatch y with
  | S x => idtac
  | _ => fail
  end.
```

`successive x y`{.coq} will fails if `y`{.coq} is not the successor of
`x`{.coq}. On the contrary, the “syntactically equivalent” function in Gallina
will exhibit a totally different behavior.

```coq
Definition successor (x y : nat) : bool :=
  match y with
  | S x => true
  | _ => false
  end.
```

Here, the first branch of the pattern match is systematically selected when
`y`{.coq} is not `O`{.coq}, and in this branch, the argument `x`{.coq} is shadowed by the
predecessor of `y`{.coq}.

For Ltac to adopt a behavior similar to Gallina, the `?`{.coq} prefix shall be
used. For instance, the following tactic will check whether its argument
has a known successor, prints it if it does, or fail otherwise.

```coq
Ltac print_pred_or_zero x :=
  match x with
  | S ?x => idtac x
  | _ => fail
  end.
```

On the one hand, `print_pred_or_zero 3`{.coq} will print `2`{.coq}. On the
other hand, if there exists a variable `x : nat`{.coq} in the context, calling
`print_pred_or_zero x`{.coq} will fail, since the exact value of `x`{.coq} is
not known.

### Pattern Matching on Types with `type of`{.coq}

The `type of`{.coq} operator can be used in conjunction to pattern matching to
generate different terms according to the type of a variable. We could
leverage this to reimplement `induction`{.coq} for instance.

As an example, we propose the following `not_nat`{.coq} tactic which, given an
argument `x`{.coq}, fails if `x`{.coq} is of type `nat`{.coq}.

```coq
Ltac not_nat x :=
  lazymatch type of x with
  | nat => fail "argument is of type nat"
  | _ => idtac
  end.
```

With this definition, `not_nat true`{.coq} succeeds since `true`{.coq} is of
type `bool`{.coq}, and `not_nat O`{.coq} since `O`{.coq} encodes $0$ in
`nat`{.coq}.

We can also use the `?`{.coq} prefix to write true pattern. For instance, the
following tactic will fail if the type of its supplied argument has at least
one parameter.

```coq
Ltac not_param_type x :=
  lazymatch type of x with
  | ?f ?a => fail "argument is of type with parameter"
  | _ => idtac
  end.
```

Both `not_param_type (@nil nat)`{.coq} of type `list nat`{.coq} and `@eq_refl
nat 0`{.coq} of type `0 = 0`{.coq} fail, but `not_param_type 0`{.coq} of type
`nat`{.coq} succeeds. *)

## Pattern Matching on the Context with `goal`{.coq}

Lastly, we discuss how Ltac allows for inspecting the context (*i.e.*, the
hypotheses and the goal) using the `goal`{.coq} keyword.

For instance, we propose a naive implementation of the `subst`{.coq} tactic
as follows.

```coq
Ltac subst' :=
  repeat
    match goal with
    | H :  ?x = _ |- context[?x]
      => repeat rewrite H; clear H
    end.
```

With `goal`{.coq}, patterns are of the form `H : (pattern), ... |-
(pattern)`{.coq}.

- At the left side of `|-`{.coq}, we match on hypotheses. Beware that
  contrary to variable name in pattern, hypothesis names behaves as in
  Gallina (i.e., fresh binding, shadowing, etc.). In the branch, we are
  looking for equations, i.e., an hypothesis of the form `?x = _`{.coq}.
- At the right side of `|-`{.coq}, we match on the goal.

In both cases, Ltac makes available an interesting operator,
`context[(pattern)`{.coq}], which is satisfies if `(pattern)`{.coq} appears somewhere in
the object we are pattern matching against. So, the branch of the `match`{.coq}
reads as follows: we are looking for an equation `H`{.coq} which specifies the
value of an object `x`{.coq} which appears in the goal. If such an equation
exists, `subst'`{.coq} tries to `rewrite x`{.coq} as many time as possible.

This implementation of `subst'`{.coq} is very fragile, and will not work if the
equation is of the form `_ = ?x`{.coq}, and it may behaves poorly if we have
“transitive equations”, such as there exists hypotheses `?x = ?y`{.coq} and `?y
= _`{.coq}. Motivated readers may be interested in proposing more robust
implementation of `subst'`{.coq}.
