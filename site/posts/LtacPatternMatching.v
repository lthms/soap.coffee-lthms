(** #<nav><p class="series">Ltac.html</p>
     <p class="series-prev">./LtacMetaprogramming.html</p>
     <p class="series-next">./MixingLtacAndGallina.html</p></nav># *)

(** * Pattern Matching on Types and Contexts  *)

(** In the #<a href="LtacMetaprogramming.html">#previous article#</a># of our
    series on Ltac, we have shown how tactics allow for constructing Coq terms
    incrementally.  Ltac programs (“proof scripts”) generate terms, and the
    shape of said terms can be very different regarding the initial context. For
    instance, [induction x] will refine the current goal using an inductive
    principle dedicated to the type of [x].

    This is possible because Ltac allows for pattern matching on types and
    contexts. In this article, we give a short introduction on this feature of
    key importance. *)

(** #<nav id="generate-toc"></nav>#

    #<div id="history">site/posts/LtacPatternMatching.v</div># *)

(** ** To [lazymatch] or to [match] *)

(** Gallina provides one pattern matching construction, whose semantics is
    always the same: for a given term, the first pattern to match will always be
    selected. On the contrary, Ltac provides several pattern matching
    constructions with different semantics. This key difference has probably
    been motivated because Ltac is not a total language: a tactic may not always
    succeed.

    Ltac programmers can use [match] or [lazymatch]. One the one hand, with
    [match], if one pattern matches, but the branch body fails, Coq will
    backtrack and try the next branch. On the other hand, [lazymatch] will stop
    on error.

    So, for instance, the two following tactics will print two different
    messages: *)

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
>>

    Moreover, pattern matching allows for matching over _patterns_, not just
    constants. Here, Ltac syntax differs from Gallina’s. In Gallina, if a
    variable name is used in a pattern, Gallina creates a new variable in the
    scope of the related branch. If a variable with the same name already
    existed, it is shadowed. On the contrary, in Ltac, using a variable name
    as-is in a pattern implies an equality check.

    To illustrate this difference, we can take the example of the following
    tactic. *)

Ltac successive x y :=
  lazymatch y with
  | S x => idtac
  | _ => fail
  end.

(** [successive x y] will fails if [y] is not the successor of [x]. On the
    contrary, the “syntactically equivalent” function in Gallina will exhibit
    a totally different behavior. *)

Definition successor (x y : nat) : bool :=
  match y with
  | S x => true
  | _ => false
  end.

(** Here, the first branch of the pattern match is systematically selected when
    [y] is not O, and in this branch, the argument [x] is shadowed by the
    predecessor of [y].

    For Ltac to adopt a behavior similar to Gallina, the [?] prefix shall be
    used. For instance, the following tactic will check whether its argument
    has a known successor, prints it if it does, or fail otherwise. *)

Ltac print_pred_or_zero x :=
  match x with
  | S ?x => idtac x
  | _ => fail
  end.

(** On the one hand, [print_pred_or_zero 3] will print [2]. On the other hand,
    if there exists a variable [x : nat] in the context, calling
    [print_pred_or_zero x] will fail, since the exact value of [x] is not
    known. *)

(** ** Pattern Matching on Types with [type of] *)

(** The [type of] operator can be used in conjunction to pattern matching to
    generate different terms according to the type of a variable. We could
    leverage this to reimplement <<induction>> for instance.

    As an example, we propose the following <<not_nat>> tactic which, given an
    argument [x], fails if [x] is of type [nat]. *)

Ltac not_nat x :=
  lazymatch type of x with
  | nat => fail "argument is of type nat"
  | _ => idtac
  end.

(** With this definition, <<not_nat true>> succeeds since [true] is of type
    [bool], and [not_nat O] since [O] encodes #<span class="imath">#0#</span># in
    [nat].

    We can also use the [?] prefix to write true pattern. For instance, the
    following tactic will fail if the type of its supplied argument has at least
    one parameter. *)

Ltac not_param_type x :=
  lazymatch type of x with
  | ?f ?a => fail "argument is of type with parameter"
  | _ => idtac
  end.

(** Both <<not_param_type (@nil nat)>> of type [list nat] and
    <<(@eq_refl nat 0)>> of type [0 = 0] fail, but <<not_param_type 0>> of type [nat]
    succeeds. *)

(** ** Pattern Matching on the Context with [goal] *)

(** Lastly, we discuss how Ltac allows for inspecting the context (i.e., the
    hypotheses and the goal) using the [goal] keyword.

    For instance, we propose a naive implementation of the [subst] tactic
    as follows. *)

Ltac subst' :=
  repeat
    match goal with
    | H :  ?x = _ |- context[?x]
      => repeat rewrite H; clear H
    end.

(** With [goal], patterns are of the form <<H : (pattern), ... |- (pattern)>>.

      - At the left side of [|-], we match on hypotheses. Beware that
        contrary to variable name in pattern, hypothesis names behaves as in
        Gallina (i.e., fresh binding, shadowing, etc.). In the branch, we are
        looking for equations, i.e., an hypothesis of the form [?x = _].
      - At the right side of [|-], we match on the goal.

    In both cases, Ltac makes available an interesting operator,
    [context[(pattern)]], which is satisfies if [(pattern)] appears somewhere in
    the object we are pattern matching against. So, the branch of the [match]
    reads as follows: we are looking for an equation [H] which specifies the
    value of an object [x] which appears in the goal. If such an equation
    exists, <<subst'>> tries to <<rewrite>> [x] as many time as possible.

    This implementation of [subst'] is very fragile, and will not work if the
    equation is of the form [_ = ?x], and it may behaves poorly if we have
    “transitive equations”, such as there exists hypotheses [?x = ?y] and [?y =
    _]. Motivated readers may be interested in proposing more robust
    implementation of [subst']. *)

(** ** Conclusion *)

(** This concludes our tour on Ltac pattern matching capabilities. In the #<a
    href="MixingLtacAndGallina.html">#next article of this series#</a>#, we
    explain how Ltac and Gallina can actually be used simultaneously. *)
