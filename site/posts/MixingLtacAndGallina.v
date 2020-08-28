(** * Mixing Ltac and Gallina for Fun and Profit *)

(** One of the most misleading introduction to Coq is to say that “Gallina is
    for programs, while tactics are for proofs.”  Indeed, in Coq we construct
    terms of given types, always. Terms encodes both programs and proofs about
    these programs. Gallina is the preferred way to construct programs, and
    tactics are the preferred way to construct proofs.

    The key word here is “preferred.” We do not always need to use tactics to
    construct a proof term. Conversly, there are some occasions where
    constructing a program with tactics become handy. Furthermore, Coq actually
    allows for _mixing together_ Ltac and Gallina.

    In the #<a href="LtacPatternMatching.html">#previous article of this
    series#</a>#, we discuss how Ltac provides two very interesting features:

      - With [match goal with] it can inspect its context
      - With [match type of _ with] it can pattern matches on types

    It turns out these features are more than handy when it comes to
    metaprogramming (that is, the generation of programs by programs). *)

(** #<div id="generate-toc"></div>#

    #<div id="history">site/posts/MixingLtacAndGallina.v</div># *)

(** ** A Tale of Two Worlds, and Some Bridges *)

(** Constructing terms proofs directly in Gallina often happens when one is
    writing dependently-typed definition. For instance, we can write a type safe
    [from_option] function (inspired by #<a
    href="https://plv.csail.mit.edu/blog/unwrapping-options.html">#this very
    nice write-up#</a>#) such that the option to unwrap shall be accompagnied by
    a proof that said option contains something. This extra argument is used in
    the [None] case to derive a proof of [False], from which we can derive
    anything. *)

Definition is_some {α} (x : option α) : bool :=
  match x with Some _ => true | None => false end.

Lemma is_some_None {α} (x : option α)
  : x = None -> is_some x <> true.
Proof. intros H. rewrite H. discriminate. Qed.

Definition from_option {α}
    (x : option α) (some : is_some x = true)
  : α :=
  match x as y return x = y -> α with
  | Some x => fun _ => x
  | None => fun equ => False_rect α (is_some_None x equ some)
  end eq_refl.

(** In [from_option], we construct two proofs without using tactics:

      - [False_rect α (is_some_None x equ some)] to exclude the absurd case
      - [eq_refl] in conjunction with a dependent pattern matching (if you are
        not familiar with this trick: the main idea is to allow Coq to
        “remember” that [x = None] in the second branch)

    We can use another approach. We can decide to implement [from_option]
    with a proof script. *)

Definition from_option' {α}
    (x : option α) (some : is_some x = true)
  : α.

Proof.
  case_eq x.
  + intros y _.
    exact y.
  + intros equ.
    rewrite equ in some.
    now apply is_some_None in some.
Defined.

(** There is a third approach we can consider: mixing Gallina terms, and
    tactics. This is possible thanks to the [ltac:()] feature. *)

Definition from_option'' {α}
    (x : option α) (some : is_some x = true)
  : α :=
  match x as y return x = y -> α with
  | Some x => fun _ => x
  | None => fun equ => ltac:(rewrite equ in some;
                             now apply is_some_None in some)
  end eq_refl.

(** When Coq encounters [ltac:()], it treats it as a hole. It sets up a
    corresponding goal, and tries to solve it with the supplied tactic.

    Conversly, there exists ways to construct terms in Gallina when writing a
    proof script. Certains tactics takes such terms as arguments. Besides, Ltac
    provides [constr:()] and [uconstr:()] which work similarly to [ltac:()].
    The difference between [constr:()] and [uconstr:()] is that Coq will try to
    assign a type to the argument of [constr:()], but will leave the argument of
    [uconstr:()] untyped.

    For instance, consider the following tactic definition. *)

Tactic Notation "wrap_id" uconstr(x) :=
  let f := uconstr:(fun x => x) in
  exact (f x).

(** Both [x] the argument of [wrap_id] and [f] the anonymous identity function
    are not typed. It is only when they are composed together as an argument of
    [exact] (which expects a typed argument, more precisely of the type of the
    goal) that Coq actually tries to typecheck it.

    As a consequence, [wrap_id] generates a specialized identity function for
    each specific context. *)

Definition zero : nat := ltac:(wrap_id 0).

(** The generated anonymous identity function is [fun x : nat => x]. *)

Definition empty_list α : list α := ltac:(wrap_id nil).

(** The generated anonymous identity function is [fun x : list α => x]. Besides,
    we do not need to give more type information about [nil]. If [wrap_id] were
    to be expecting a typed term, we would have to replace [nil] by [(@nil
    α)]. *)

(** ** Beware the Automation Elephant in the Room *)

(** Proofs and computational programs are encoded in Coq as terms, but there is
    a fundamental difference between them, and it is highlighted by one of the
    axiom provided by the Coq standard library: proof irrelevance.

    Proof irrelevance states that two proofs of the same theorem (i.e., two
    proof terms which share the same type) are essentially equivalent, and can
    be substituted without threatening the trustworthiness of the system. From a
    formal methods point of view, it makes sense. Even if we value “beautiful
    proofs,” we mostly want correct proofs.

    The same reasoning does _not_ apply to computational programs. Two functions
    of type [nat -> nat -> nat] are unlikely to be equivalent.  For instance,
    [add], [mul] or [sub] share the same type, but computes totally different
    results.

    Using tactics such as [auto] to generate terms which do not live inside
    [Prop] is risky, to say the least. For instance, *)

Definition add (x y : nat) : nat := ltac:(auto).

(** This works, but it is certainly not what you would expect:

<<
add = fun _ y : nat => y
     : nat -> nat -> nat
>>

    That being said, if we keep that in mind, and assert the correctness of the
    generated programs (either by providing a proof, or by extensively testing
    it), there is no particular reason not to use Ltac to generate terms when it
    makes sens.

    Dependently-typed programming can help here. If we decorate the return type
    of a function with the expected properties of the result wrt. the function’s
    arguments, we can ensure the function is correct, and conversly prevent
    tactics such as [auto] to generate “incorrect” terms. Interested readers may
    refer to #<a href="/posts/StronglySpecifiedFunctions.html">#the dedicated
    series on this very website#</a>. *)
