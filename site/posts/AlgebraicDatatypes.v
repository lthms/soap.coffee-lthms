(** #<nav><p class="series">../coq.html</p>
     <p class="series-prev">./ClightIntroduction.html</p>
     <p class="series-next">./Coqffi.html</p></nav># *)

(** * Proving Algebraic Datatypes are “Algebraic” *)

(** Several programming languages allow programmers to define (potentially
    recursive) custom types, by composing together existing ones. For instance,
    in OCaml, one can define lists as follows:

<<
type 'a list =
| Cons of 'a * 'a list
| Nil
>>

    This translates in Haskell as

<<
data List a =
  Cons a (List a)
| Nil
>>

    In Rust:

<<
enum List<A> {
  Cons(A, Box< List<a> >),
  Nil,
}
>>

    In Coq:

<<
Inductive list a :=
| cons : a -> list a -> list a
| nil
>>

    And so forth.

    Each language will have its own specific constructions, and the type systems
    of OCaml, Haskell, Rust and Coq —to only cite them— are far from being
    equivalent. That being said, they often share a common “base formalism,”
    usually (and sometimes abusively) referred to as _algebraic datatypes_. This
    expression is used because under the hood any datatype can be encoded as a
    composition of types using two operators: sum ([+]) and product ([*]) for
    types.

      - [a + b] is the disjoint union of types [a] and [b]. Any term of [a]
        can be injected into [a + b], and the same goes for [b]. Conversely,
        a term of [a + b] can be projected into either [a] or [b].
      - [a * b] is the Cartesian product of types [a] and [b]. Any term of [a *
        b] is made of one term of [a] and one term of [b] (remember tuples?).

    For an algebraic datatype, one constructor allows for defining “named
    tuples”, that is ad-hoc product types. Besides, constructors are mutually
    exclusive: you cannot define the same term using two different constructors.
    Therefore, a datatype with several constructors is reminescent of a disjoint
    union.  Coming back to the [list] type, under the syntactic sugar of
    algebraic datatypes, the [list α] type is equivalent to [unit + α * list α],
    where [unit] models the [nil] case, and [α * list α] models the [cons] case.

    The set of types which can be defined in a language together with [+] and
    [*] form an “algebraic structure” in the mathematical sense, hence the
    name. It means the definitions of [+] and [*] have to satisfy properties
    such as commutativity or the existence of neutral elements. In this article,
    we will prove some of them in Coq. More precisely,

      - [+] is commutative, that is #<span class="imath">#\forall (x, y),\ x + y
        = y + x#</span>#
      - [+] is associative, that is #<span class="imath">#\forall (x, y, z),\ (x
        + y) + z = x + (y + z)#</span>#
      - [+] has a neutral element, that is #<span class="imath">#\exists e_s,
        \ \forall x,\ x + e_s = x#</span>#
      - [*] is commutative, that is #<span class="imath">#\forall (x, y),\ x * y
        = y * x#</span>#
      - [*] is associative, that is #<span class="imath">#\forall (x, y, z),\ (x
        * y) * z = x * (y * z)#</span>#
      - [*] has a neutral element, that is #<span class="imath">#\exists e_p,
        \ \forall x,\ x * e_p = x#</span>#
      - The distributivity of [+] and [*], that is #<span class="imath">#\forall
        (x, y, z),\ x * (y + z) = x * y + x * z#</span>#
      - [*] has an absorbing element, that is #<span class="imath">#\exists e_a,
        \ \forall x, \ x * e_a = e_a#</span>#

    For the record, the [sum] and [prod] types are defined in Coq as follows:

<<
Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B

Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B
>>

    #<nav id="generate-toc"></nav>#

    #<div id="history">site/posts/AlgebraicDatatypes.v</div># *)

From Coq Require Import
     Basics Setoid Equivalence Morphisms
     List FunctionalExtensionality.
Import ListNotations.

Set Implicit Arguments.

(** ** An Equivalence for [Type] *)

(** Algebraic structures come with _equations_ expected to be true.  This means
    there is an implicit dependency which is —to my opinion— too easily
    overlooked: the definition of [=]. In Coq, [=] is a built-in relation that
    states that two terms are “equal” if they can be reduced to the same
    “hierarchy” of constructors. This is too strong in the general case, and in
    particular for our study of algebraic structures of [Type]. It is clear
    that, to Coq’s opinion, [α + β] is not structurally _equal_ to [β + α], yet
    we will have to prove they are “equivalent.” *)

(** *** Introducing [type_equiv] *)

(** Since [=] for [Type] is not suitable for reasoning about algebraic
    datatypes, we introduce our own equivalence relation, denoted [==].  We say
    two types [α] and [β] are equivalent up to an isomorphism (denoted by [α ==
    β]) when for any term of type [α], there exists a counter-part term of type
    [β] and vice versa. In other words, [α] and [β] are equivalent if we can
    exhibit two functions [f] and [g] such that:

    #<span class="dmath">#\forall (x : α),\ x = g(f(x))#</span>#

    #<span class="dmath">#\forall (y : β),\ y = f(g(y))#</span>#

    In Coq, this translates into the following inductive types. *)

Reserved Notation "x == y" (at level 72).

Inductive type_equiv (α β : Type) : Prop :=
| mk_type_equiv (f : α -> β) (g : β -> α)
                (equ1 : forall (x : α), x = g (f x))
                (equ2 : forall (y : β), y = f (g y))
  : α == β
where "x == y" := (type_equiv x y).

(** As mentioned earlier, we prove two types are equivalent by exhibiting
    two functions, and proving these functions satisfy two properties. We
    introduce a <<Ltac>> notation to that end. *)

Tactic Notation "equiv" "with" uconstr(f) "and" uconstr(g)
  := apply (mk_type_equiv f g).

(** The tactic [equiv with f and g] will turn a goal of the form [α == β] into
    two subgoals to prove [f] and [g] form an isomorphism. *)

(** *** [type_equiv] is an Equivalence *)

(** [type_equiv] is an equivalence, and we can prove it by demonstrating it is
    (1) reflexive, (2) symmetric, and (3) transitive.

    [type_equiv] is reflexive. *)

Lemma type_equiv_refl (α : Type) : α == α.

(** This proof is straightforward. A type [α] is equivalent to itself because:

    #<span class="imath">#\forall (x : α),\ x = id(id(x))#</span># *)

Proof.
  now equiv with (@id α) and (@id α).
Qed.

(** [type_equiv] is symmetric. *)

Lemma type_equiv_sym {α β} (equ : α == β) : β == α.

(** If [α == β], then we know there exists two functions [f] and [g] which
    satisfy the expected properties. We can “swap” them to prove that [β == α].
    *)

Proof.
  destruct equ as [f g equ1 equ2].
  now equiv with g and f.
Qed.

(** [type_equiv] is transitive *)

Lemma type_equiv_trans {α β γ} (equ1 : α == β) (equ2 : β == γ)
  : α == γ.

(** If [α == β], we know there exists two functions [fα] and [gβ] which satisfy
    the expected properties of [type_equiv]. Similarly, because [β == γ], we
    know there exists two additional functions [fβ] and [gγ]. We can compose
    these functions together to prove [α == γ].

    As a reminder, composing two functions [f] and [g] (denoted by [f >>> g]
    thereafter) consists in using the result of [f] as the input of [g]: *)

Infix ">>>" := (fun f g x => g (f x)) (at level 70).

(** Then comes the proof. *)

Proof.
  destruct equ1 as [fα gβ equαβ equβα],
           equ2 as [fβ gγ equβγ equγβ].
  equiv with (fα >>> fβ) and (gγ >>> gβ).
  + intros x.
    rewrite <- equβγ.
    now rewrite <- equαβ.
  + intros x.
    rewrite <- equβα.
    now rewrite <- equγβ.
Qed.

(** The Coq standard library introduces the [Equivalence] type class. We can
    provide an instance of this type class for [type_equiv], using the three
    lemmas we have proven in this section. *)

#[refine]
Instance type_equiv_Equivalence : Equivalence type_equiv :=
  {}.

Proof.
  + intros x.
    apply type_equiv_refl.
  + intros x y.
    apply type_equiv_sym.
  + intros x y z.
    apply type_equiv_trans.
Qed.

(** *** Examples *)

(** **** [list]’s Canonical Form *)

(** We now come back to our initial example, given in the Introduction of this
    write-up. We can prove our assertion, that is [list α == unit + α * list
    α]. *)

Lemma list_equiv (α : Type)
  : list α == unit + α * list α.

Proof.
  equiv with (fun x => match x with
                       | [] => inl tt
                       | x :: rst => inr (x, rst)
                       end)
         and (fun x => match x with
                       | inl _ => []
                       | inr (x, rst) => x :: rst
                       end).
  + now intros [| x rst].
  + now intros [[] | [x rst]].
Qed.

(** **** [list] is a Morphism *)

(** This means that if [α == β], then [list α == list β]. We prove this by
    defining an instance of the [Proper] type class. *)

Instance list_Proper
  : Proper (type_equiv ==> type_equiv) list.

Proof.
  add_morphism_tactic.
  intros α β [f g equαβ equβα].
  equiv with (map f) and (map g).
  all: setoid_rewrite map_map; intros l.
  + replace (fun x : α => g (f x))
       with (@id α).
    ++ symmetry; apply map_id.
    ++ apply functional_extensionality.
       apply equαβ.
  + replace (fun x : β => f (g x))
       with (@id β).
    ++ symmetry; apply map_id.
    ++ apply functional_extensionality.
       apply equβα.
Qed.

(** The use of the [Proper] type class allows for leveraging hypotheses of the
    form [α == β] with the [rewrite] tactic. I personally consider providing
    instances of [Proper] whenever it is possible to be a good practice, and
    would encourage any Coq programmers to do so. *)

(** **** [nat] is a Special-Purpose [list] *)

(** Did you notice? Now, using [type_equiv], we can prove it! *)

Lemma nat_and_list : nat == list unit.

Proof.
  equiv with (fix to_list n :=
                match n with
                | S m => tt :: to_list m
                | _ => []
                end)
         and (fix of_list l :=
                match l with
                | _ :: rst => S (of_list rst)
                | _ => 0
                end).
  + induction x; auto.
  + induction y; auto.
    rewrite <- IHy.
    now destruct a.
Qed.

(** **** Non-empty Lists *)

(** We can introduce a variant of [list] which contains at least one element by
    modifying the [nil] constructor so that it takes one argument instead of
    none. *)

Inductive non_empty_list (α : Type) :=
| ne_cons : α -> non_empty_list α -> non_empty_list α
| ne_singleton : α -> non_empty_list α.

(** We can demonstrate the relation between [list] and [non_empty_list], which
    reveals an alternative implementation of [non_empty_list]. More precisely,
    we can prove that [forall (α : Type), non_empty_list α == α * list α].  It
    is a bit more cumbersome, but not that much. We first define the conversion
    functions, then prove they satisfy the properties expected by
    [type_equiv]. *)

Fixpoint non_empty_list_of_list {α} (x : α) (l : list α)
  : non_empty_list α :=
  match l with
  | y :: rst => ne_cons x (non_empty_list_of_list y rst)
  | [] => ne_singleton x
  end.

#[local]
Fixpoint list_of_non_empty_list {α} (l : non_empty_list α)
  : list α :=
  match l with
  | ne_cons x rst => x :: list_of_non_empty_list rst
  | ne_singleton x => [x]
  end.

Definition prod_list_of_non_empty_list {α} (l : non_empty_list α)
  : α * list α :=
  match l with
  | ne_singleton x => (x, [])
  | ne_cons x rst => (x, list_of_non_empty_list rst)
  end.

Lemma ne_list_list_equiv (α : Type)
  : non_empty_list α == α * list α.

Proof.
  equiv with prod_list_of_non_empty_list
         and (prod_curry non_empty_list_of_list).
  + intros [x rst|x]; auto.
    cbn.
    revert x.
    induction rst; intros x; auto.
    cbn; now rewrite IHrst.
  + intros [x rst].
    cbn.
    destruct rst; auto.
    change (non_empty_list_of_list x (α0 :: rst))
      with (ne_cons x (non_empty_list_of_list α0 rst)).
    replace (α0 :: rst)
      with (list_of_non_empty_list
              (non_empty_list_of_list α0 rst)); auto.
    revert α0.
    induction rst; intros y; [ reflexivity | cbn ].
    now rewrite IHrst.
Qed.

(** ** The [sum] Operator *)

(** *** [sum] is a Morphism *)

(** This means that if [α == α'] and [β == β'], then [α + β == α' + β']. To
    prove this, we compose together the functions whose existence is implied by
    [α == α'] and [β == β']. To that end, we introduce the auxiliary function
    [lr_map]. *)

Definition lr_map_sum {α β α' β'} (f : α -> α') (g : β -> β')
    (x : α + β)
  : α' + β' :=
  match x with
  | inl x => inl (f x)
  | inr y => inr (g y)
  end.

(** Then, we prove [sum] is a morphism by defining a [Proper] instance. *)

Instance sum_Proper
  : Proper (type_equiv ==> type_equiv ==> type_equiv) sum.

Proof.
  add_morphism_tactic.
  intros α α' [fα gα' equαα' equα'α]
         β β' [fβ gβ' equββ' equβ'β].
  equiv with (lr_map_sum fα fβ)
         and (lr_map_sum gα' gβ').
  + intros [x|y]; cbn.
    ++ now rewrite <- equαα'.
    ++ now rewrite <- equββ'.
  + intros [x|y]; cbn.
    ++ now rewrite <- equα'α.
    ++ now rewrite <- equβ'β.
Qed.

(** *** [sum] is Commutative *)

Definition sum_invert {α β} (x : α + β) : β + α :=
  match x with
  | inl x => inr x
  | inr x => inl x
  end.

Lemma sum_com {α β} : α + β == β + α.

Proof.
  equiv with sum_invert and sum_invert;
    now intros [x|x].
Qed.

(** *** [sum] is Associative *)

(** The associativity of [sum] is straightforward to prove, and should not pose
    a particular challenge to perspective readers; if we assume that this
    article is well-written, that is!  *)

Lemma sum_assoc {α β γ} : α + β + γ == α + (β + γ).

Proof.
  equiv with (fun x =>
                match x with
                | inl (inl x) => inl x
                | inl (inr x) => inr (inl x)
                | inr x => inr (inr x)
                end)
         and (fun x =>
                match x with
                | inl x => inl (inl x)
                | inr (inl x) => inl (inr x)
                | inr (inr x) => inr x
                end).
  + now intros [[x|x]|x].
  + now intros [x|[x|x]].
Qed.

(** *** [sum] has a Neutral Element *)

(** We need to find a type [e] such that [α + e == α] for any type [α]
    (similarly to #<span class="imath">#x~+~0~=~x#</span># for any natural
    number #<span class="imath">#x#</span># that is).

    Any empty type (that is, a type with no term such as [False]) can act as the
    natural element of [Type]. As a reminder, empty types in Coq are defined
    with the following syntax: *)

Inductive empty := .

(** Note that the following definition is erroneous.

<<
Inductive empty.
>>

   Using [Print] on such a type illustrates the issue.

<<
Inductive empty : Prop := Build_empty {  }
>>

    That is, when the [:=] is omitted, Coq defines an inductive type with one
    constructor.

    Coming back to [empty] being the neutral element of [sum]. From a high-level
    perspective, this makes sense. Because we cannot construct a term of type
    [empty], then [α + empty] contains exactly the same numbers of terms as [α].
    This is the intuition. Now, how can we convince Coq that our intuition is
    correct? Just like before, by providing two functions of types:

      - [α -> α + empty]
      - [α + empty -> α]

    The first function is [inl], that is one of the constructor of [sum].

    The second function is more tricky to write in Coq, because it comes down to
    writing a function of type is [empty -> α]. *)

Definition from_empty {α} : empty -> α :=
  fun x => match x with end.

(** It is the exact same trick that allows Coq to encode proofs by
    contradiction.

    If we combine [from_empty] with the generic function *)

Definition unwrap_left_or {α β}
    (f : β -> α) (x : α + β)
  : α :=
  match x with
  | inl x => x
  | inr x => f x
  end.

(** Then, we have everything to prove that [α == α + empty]. *)

Lemma sum_neutral (α : Type) : α == α + empty.

Proof.
  equiv with inl and (unwrap_left_or from_empty);
    auto.
  now intros [x|x].
Qed.

(** ** The [prod] Operator *)

(** This is very similar to what we have just proven for [sum], so expect less
    text for this section. *)

(** *** [prod] is a Morphism *)

Definition lr_map_prod {α α' β β'}
    (f : α -> α') (g : β -> β')
  : α * β -> α' * β' :=
  fun x => match x with (x, y) => (f x, g y) end.

Instance prod_Proper
  : Proper (type_equiv ==> type_equiv ==> type_equiv) prod.

Proof.
  add_morphism_tactic.
  intros α α' [fα gα' equαα' equα'α]
         β β' [fβ gβ' equββ' equβ'β].
  equiv with (lr_map_prod fα fβ)
         and (lr_map_prod gα' gβ').
  + intros [x y]; cbn.
    rewrite <- equαα'.
    now rewrite <- equββ'.
  + intros [x y]; cbn.
    rewrite <- equα'α.
    now rewrite <- equβ'β.
Qed.

(** *** [prod] is Commutative *)

Definition prod_invert {α β} (x : α * β) : β * α :=
  (snd x, fst x).

Lemma prod_com {α β} : α * β == β * α.

Proof.
  equiv with prod_invert and prod_invert;
    now intros [x y].
Qed.

(** *** [prod] is Associative *)

Lemma prod_assoc {α β γ}
  : α * β * γ == α * (β * γ).

Proof.
  equiv with (fun x =>
                match x with
                | ((x, y), z) => (x, (y, z))
                end)
         and (fun x =>
                match x with
                | (x, (y, z)) => ((x, y), z)
                end).
  + now intros [[x y] z].
  + now intros [x [y z]].
Qed.

(** *** [prod] has a Neutral Element *)

Lemma prod_neutral (α : Type) : α * unit == α.

Proof.
  equiv with fst and ((flip pair) tt).
  + now intros [x []].
  + now intros.
Qed.

(** ** [prod] has an Absorbing Element *)

(** And this absorbing element is [empty], just like the absorbing element of
    the multiplication of natural number is #<span class="imath">#0#</span>#
    (the neutral element of the addition). *)

Lemma prod_absord (α : Type) : α * empty == empty.

Proof.
  equiv with (snd >>> from_empty)
         and (from_empty).
  + intros [_ []].
  + intros [].
Qed.

(** ** [prod] and [sum] Distributivity *)

(** Finally, we can prove the distributivity property of [prod] and [sum] using
    a similar approach to prove the associativity of [prod] and [sum]. *)

Lemma prod_sum_distr (α β γ : Type)
  : α * (β + γ) == α * β + α * γ.

Proof.
  equiv with (fun x => match x with
                       | (x, inr y) => inr (x, y)
                       | (x, inl y) => inl (x, y)
                       end)
         and (fun x => match x with
                       | inr (x, y) => (x, inr y)
                       | inl (x, y) => (x, inl y)
                       end).
  + now intros [x [y | y]].
  + now intros [[x y] | [x y]].
Qed.

(** ** Bonus: Algebraic Datatypes and Metaprogramming *)

(** Algebraic datatypes are very suitable for generating functions, as
    demonstrated by the automatic deriving of typeclass in Haskell or trait in
    Rust. Because a datatype can be expressed in terms of [sum] and [prod], you
    just have to know how to deal with these two constructions to start
    metaprogramming.

    We can take the example of the [fold] functions. A [fold] function is a
    function which takes a container as its argument, and iterates over the
    values of that container in order to compute a result.

    We introduce [fold_type INPUT CANON_FORM OUTPUT], a tactic to compute the
    type of the fold function of the type <<INPUT>>, whose “canonical form” (in
    terms of [prod] and [sum]) is <<CANON_FORM>> and whose result type is
    #<code>#OUTPUT#</code>#. Interested readers have to be familiar with
    [Ltac]. *)

Ltac fold_args b a r :=
  lazymatch a with
  | unit =>
    exact r
  | b =>
    exact (r -> r)
  | (?c + ?d)%type =>
    exact (ltac:(fold_args b c r) * ltac:(fold_args b d r))%type
  | (b * ?c)%type =>
    exact (r -> ltac:(fold_args b c r))
  | (?c * ?d)%type =>
    exact (c -> ltac:(fold_args b d r))
  | ?a =>
    exact (a -> r)
  end.

Ltac currying a :=
  match a with
  | ?a * ?b -> ?c => exact (a -> ltac:(currying (b -> c)))
  | ?a => exact a
  end.

Ltac fold_type b a r :=
  exact (ltac:(currying (ltac:(fold_args b a r) -> b -> r))).

(** We use it to compute the type of a [fold] function for [list]. *)

Definition fold_list_type (α β : Type) : Type :=
  ltac:(fold_type (list α) (unit + α * list α)%type β).

(** Here is the definition of [fold_list_type], as outputed by [Print].

<<
fold_list_type =
  fun α β : Type => β -> (α -> β -> β) -> list α -> β
     : Type -> Type -> Type
>>

    It is exactly what you could have expected (as match the type of
    [fold_right]).

    Generating the body of the function is possible in theory, but probably not
    in [Ltac] without modifying a bit [type_equiv]. This could be a nice
    use-case for #<a href="https://github.com/MetaCoq/metacoq">#MetaCoq#</a>#,
    though.  *)
