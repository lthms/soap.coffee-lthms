(** #<nav><p class="series">./coq.html</p>
     <p class="series-prev">./RewritingInCoq.html</p>
     <p class="series-next">./AlgebraicDatatypes.html</p></nav># *)

(** * A Study of Clight and its Semantics *)
(* begin hide *)
From Coq Require Import List.
Import ListNotations.
(* end hide *)
(** CompCert is a certified C compiler which comes with a proof of semantics
    preservation. What this means is the following: the semantics of the C code
    you write is preserved by CompCert compilation passes up to the generated
    machine code.

    I had been interested in CompCert for quite some times, and ultimately
    challenged myself to study Clight and its semantics. This write-up is the
    result of this challenge, written as I was progressing.

    #<nav id="generate-toc"></nav>#

    #<div id="history">site/posts/ClightIntroduction.v</div># *)

(** ** Installing CompCert *)

(** CompCert has been added to <<opam>>, and as a consequence can be very easily
    used as a library for other Coq developments. A typical use case is for a
    project to produce Clight (the high-level AST of CompCert), and to benefit
    from CompCert proofs after that.

    Installing CompCert is as easy as

<<
opam install coq-compcert
>>

    More precisely, this article uses #<code>coq-compcert.3.8</code>#.

    Once <<opam>> terminates, the <<compcert>> namespace becomes available. In
    addition, several binaries are now available if you have correctly set your
    <<PATH>> environment variable. For instance, <<clightgen>> takes a C file as
    an argument, and generates a Coq file which contains the Clight generated by
    CompCert. *)

(** ** Problem Statement *)

(** Our goal for this first write-up is to prove that the C function

<<
int add (int x, int y) {
    return x + y;
}
>>

    returns the expected result, that is <<x + y>>. The <<clightgen>> tool
    generates (among other things) the following AST (note: I have modified it
    in order to improve its readability). *)

From compcert Require Import Clight Ctypes Clightdefs AST
                             Coqlib Cop.

Definition _x : ident := 1%positive.
Definition _y : ident := 2%positive.

Definition f_add : function :=
  {| fn_return := tint
   ; fn_callconv := cc_default
   ; fn_params := [(_x, tint); (_y, tint)]
   ; fn_vars := []
   ; fn_temps := []
   ; fn_body := Sreturn
                  (Some (Ebinop Oadd
                                (Etempvar _x tint)
                                (Etempvar _y tint)
                                tint))
  |}.

(** The fields of the [function] type are pretty self-explanatory (as it is
    often the case in CompCert’s ASTs as far as I can tell for now).

    Identifiers in Clight are ([positive]) indices.  The [fn_body] field is of
    type [statement], with the particular constructor [Sreturn] whose argument
    is of type [option expr], and [statement] and [expr] look like the two main
    types to study.  The predicates [step1] and [step2] allow for reasoning
    about the execution of a [function], step by step (hence the name). It
    appears that <<clightgen>> generates Clight terms using the function call
    convention encoded by [step2].  To reason about a complete execution, it
    appears that we can use [star] (from the [Smallstep] module) which is
    basically a trace of [step]. These semantics are defined as predicates (that
    is, they live in [Prop]). They allow for reasoning about
    state-transformation, where a state is either

      - A function call, with a given list of arguments and a continuation
      - A function return, with a result and a continuation
      - A [statement] execution within a [function]

    We import several CompCert modules to manipulate _values_ (in our case,
    bounded integers). *)

From compcert Require Import Values Integers.
Import Int.

(** Putting everything together, the lemma we want to prove about [f_add] is
    the following. *)

Lemma f_add_spec (env : genv)
    (t : Events.trace)
    (m m' : Memory.Mem.mem)
    (v : val) (x y z : int)
    (trace : Smallstep.star step2 env
               (Callstate (Ctypes.Internal f_add)
                          [Vint x; Vint y]
                          Kstop
                          m)
               t
               (Returnstate (Vint z) Kstop m'))
  : z = add x y.

(** ** Proof Walkthrough *)

(** We introduce a custom [inversion] tactic which does some clean-up in
    addition to just perform the inversion. *)

Ltac smart_inv H :=
  inversion H; subst; cbn in *; clear H.

(** We can now try to prove our lemma. *)

Proof.

(** We first destruct [trace], and we rename the generated hypothesis in order
    to improve the readability of these notes. *)

  smart_inv trace.
  rename H into Hstep.
  rename H0 into Hstar.

(** This generates two hypotheses.

<<
Hstep : step1
          env
          (Callstate (Ctypes.Internal f_add)
                     [Vint x; Vint y]
                     Kstop
                     m)
          t1
          s2
Hstar : Smallstep.star
          step2
          env
          s2
          t2
          (Returnstate (Vint z) Kstop m')
>>

    In other words, to “go” from a [Callstate] of [f_add] to a [Returnstate],
    there is a first step from a [Callstate] to a state [s2], then a succession
    of steps to go from [s2] to a [Returnstate].

    We consider the single [step], in order to determine the actual value of
    [s2] (among other things). To do that, we use [smart_inv] on [Hstep], and
    again perform some renaming. *)

  smart_inv Hstep.
  rename le into tmp_env.
  rename e into c_env.
  rename H5 into f_entry.

(** This produces two effects. First, a new hypothesis is added to the context.

<<
f_entry : function_entry1
            env
            f_add
            [Vint x; Vint y]
            m
            c_env
            tmp_env
            m1
>>

    Then, the [Hstar] hypothesis has been updated, because we now have a more
    precise value of [s2]. More precisely, [s2] has become

<<
State
  f_add
  (Sreturn
    (Some (Ebinop Oadd
                  (Etempvar _x tint)
                  (Etempvar _y tint)
                  tint)))
  Kstop
  c_env
  tmp_env
  m1
>>

    Using the same approach as before, we can uncover the next step. *)

  smart_inv Hstar.
  rename H into Hstep.
  rename H0 into Hstar.

(** The resulting hypotheses are

<<
Hstep : step2 env
          (State
             f_add
             (Sreturn
               (Some
                 (Ebinop Oadd
                 (Etempvar _x tint)
                 (Etempvar _y tint)
                 tint)))
             Kstop c_env tmp_env m1) t1 s2
Hstar : Smallstep.star
          step2
          env
          s2
          t0
          (Returnstate (Vint z) Kstop m')
>>

    An inversion of [Hstep] can be used to learn more about its resulting
    state… So let’s do just that. *)

  smart_inv Hstep.
  rename H7 into ev.
  rename v0 into res.
  rename H8 into res_equ.
  rename H9 into mem_equ.

(** The generated hypotheses have become

<<
res : val
ev : eval_expr env c_env tmp_env m1
       (Ebinop Oadd
               (Etempvar _x tint)
               (Etempvar _y tint)
               tint)
       res
res_equ : sem_cast res tint tint m1 = Some v'
mem_equ : Memory.Mem.free_list m1
                               (blocks_of_env env c_env)
            = Some m'0
>>

    Our understanding of these hypotheses is the following

      - The expression [_x + _y] is evaluated using the [c_env] environment (and
        we know thanks to [binding] the value of [_x] and [_y]), and its result
        is stored in [res]
      - [res] is cast into a [tint] value, and acts as the result of [f_add]

    The [Hstar] hypothesis is now interesting

<<
Hstar : Smallstep.star
          step2 env
          (Returnstate v' Kstop m'0) t0
          (Returnstate (Vint z) Kstop m')
>>

    It is clear that we are at the end of the execution of [f_add] (even if Coq
    generates two subgoals, the second one is not relevant and easy to
    discard). *)

  smart_inv Hstar; [| smart_inv H ].

(** We are making good progress here, and we can focus our attention on the [ev]
    hypothesis, which concerns the evaluation of the [_x + _y] expression. We
    can simplify it a bit further. *)

  smart_inv ev; [| smart_inv H].
  rename H4 into fetch_x.
  rename H5 into fetch_y.
  rename H6 into add_op.

(** In a short-term, the hypotheses [fetch_x] and [fetch_y] are the most
    important.

<<
fetch_x : eval_expr env c_env tmp_env m1 (Etempvar _x tint) v1
fetch_y : eval_expr env c_env tmp_env m1 (Etempvar _y tint) v2
>>

    The current challenge we face is to prove that we know their value.  At this
    point, we can have a look at [f_entry]. This is starting to look familiar:
    [smart_inv], then renaming, etc. *)

  smart_inv f_entry.
  clear H.
  clear H0.
  clear H1.
  smart_inv H3; subst.
  rename H2 into allocs.

(** We are almost done. Let’s simplify as much as possible [fetch_x] and
    [fetch_y]. Each time, the [smart_inv] tactic generates two suboals, but only
    the first one is relevant. The second one is not, and can be discarded. *)

  smart_inv fetch_x; [| inversion H].
  smart_inv H2.
  smart_inv fetch_y; [| inversion H].
  smart_inv H2.

(** We now know the values of the operands of [add]. The two relevant hypotheses
    that we need to consider next are [add_op] and [res_equ]. They are easy to
    read.

<<
add_op : sem_binarith
           (fun (_ : signedness) (n1 n2 : Integers.int)
              => Some (Vint (add n1 n2)))
           (fun (_ : signedness) (n1 n2 : int64)
              => Some (Vlong (Int64.add n1 n2)))
           (fun n1 n2 : Floats.float
              => Some (Vfloat (Floats.Float.add n1 n2)))
           (fun n1 n2 : Floats.float32
              => Some (Vsingle (Floats.Float32.add n1 n2)))
           v1 tint v2 tint m1 = Some res
>>

      - [add_op] is the addition of [Vint x] and [Vint y], and its result is
        [res].

<<
res_equ : sem_cast res tint tint m1 = Some (Vint z)
>>

      - [res_equ] is the equation which says that the result of [f_add] is
        [res], after it has been cast as a [tint] value.

    We can simplify [add_op] and [res_equ], and this allows us to
    conclude. *)

  smart_inv add_op.
  smart_inv res_equ.
  reflexivity.
Qed.

(** ** Conclusion *)

(** The definitions of Clight are easy to understand, and the #<a
    href="http://compcert.inria.fr/doc/index.html">#CompCert
    documentation#</a># is very pleasant to read.  Understanding
    Clight and its semantics can be very interesting if you are
    working on a language that you want to translate into machine
    code. However, proving functional properties of a given C snippet
    using only CompCert can quickly become cumbersome. From this
    perspective, the #<a
    href="https://github.com/PrincetonUniversity/VST">#VST#</a>#
    project is very interesting, as its main purpose is to provide
    tools to reason about Clight programs more easily. *)
