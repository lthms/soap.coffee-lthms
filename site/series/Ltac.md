---
abstract: |
    Ltac is the “tactic language” of Coq. It is commonly advertised as the
    common approach to write proofs, which tends to bias how it is introduced
    to new Coq users. In this series, we present Ltac as the metaprogramming
    tool it is, since fundamentally it is an imperative language which allows
    for constructing Coq terms interactively and incrementally.
---

# A Series on Ltac

Ltac is the “tactic language” of Coq. It is commonly advertised as the common
approach to write proofs, which tends to bias how it is introduced to
new Coq users[^anecdote]. In this series, we present Ltac as the
metaprogramming tool it is, since fundamentally it is an imperative
language which allows for constructing Coq terms interactively and
incrementally.

[^anecdote]: I know *I* was introduced to Coq in a similar way in
    my Master courses.

@[series](Test)
