---
abstract: |
    Using dependent types and the `Prop`{.coq} sort, it becomes possible to
    specify functions whose arguments and results are constrained by
    properties. However, implementing such functions can be challenging. In
    this series, we explore several approaches available to Coq developers.
---

# A Series on Strongly-Specified Functions in Coq

Using dependent types and the `Prop`{.coq} sort, it becomes possible to specify
functions whose arguments and results are constrained by properties. Using
such a “strongly-specified” function requires to provide a proof that the
supplied arguments satisfy the expected properties, and allows for soundly
assuming the results are correct too. However, implementing such functions can
be challenging. In this series, we explore several approaches available to Coq
developers.

@[series](.)
