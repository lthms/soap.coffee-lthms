---
published: 2023-01-26
tags: ['git', 'opinions']
abstract: |
    Could patch dependencies could help reduce the friction my branchless
    workflow suffers from when it comes to stacked MRs?
---

# Patch Dependencies for Stacked Git

Every time I catch myself thinking about dependencies between
changeset of a software project, the fascinating field of patch
theories comes to my mind.

A “patch theory” usually refers to the mathematical foundation behind
the data model of so-called Patch-based DVCS like Darcs and
Pijul. More precisely, a patch theory is an encoding of the state of a
repository, equipped with operations (gathered in so-called patches,
not to be confused with `GNU diff` patches) one can do to this
state. For instance, my rough understanding of Pijul’s patch theory is
that a repository is an oriented graph of lines, and a patch is a set
of operations onto this graph.

An interesting aspect of patch theory is that it requires a partial
order for its patches, from which a Patch-based DVCS derives a
dependency graph. In a nutshell, a patch $P$ depends on the patches
which are responsible for the presence of the lines that $P$
modifies.

I have always found this idea of a dependency graph for the patches
of a repository fascinating, because I though it would be a very
valuable tool in the context of software development.

I wanted to slightly change the definition of what a patch
dependency is, though. See, the partial order of Darcs and Pijul
focus on syntactic dependencies: the relation between lines in text
files. They need that to reconstruct these text files in the file
system of their users. As a software developers writing these text
files, I quickly realized these dependencies were of little interest
to me, though. What I wanted to be able to express was that a
feature introduced by a patch $P$ relied on a fix introduced by a
patch $P'$.

I have experimented with Darcs and Pijul quite a bit, with this idea
stuck in the back of my mind. At the end of this journey, I
convinced myself[^caution] (1) this beautiful idea I
had simply could not scale, and (2) neither I nor our industry is
ready to give up on the extensive ecosystem that has been built on top
of `git` just yet. As a consequence, my interest in Patch-based DVCS
decreased sensibly.

[^caution]: I am not trying to convince you, per say. This is a very personal
    and subjective feedback, it does not mean someone else couldn't reach a
    different conclusion.

Until very recently, that is. I got reminded of the appeal of a
dependency graph for changesets when I started adopted a Gitlab
workflow centered around Stacked Git and smaller, sometimes
interdependent MRs.

A manually curated graph dependency for a whole repository is not
practical, but what about my local queue of patches, patiently
waiting to be integrated into the upstream repository I am
contributing too?  Not only does it look like a more approachable
task, it could make synchronizing my stacked MRs a lot easier.

The workflow I have in mind would proceed as follows.

- Stacked Git’s `new` and `edit` commands could be extended to let
  developers declare dependencies between their patches. It would be
  the commands’ responsibility to enforce the wellfoundness of the
  dependency graph (*e.g.*, prevent the introduction of cycles in the
  graph, and maybe diamonds too[^diamond]).
- The `series` command could be improved to display the resulting
  dependency graph.
- `push` and `pop` would automatically take care (pushing or popping)
  of the selected patch(es) dependencies.
- Ideally, Stacked Git would get a new command `prepare <PATCH NAME>`
  which would pop every patches applied, then only only push `<PATCH
  NAME>` and its dependencies (in the reverse order). Developers could
  fix conflicts if need be. That is, Stacked Git would not be
  responsible for the consistency or correctness of the dependency
  graph.
- Stacked Git could get commands to detect potential issues with the
  dependency graph specified by the developer (mostly consisting in
  dry-run of `prepare` to check if it would lead to conflicts).

[^diamond]: At least in a first version. There is definitely value in being
    able to work with two independent patches in conjunction with a third one
    that needs them both. That being said, our goal here is to organize our
    work locally, and if it is made easier by declaring artificial dependency,
    this is a pragmatic sacrifice I am personally willing to make.

Because what we want is semantic dependencies, not syntactic dependencies
between patches, I really think it makes a lot of sense to completely delegate
the dependencies declaration to the developer[^future]. The very mundane
example that convinced me is the `CHANGELOG` file any mature software project
ends up maintaining. If the contribution guidelines require to modify the
`CHANGELOG` file in the same commit as a feature is introduced, then the
patches to two independent features will systematically conflict. This does not
mean, from my patch queue perspective, I should be forced to `pop` the first
commit before starting to work on the second one. It just means that when I
call `stg prepare`, I can have to fix a conflict, but fixing Git conflicts is
part of the job after all[^rerere]. If for some reasons solving a conflict
proves to be too cumbersome, I can always acknowledge that, and declare a new
dependency to the appropriate patch. It only means I and my reviewers will be
constrained a bit more than expected when dealing with my stack of MRs.

[^future]: Further versions of Stacked Git could explore computing the
    dependency graph automatically, similarly to what Git does. But I think
    that if Darcs and Pijul told us anything, it's that this computation is far
    from being trivial.

[^rerere]: And we have tools to help us. I wonder to which extends `git rerere`
    could save the day in some cases, for instance.

I am under the impression that this model extends quite nicely the current way
Stacked Git is working. To its core, it extends its data model to constraint a
bit `push` and `pop`, and empowers developers to organize a bit its local mess.
