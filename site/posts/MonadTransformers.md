---
published: 2017-07-15
tags: ['haskell', 'opinions']
abstract: |
    Monads are hard to get right, monad transformers are harder. Yet, they
    remain a very powerful abstraction.
---

# Monad Transformers are a Great Abstraction

Monads are hard to get right. I think it took me around a year of Haskelling to
feel like I understood them. The reason is, to my opinion, there is not such
thing as *the* Monad. It is even the contrary. When someone asks me how I would
define Monads in only a few words, I say monads are a convenient formalism to
chain specific computations. Once I’ve got that, I started noticing “monadic
construction” everywhere, from the Rust `?`{.rust} operator to the [Elixir
`with`{.elixir} keyword](https://blog.drewolson.org/elixirs-secret-weapon/).

Haskell often uses another concept above Monads: Monad Transformers. This allows
you to work not only with *one* Monad, but rather a stack. Each Monad brings its
own properties and you can mix them into your very own one. That you can’t have
in Rust or Elixir, but it works great in Haskell. Unfortunately, it is not an
easy concept and it can be hard to understand. This article is not an attempt to
do so, but rather a postmortem review of one situation where I found them
extremely useful. If you think you have understood how they work, but don’t see
the point yet, you might find here a beginning of answer.

Recently, I ran into a very good example of why Monad Transformers worth it[^doubts]. I
have been working on a project called ogma for a couple years now. In a
nutshell, I want to build “a tool” to visualize in time and space a
storytelling. We are not here just yet, but in the meantime I have wrote a
software called `celtchar` to build a novel from a list of files. One of its
newest feature is the choice of language, and by extension, the typographic
rules. This information is read from a configuration file very early in the
program flow. Unfortunately, its use comes much later, after several function
calls.

[^doubts]: Time has passed since the publication of this article. Whether or
    not I remain in sync with its conclusions is an open question. Monad
    Transformers are a great abstraction, but nowadays I would probably try to
    choose another approach.

In Haskell, you deal with that kind of challenges by relying on the Reader
Monad. It carries an environment in a transparent way. The only thing is, I was
already using the State Monad to carry the computation result. But that’s not an
issue with the Monad Transformers.

```diff
-type Builder = StateT Text IO
+type Builder = StateT Text (ReaderT Language IO)
```

As you may have already understood, I wasn't using the “raw” `State`{.haskell}
Monad, but rather the transformer version `StateT`{.haskell}. The underlying
Monad was `IO`{.haskell}, because I needed to be able to read some files from
the filesystem. By replacing `IO`{.haskell} by `ReaderT Language IO`{.haskell},
I basically fixed my “carry the variable to the correct function call easily”
problem.

Retrieving the chosen language is as simple as:

```haskell
getLanguage :: Builder Language
getLanguage = lift ask
```

And that was basically it.

Now, my point is not that Monad Transformers are the ultimate beast we will have
to tame once and then everything will be shiny and easy[^funny]. There are a lot of
other way to achieve what I did with my `Builder`{.haskell} stack. For instance, in an
OO language, I probably would have to add a new class member to my `Builder`{.haskell}
class and I would have done basically the same thing.

[^funny]: It is amusing to see Past Me being careful here.

However, there is something I really like about this approach: the
`Builder`{.haskell} type definition gives you a lot of useful information
already. Both the `State`{.haskell} and `Reader`{.haskell} Monads have a well
established semantics most Haskellers will understand in a glance. A bit of
documentation won’t hurt, but I suspect it is not as necessary as one could
expect. Moreover, the presence of the `IO`{.haskell} Monad tells everyone using
the `Builder`{.haskell} Monad might cause I/O.
