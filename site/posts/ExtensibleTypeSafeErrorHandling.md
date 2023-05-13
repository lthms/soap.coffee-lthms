---
published: 2018-02-04
modified: 2023-05-08
tags: ['haskell']
abstract: |
    Ever heard of “extensible effects?” By applying the same principle, but for
    error handling, the result is nice, type-safe API for Haskell, with a lot
    of GHC magic under the hood.
---

# Extensible Type-Safe Error Handling in Haskell

A colleague of mine introduced me to the benefits of
[`error-chain`](https://crates.io/crates/error-chain), a crate which aims to
implement “*consistent error handling*” for Rust. I found the overall design
pretty convincing, and in his use case, the crate really makes error handling
clearer and flexible. I knew [Pijul](https://pijul.org) was also using
`error-chain` at that time, but I never had the opportunity to dig more into it.

At the same time, I have read quite a lot about *extensible effects* in
Functional Programming, for an academic article I have submitted to [Formal
Methods 2018](http://www.fm2018.org)[^fm2018]. In particular, the
[freer](https://hackage.haskell.org/package/freer) package provides a very nice
API to define monadic functions which may use well-identified effects. For
instance, we can imagine that `Console`{.haskell} identifies the functions
which may print to and read from the standard output. A function
`askPassword`{.haskell} which displays a prompt and get the user password would
have this type signature:

[^fm2018]: The odds were in my favour: the aforementioned academic article has
    been accepted.

```haskell
askPassword :: Member Console r => Eff r ()
```

Compared to `IO`{.haskell}, `Eff`{.haskell} allows for meaningful type
signatures. It becomes easier to reason about function composition, and you
know that a given function which lacks a given effect in its type signature
will not be able to use them. As a predictable drawback, `Eff`{.haskell} can
become burdensome to use.

Basically, when my colleague showed me his Rust project and how he was using
`error-chain`, the question popped out. *Can we use an approach similar to
`Eff`{.haskell} to implement a Haskell-flavoured `error-chain`?*

Spoiler alert: the answer is yes. In this post, I will dive into the resulting
API, leaving for another time the details of the underlying implementation[^api].
Believe me, there is plenty to say. If you want to have a look already, the
current implementation can be found on
[GitHub](https://github.com/lthms/chain).

[^api]: For once, I wanted to write about the *result* of a project, instead of
    *how it is implemented*.

In this article, I will use several “advanced” GHC pragmas. I will not explain
each of them, but I will *try* to give some pointers for the reader who wants
to learn more.


## State of the Art

This is not an academic publication, and my goal was primarily to explore the
arcane of the Haskell type system, so I might have skipped the proper study of
the state of the art. That being said, I have written programs in Rust and
Haskell before.

### Starting Point

In Rust, `Result<T, E>`{.rust} is the counterpart of `Either E T`{.haskell} in
Haskell[^either]. You can use it to model to wrap either the result of a
function (`T`) or an error encountered during this computation (~E~). Both
`Either`{.haskell} and `Result`{.rust} are used in order to achieve the same
end, that is writing functions which might fail.

[^either]: I wonder if they deliberately choose to swap the two type arguments.

On the one hand, `Either E`{.haskell} is a monad. It works exactly as
`Maybe`{.haskell} (returning an error acts as a shortcut for the rest of the
function), but gives you the ability to specify *why* the function has failed.
To deal with effects, the `mtl` package provides `EitherT`{.haskell}, a
transformer version of `Either`{.haskell} to be used in a monad stack.

On the other hand, the Rust language provides the `?`{.rust} syntactic sugar,
to achieve the same thing. That is, both languages provide you the means to
write potentially failing functions without the need to care locally about
failure. If your function `f` uses a function `g` which might fail, and want to
fail yourself if `f` fails, it becomes trivial.

Out of the box, neither `EitherT`{.haskell} nor `Result`{.rust} is extensible.
The functions must use the exact same `E`, or errors must be converted
manually.

### Handling Errors in Rust

Rust and the `error-chain` crate provide several means to overcome this
limitation. In particular, it has the `Into`{.rust} and `From`{.rust} traits to
ease the conversion from one error to another. Among other things, the
`error-chain` crate provides a macro to easily define a wrapper around many
errors types, basically your own and the one defined by the crates you are
using.

I see several drawbacks to this approach. First, it is extensible if you take
the time to modify the wrapper type each time you want to consider a new error
type. Second, either you can either use one error type or every error
type.

However, the `error-chain` package provides a way to solve a very annoying
limitation of `Result`{.rust} and `Either`{.haskell}. When you “catch” an
error, after a given function returns its result, it can be hard to determine
from where the error is coming from. Imagine you are parsing a very complicated
source file, and the error you get is `SyntaxError`{.rust} with no additional
context. How would you feel?

`error-chain` solves this by providing an API to construct a chain of errors,
rather than a single value.

```rust
my_function().chain_err(|| "a message with some context")?;
```

The `chain_err` function makes it easier to replace a given error in its
context, leading to be able to write more meaningful error messages for
instance.

## The `ResultT`{.haskell} Monad

The `ResultT`{.haskell} is an attempt to bring together the extensible power of
`Eff`{.haskell} and the chaining of errors of `chain_err`. I will admit that,
for the latter, the current implementation of `ResultT`{.haskell} is probably
less powerful, but to be honest I mostly cared about the “extensible” thing, so
it is not very surprising.

This monad is not an alternative to neither Monad Stacks a la mtl nor to the
`Eff`{.haskell} monad. In its current state, it aims to be a more powerful and
flexible version of `EitherT`{.haskell}.

### Parameters

As often in Haskell, the `ResultT`{.haskell} monad can be parameterised in
several ways.

```haskell
data ResultT msg (err :: [*]) m a
```

- `msg`{.haskell} is the type of messages you can stack to provide more context
  to error handling
- `err`{.haskell} is a *row of errors*[^row], it basically describes the set of
  errors you will eventually have to handle
- `m`{.haskell} is the underlying monad stack of your application, knowing that
  `ResultT`{.haskell} is not intended to be stacked itself
- `a`{.haskell} is the expected type of the computation result

[^row]: You might have notice `err`{.haskell} is of kind `[*]`{.haskell}. To write such a thing,
    you will need the
    [`DataKinds`{.haskell}](https://www.schoolofhaskell.com/user/konn/prove-your-haskell-for-great-safety/dependent-types-in-haskell)
    GHC pragmas.

### `achieve`{.haskell} and `abort`{.haskell}

The two main monadic operations which comes with ~ResultT~ are ~achieve~ and
~abort~. The former allows for building the context, by stacking so-called
messages which describe what you want to do. The latter allows for bailing on a
computation and explaining why.

```haskell
achieve :: (Monad m)
        => msg
        -> ResultT msg err m a
        -> ResultT msg err m a
```

`achieve`{.haskell} should be used for `do`{.haskell} blocks. You can use
`<?>`{.haskell} to attach a contextual message to a given computation.

The type signature of `abort`{.haskell} is also interesting, because it
introduces the `Contains`{.haskell} typeclass (e.g., it is equivalent to
`Member`{.haskell} for `Eff`{.haskell}).

```haskell
abort :: (Contains err e, Monad m)
      => e
      -> ResultT msg err m a
```

This reads as follows: “*you can abort with an error of type `e`{.haskell} if
and only if the row of errors `err`{.haskell} contains the type
`e`{.haskell}.*”

For instance, imagine we have an error type `FileError`{.haskell} to describe
filesystem-related errors. Then, we can imagine the following function:

```haskell
readContent :: (Contains err FileError, MonadIO m)
            => FilePath
            -> ResultT msg err m String
```

We could leverage this function in a given project, for instance to read its
configuration files (for the sake of the example, it has several configuration
files). This function can use its own type to describe ill-formed description
(`ConfigurationError`{.haskell}).

```haskell
parseConfiguration :: (Contains err ConfigurationError, MonadIO m)
                   => String
                   -> String
                   -> ResultT msg err m Configuration
```

To avoid repeating `Contains`{.haskell} when the row of errors needs to
contains several elements, we introduce `:<`{.haskell}[^top] (read *subset or
equal*):

```haskell
getConfig :: ( '[FileError, ConfigurationError] :< err
             , MonadIO m)
             => ResultT String err m Configuration
getConfig = do
  achieve "get configuration from ~/.myapp directory" $ do
    f1 <- readContent "~/.myapp/init.conf"
              <?> "fetch the main configuration"
    f2 <- readContent "~/.myapp/net.conf"
              <?> "fetch the net-related configuration"

    parseConfiguration f1 f2
```

You might see, now, why I say ~ResultT~ is extensible. You can use two functions
with totally unrelated errors, as long as the caller advertises that with
~Contains~ or ~:<~.

[^top]: If you are confused by `:<`{.haskell}, it is probably because you were
    not aware that the
    [`TypeOperators`{.haskell}](https://ocharles.org.uk/blog/posts/2014-12-08-type-operators.html)
    GHC pragma was a thing.

### Recovering by Handling Errors

Monads are traps, you can only escape them by playing with their
rules. `ResultT`{.haskell} comes with `runResultT`{.haskell}.

```haskell
runResultT :: Monad m => ResultT msg '[] m a -> m a
```

This might be surprising: we can only escape out from the `ResultT`{.haskell}
if we do not use *any errors at all*. That is, `ResultT`{.haskell} forces us to
handle errors before calling `runResultT`{.haskell}.

`ResultT`{.haskell} provides several functions prefixed by `recover`{.haskell}.
Their type signatures can be a little confusing, so we will dive into the
simpler one:

```haskell
recover :: forall e m msg err a.
           (Monad m)
        => ResultT msg (e ': err) m a
        -> (e -> [msg] -> ResultT msg err m a)
        -> ResultT msg err m a
```

`recover`{.haskell} allows for *removing* an error type from the row of errors,
To do that, it requires to provide an error handler to determine what to do
with the error raised during the computation and the stack of messages at that
time. Using `recover`{.haskell}, a function may use more errors than advertised
in its type signature, but we know by construction that in such a case, it
handles these errors so that it is transparent for the function user. The type
of the handler is `e -> [msg] -> ResultT msg err m a`{.haskell}, which means
the handler *can raise errors if required*.

`recoverWhile msg`{.haskell} is basically a synonym for `achieve msg $
recover`{.haskell}. `recoverMany`{.haskell} allows for doing the same with a
row of errors, by providing as many functions as required. Finally,
`recoverManyWith`{.haskell} simplifies `recoverMany`{.haskell}: you can provide
only one function tied to a given typeclass, on the condition that the handling
errors implement this typeclass.

Using `recover`{.haskell} and its siblings often requires to help a bit the
Haskell type system, especially if we use lambdas to define the error handlers.
Doing that is usually achieved with the `Proxy a`{.haskell} dataype (where
`a`{.haskell} is a phantom type). I would rather use the
`TypeApplications`{.haskell} pragma[^tap].

```haskell
recoverManyWith @[FileError, NetworkError] @DescriptiveError
    (do x <- readFromFile f
        y <- readFromNetwork socket
        printToStd x y)
    printErrorAndStack
```

The `DecriptiveError`{.haskell} typeclass can be seen as a dedicated
`Show`{.haskell}, to give textual representation of errors. It is inspired by
the macros of `error_chain`.

We can start from an empty row of errors, and allows ourselves to
use more errors thanks to the `recover*` functions.

[^tap]: The
    [TypeApplications](https://medium.com/@zyxoas/abusing-haskell-dependent-types-to-make-redis-queues-safer-cc31db943b6c)
    pragmas is probably one of my favourites.

    When I use it, it feels almost like if I were writing a Coq document.

## `cat` in Haskell using `ResultT`{.haskell}

`ResultT`{.haskell} only cares about error handling. The rest of the work is up
to the underlying monad `m`{.haskell}. That being said, nothing forbids us to
provide fine-grained API, *e.g.*, for Filesystem-related functions. From an
error handling perspective, the functions provided by Prelude (the standard
library of Haskell) are pretty poor, and the documentation is not really
precise regarding the kind of error we can encounter while using it.

In this section, I will show you how we can leverage `ResultT`{.haskell} to
**(i)** define an error-centric API for basic file management functions and
**(ii)** use this API to implement a `cat`-like program which read a file and
print its content in the standard output.

### (A Lot Of) Error Types

We could have one sum type to describe in the same place all the errors we can
find, and later use the pattern matching feature of Haskell to determine which
one has been raised. The thing is, this is already the job done by the row of
errors of ~ResultT~. Besides, this means that we could raise an error for being
not able to write something into a file in a function which /opens/ a file.

Because ~ResultT~ is intended to be extensible, we should rather define several
types, so we can have a fine-grained row of errors. Of course, too many types
will become burdensome, so this is yet another time where we need to find the
right balance.

```haskell
newtype AlreadyInUse = AlreadyInUse FilePath
newtype DoesNotExist = DoesNotExist FilePath
data AccessDeny = AccessDeny FilePath IO.IOMode
data EoF = EoF
data IllegalOperation = IllegalRead | IllegalWrite
```

To be honest, this is a bit too much for the real life, but we are in a blog post
here, so we should embrace the potential of `ResultT`{.haskell}.

### Filesystem API

By reading the
[`System.IO`{.haskell}](https://hackage.haskell.org/package/base-4.9.1.0/docs/System-IO.html)
documentation, we can infer what our functions type signatures should look
like. I will not discuss their actual implementation in this article, as this
requires me to explain how `IO`{.haskell} deals with errors itself (and this
article is already long enough to my taste). You can have a look at [this
gist](https://gist.github.com/lthms/c669e68e284a056dc8c0c3546b4efe56) if you
are interested.

```haskell
openFile :: ( '[AlreadyInUse, DoesNotExist, AccessDeny] :< err
            , MonadIO m)
         => FilePath -> IOMode -> ResultT msg err m Handle

getLine :: ('[IllegalOperation, EoF] :< err, MonadIO m)
        => IO.Handle
        -> ResultT msg err m Text

closeFile :: (MonadIO m)
          => IO.Handle
          -> ResultT msg err m ()
```

### Implementing `cat`

We can use the `ResultT`{.haskell} monad, its monadic operations and our
functions to deal with the file system in order to implement a `cat`-like
program. I tried to comment on the implementation to make it easier to follow.

```haskell
cat :: FilePath -> ResultT String err IO ()
cat path =
  -- We will try to open and read this file to mimic
  -- `cat` behaviour.
  -- We advertise that in case something goes wrong
  -- the process.
  achieve ("cat " ++ path) $ do
    -- We will recover from a potential error,
    -- but we will abstract away the error using
    -- the `DescriptiveError` typeclass. This way,
    -- we do not need to give one handler by error
    -- type.
    recoverManyWith @[Fs.AlreadyInUse, Fs.DoesNotExist, Fs.AccessDeny, Fs.IllegalOperation]
                    @(Fs.DescriptiveError)
      (do f <- Fs.openFile path Fs.ReadMode
          -- `repeatUntil` works like `recover`, except
          -- it repeats the computation until the error
          -- actually happpens.
          -- I could not have used `getLine` without
          -- `repeatUntil` or `recover`, as it is not
          -- in the row of errors allowed by
          -- `recoverManyWith`.
          repeatUntil @(Fs.EoF)
              (Fs.getLine f >>= liftIO . print)
              (\_ _ -> liftIO $ putStrLn "%EOF")
          closeFile f)
      printErrorAndStack
    where
      -- Using the `DescriptiveError` typeclass, we
      -- can print both the stack of Strings which form
      -- the context, and the description of the generic
      -- error.
      printErrorAndStack e ctx = do
        liftIO . putStrLn $ Fs.describe e
        liftIO $ putStrLn "stack:"
        liftIO $ print ctx
```

The type signature of `cat`{.haskell} teaches us that this function handles any
error it might encounter. This means we can use it anywhere we want: both in
another computation inside `ResultT`{.haskell} which might raise errors
completely unrelated to the file system, or we can use it with
`runResultT`{.haskell}, escaping the `ResultT`{.haskell} monad (only to fall
into the `IO`{.haskell} monad, but this is another story).
