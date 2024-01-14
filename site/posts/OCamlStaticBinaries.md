---
tags: ['ocaml']
published: 2023-12-31
modified: 2024-01-14
abstract: |
    Building static binaries can come in handy. Most notably, when the time
    comes to distribute executables. Fortunately, building static binaries from
    OCaml projects can be achieved pretty easily, when you know what you are
    doing.
---

# Building Static Binaries for OCaml Projects

Building static binaries can come in handy. Most notably, when the time comes
to distribute executables. I should know, because I spend a bit of time
recently preparing for [the 6th release of Spatial
Shell](./SpatialShell6.html), and part of that time was ensuring that folks on
Linux unwilling to build an OCaml project from source could still give my
project a shot.

Turns out, it can be achieved pretty easily, when you know what you are doing.
This is not the first article published on the Internet which explains how to
build static binaries, but (1) the ones I have found were a bit verbose and
hard to follow, and (2) the most recent versions of OCaml bring a new challenge
to tackle.

## Setting-Up a Dedicated `dune` Profile

At the root of your repository, create a `dune` file containing the following
stanza:

```lisp
(env
 (static
  (flags
   (:standard -cclib -static))))
```

This tells `dune` to passes specific arguments to the OCaml compiler when
called with the `--profile=static` command-line argument.

At this point, calling `dune build --profile=static` is likely to fail with
linking related errors. For instance, I got this one.

```
/sbin/ld: /usr/lib/gcc/x86_64-pc-linux-gnu/13.2.1/crt
beginT.o: relocation R_X86_64_32 against hidden symbol `__TMC_END__' can not be used when making a shared object
/sbin/ld: failed to set dynamic section sizes: bad value
collect2: error: ld returned 1 exit status
```

With OCaml 5.1.0 and OCaml 5.1.1, you are also likely to hit an error related
to `zstd`, which is a new runtime dependency for OCaml programs[^temp].

```
/sbin/ld: cannot find -lzstd: No such file or directory
collect2: error: ld returned 1 exit status
```

[^temp]: It looks like a temporary issue. If I understood correctly, the OCaml
    core developers are planning to remove said dependency in future versions
    of the compiler.


The solution for these two problems is the same.

## Setting Up a Specific Opam Switch

The OCaml compiler has a lot of so-called variants. The most famous is probably
[`flambda`](https://v2.ocaml.org/manual/flambda.html), which enables a series
of optimisations for native compilation.

Nowadays, enabling the specific features of a given variant is achieved by
installing the related `option` package when choosing your compiler version. In
our case, we have to install:

- `ocaml-option-static` (which will also enables `ocaml-option-musl`)
- `ocaml-option-no-compression` (for OCaml 5.1.0 and 5.1.1)

The minimal Opam invocation to create such a switch is:

```bash
opam switch create . --packages "ocaml-option-static,ocaml-option-no-compression,ocaml.5.1.1"
```

This particular configuration will produce static binaries using
[*musl*](https://musl.libc.org), a lightweight libc implementation that is way
more suited than the glibc when it comes to static binaries. This means you
will have to install *musl* on your system (it is more than likely that it is
packaged by your favorite distribution).

Additionally, you will have to provide the static versions (`.a`) of the system
libraries your project relies on. This part might be tricky to address, and is
very dependent on the particular system you are using. For instance, Debian
makes this a *lot* easier than Archlinux. This was typically what was happening
with `zstd`: Archlinux only distributed dynamic libraries, so no `.a` where
available on my laptop. Another example: if your project depends on
[Zarith](https://github.com/ocaml/Zarith), then you have a dependency to `gmp`.
You need to go and find the static library for it before moving to the next
section[^lucky].

[^lucky]: Of course, it is also possible that you are working on a pure OCaml
    project whose only real dependency is to the libc. Lucky you.

## Verifying the Resulting Binaries

Now is the time to call Dune again, with the `--profile=static` command-line
argument. Checking the result of your effort is as simple as calling `ldd` on
the binary compiled by Dune.

```
    not a dynamic executable
```

If `ldd` outputs something of this form, then you are good to go!

## Conclusion

This is, in a nutshell, the approach I am using to produce static binaries for
Spatial Shell releases. You can find the resulting script in [the project
repository](https://github.com/lthms/spatial-shell/blob/cc026c67a4645a01bf6cc6600e9e6baa87441fa8/scripts/prepare-release-artifacts.sh)
if you are interested.

If you have spotted an error in this article, or if you think the solution
proposed here can be improved, do not hesitate to reach out to me (ideally
though my [public inbox](mailto:~lthms/public-inbox@lists.sr.ht)). Or, even
better, open an issue on [Spatial Shell
tracker](https://github.com/lthms/spatial-shell/issues)! Afterall, these are
the very steps I’m relying on in order to provide static binaries, so I’d like
to know if I am doing something wrong 😅.
