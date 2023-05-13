---
published: 2018-06-17
tags: ['lisp']
abstract: |
    Common Lisp is a venerable programming languages like no other I know. From
    the creation of a Lisp package up to the creation of a standalone
    executable, we explore the shore of this strange beast.
---

# Discovering Common Lisp with `trivial-gamekit`

I always wanted to learn some Lisp dialect. In the meantime,
[lykan](https://github.com/lkn-org/lykan) —my Slayers Online clone— begins to
take shape. So, of course, my brain got an idea: *why not writing a client for
lykan in some Lisp dialect?*[^why] I asked on
[Mastodon](https://mastodon.social/@lthms/100135240390747697) if there were
good game engine for Lisp, and someone told me about
[`trivial-gamekit`](https://github.com/borodust/trivial-gamekit).

[^why]: Spoiler alert: this wasn’t the most efficient approach for the lykan
    project. But it was fun.

I have no idea if I will manage to implement a decent client using
trivial-gamekit, but why not trying? This article is the first of a series
about my experiments, discoveries and difficulties. The complete project
detailed in this article is available [as a
gist](https://gist.github.com/lthms/9833f4851843119c966917775b4c4180).

## Common Lisp, Quicklisp and `trivial-gamekit`

The trivial-gamekit
[website](https://borodust.github.io/projects/trivial-gamekit/) lists several
requirements. Two are related to Lisp:

1. Quicklisp
2. SBCL or CCL

[Quicklisp](https://quicklisp.org/beta) is an experimental package manager for
Lisp project, while SBCL and CCL are two Lisp implementations. I had already
installed [Clisp](https://www.archlinux.org/packages/?name=clisp), and it took
me quite some times to understand my mistake. Fortunately,
[SBCL](https://www.archlinux.org/packages/?name=sbcl) is also packaged in
ArchLinux.

With a compatible Lisp implementation, installing Quicklisp as a user is
straightforward. Following the website instructions is enough. At the end of
the process, you will have a new directory `${HOME}/quicklisp`{.bash}[^go].

[^go]: The purpose of this directory is similar to the [Go
    workspace](https://github.com/golang/go/wiki/SettingGOPATH).

Quicklisp is not a native feature of SBCL, and requires a small bit of
configuration to be made available automatically. You have to create a file
`${HOME}/.sbclrc`{.bash}, with the following content:

```lisp
(load "~/quicklisp/setup")
```

There is one final step to be able to use `trivial-gamekit`.

```bash
sbcl --eval '(ql-dist:install-dist "http://bodge.borodust.org/dist/org.borodust.bodge.txt")' \
     --quit
```

As of June 2018, Quicklisp [does not support
HTTPS](https://github.com/quicklisp/quicklisp-client/issues/167).

## Introducing Lysk

### Packaging

The first thing I search for when I learn a new language is how projects are
organized. From this perspective, `trivial-gamekit` pointed me directly to
Quicklisp

Creating a new Quicklisp project is straightforward. From my understanding, new
Quicklisp projects have to be located inside
`${HOME}/quicklisp/local-projects`{.bash}. I am not particularly happy with
this, but it is not really important.

The current code name of my Lisp game client is lysk.

```bash
mkdir ~/quicklisp/local-projects/lysk
```

Quicklisp packages (systems?) are defined through `asd` files.
I have firstly created `lysk.asd` as follows:

```lisp
(asdf:defsystem lysk
  :description "Lykan Game Client"
  :author "lthms"
  :license  "GPLv3"
  :version "0.0.1"
  :serial t
  :depends-on (trivial-gamekit)
  :components ((:file "package")
               (:file "lysk")))
```

`:serial t`{.lisp} means that the files detailed in the `components`{.lisp}
field depends on the previous ones. That is, `lysk.lisp` depends on
`package.lisp` in this case. It is possible to manage files dependencies
manually, with the following syntax:

```lisp
(:file "seconds" :depends-on "first")
```

I have declared only one dependency: `trivial-gamekit`. That way, Quicklisp
will load it for us.

The first “true” Lisp file we define in our skeleton is `package.lisp`.
Here is its content:

```lisp
(defpackage :lysk
  (:use :cl)
  (:export run app))
```

Basically, this means we use two symbols, `run`{.lisp} and `app`{.lisp}.

### A Game Client

The `lysk.lisp` file contains the program in itself. My first goal was to
obtain the following program: at startup, it shall creates a new window in
fullscreen, and exit when users release the left button of their mouse. It is
worth mentioning that I had to report [an issue to the `trivial-gamekit`
upstream](https://github.com/borodust/trivial-gamekit/issues/30) in order to
make my program work as expected.

While it may sounds scary —it suggests `trivial-gamekit` is a relatively young
project— the author has implemented a fix in less than an hour! He also took
the time to answer many questions I had when I joined the `#lispgames` Freenode
channel.

Before going any further, lets have a look at the complete file.

```lisp
(cl:in-package :lysk)

(gamekit:defgame app () ()
                 (:fullscreen-p 't))

(defmethod gamekit:post-initialize ((app app))
  (gamekit:bind-button :mouse-left :released
                       (lambda () (gamekit:stop))))

(defun run ()
  (gamekit:start 'app))
```

The first line is some kind of header, to tell Lisp the owner of the file.

The `gamekit:defgame`{.lisp} function allows for creating a new game
application (called `app`{.lisp} in our case). I ask for a fullscreen window
with `:fullscreen-p`{.lisp}. Then, we use the `gamekit:post-initialize`{.lisp}
hook to bind a handler to the release of the left button of our mouse. This
handler is a simple call to `gamekit:stop`{.lisp}. Finally, we define a new
function `run`{.lisp} which only starts our application.

Pretty straightforward!

### Running our Program

To “play” our game, we can start the SBCL REPL.

```bash
sbcl --eval '(ql:quickload :lysk)' --eval '(lysk:run)'
```

### A Standalone Executable

It looks like empower a REPL-driven development. That being said, once the
development is finished, I don't think I will have a lot of success if I ask my
future players to start sbcl to enjoy my game. Fortunately, `trivial-gamekit`
provides a dedicated function to bundle the game as a standalone executable.

Following the advises of the [**@borodust**](https://github.com/borodust) —the
`trivial-gamekit` author— I created a second package to that end. First, we
need to edit the `lysk.asd` file to detail a second package:

```lisp
(asdf:defsystem lysk/bundle
  :description "Bundle the Lykan Game Client"
  :author "lthms"
  :license  "GPLv3"
  :version "0.0.1"
  :serial t
  :depends-on (trivial-gamekit/distribution lysk)
  :components ((:file "bundle")))
  ```

This second package depends on lysk (our game client) and
trivial-gamekit/distribution. The latter provides the `deliver`{.lisp}
function, and we use it in the `bundle.lisp` file:

```lisp
(cl:defpackage :lysk.bundle
  (:use :cl)
  (:export deliver))

(cl:in-package :lysk.bundle)

(defun deliver ()
  (gamekit.distribution:deliver :lysk 'lysk:app))
```

To bundle the game, we can use SBCL from our command line interface.

```bash
sbcl --eval "(ql:quickload :lysk/bundle)" \
     --eval "(lysk.bundle:deliver)" \
     --quit
```

## Conclusion

Objectively, there is not much in this article. However, because I am totally
new to Lisp, it took me quite some time to get these few lines of code to work
together. All being told I think this constitutes a good `trivial-gamekit`
skeleton. Do not hesitate to us it this way.

Thanks again to [**@borodust**](https://github.com/borodust), for your time and
all your answers!

## Appendix: a Makefile

I like Makefile, so here is one to `run`{.lisp} the game directly, or
`bundle`{.lisp} it.

```makefile
run:
        @sbcl --eval "(ql:quickload :lysk)" \
              --eval "(lysk:run)"

bundle:
        @echo -en "[ ] Remove old build"
        @rm -rf build/
        @echo -e "\r[*] Remove old build"
        @echo "[ ] Building"
        @sbcl --eval "(ql:quickload :lysk/bundle)" \
              --eval "(lysk.bundle:deliver)" \
              --quit
        @echo "[*] Building"

.PHONY: bundle run
```
