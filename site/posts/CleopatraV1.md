---
published: 2020-02-04
modified: 2023-05-12
tags: ['meta', 'literate-programming', 'emacs']
abstract: |
    Our literate programming toolchain cannot live solely inside Org files,
    waiting to be turned into actual code by Babel. Otherwise there we would
    not have any code to execute the first time we try to generate the website.
---

# A Literate Toolchain To Build This Website

A literate program is a particular type of software program where code is not
directly written in source files, but rather in a text document as code
snippets. In essence, literate programming allows for writing in the same place
both the software program and its technical documentation.

**`cleopatra`** is a “literate toolchain” I have implemented to build this
website, and you are currently reading it[^past]. That is, **`cleopatra`** is
both the build system and an article of this website! To achieve this,
**`cleopatra`** has been written as a collection of org files which can be
either “tangled” using [Babel](https://orgmode.org/worg/org-contrib/babel/) or
“exported” as a HTML document. Tangling here refers to extract marked code
blocks into files.

[^past]: This sentence was true when this article was published, but things
    have changed since then.

    What you are reading is actually the rendered version of a Markdown
    document that was manually “translated” from the Org original document,
    named `Bootstrap.org`. Interested readers can [have a look at the original
    version
    here](https://src.soap.coffee/soap.coffee/lthms.git/tree/site/cleopatra?id=9329e9883a52eb95c0803a46560c396d149ef2c6).

    Truth be told, said version is probably complete gibberish for anyone who
    isn’t me. For this reason, this version was actually heavily reworked…
    Because I have too much free time, probably.

The page you are currently reading is **`cleopatra`** entry point. Its
primary purpose is to define two Makefiles —`makefile` and `bootstrap.mk`—
and the necessary emacs-lisp script to tangle this document.

On the one hand, `makefile` is the main entrypoint of **`cleopatra`**. It
serves two purposes:

1. It initiates a few global variables, and
2. It provides a rule to tangle this document, that is to update itself and
   `bootstrap.mk`.

On the other hand, `bootstrap.mk` is used to declare the various “generation
processes” used to generate this website.

`makefile` and the emacs-lisp scripts are versioned, because they are necessary
to bootstrap **`cleopatra`**; but since they are also defined in this document,
it means **`cleopatra`** can update itself, in some sense. This is to be kept in mind
when modifying this document to hastily.

## Global Constants and Variables

First, `makefile` defines several global “constants”[^constants]. In a nutshell,

- `$ROOT`{.bash}  tells Emacs where the root of your website sources is, so
  that tangled output filenames can be given relative to it rather than the org
  files.  So for instance, the `block_src` tangle parameter for `Makefile`
  looks like `:tangle Makefile`{.lisp}, instead of `:tangle
  ../../Makefile`{.lisp}.
- `$CLEODIR`{.bash} tells **`cleopatra`** where its sources live. If you place
  it inside the `site/` directory (as it is intended), and you enable the use
  of `org` files to author your contents, then **`cleopatra`** documents will
  be part of your website. If you don’t want that, just move the directory
  outside the `site/` directory, and update the `$CLEODIR`{.bash} variable
  accordingly.

[^constants]: As far as I know, `make` does not support true *constant* values,
    It is assumed generation processes will not modify them.

For this website, these constants are defined as follows[^comments].

[^comments]: I will use a comment in the first line to recall to which file a
    given block code is expected to be tangled.

```makefile
# makefile:
ROOT := $(shell pwd)
CLEODIR := site/cleopatra
```

We then introduce two variables to list the output of the generation processes,
with two purposes in mind: keeping the `.gitignore` up-to-date automatically,
and providing rules to remove them.

- `$ARTIFACTS`{.bash} lists the short-term artifacts which can be removed
  frequently without too much hassle. They will be removed by `make clean`.
- `$CONFIGURE`{.bash} lists the long-term artifacts whose generation can be
  time consuming. They will only be removed by`~make cleanall`.

```makefile
# makefile:
ARTIFACTS := build.log
CONFIGURE :=

clean :
	@rm -rf ${ARTIFACTS}

cleanall : clean
	@rm -rf ${CONFIGURE}
```

Generation processes can declare new build outputs using the `+=` assignement
operators. Using another operator will likely provoke an undesirable result.

## Tangling Org Documents

**`cleopatra`** is a literate program implemented with Org mode, an Emacs major
editing mode. We provide the necessary bits to easily tangle Org documents.

The configuration of Babel is done using an emacs lisp script called
`tangle-org.el` whose status is similar to `Makefile`. It is part of the
bootstrap process, and therefore lives “outside” of **`cleopatra`** (it is not
deleted with `make clean` for instance).  However, it is overwritten when this
file is tangled. If you try to modify it and find that **`cleopatra`** does not
work properly, you should restore it.

```lisp
;;; tangle-org.el:
(require 'org)
(cd (getenv "ROOT"))
(setq org-confirm-babel-evaluate nil)
(setq org-src-preserve-indentation t)
(add-to-list 'org-babel-default-header-args
             '(:mkdirp . "yes"))
(org-babel-do-load-languages
 'org-babel-load-languages
 '((shell . t)))
(org-babel-tangle)
```

We define variables that ensure that the `$ROOT`{.bash} environment variable is
set and `tangle-org.el` is loaded when using Emacs.

```makefile
# makefile:
EMACSBIN := emacs
EMACS := ROOT="${ROOT}" ${EMACSBIN}
TANGLE := --batch \
          --load="${ROOT}/scripts/tangle-org.el" \
          2>> build.log
```

Finally, we introduce a [canned
recipe](https://www.gnu.org/software/make/manual/html_node/Canned-Recipes.html#Canned-Recipes)
to seamlessly tangle a given file[^canned].

[^canned]: It was the first time I had used canned recipes, and I don’t think I
    had the opportunity to re-use it ever again.

```makefile
# makefile:
define emacs-tangle =
echo "  tangle  $<"
${EMACS} $< ${TANGLE}
endef
```

## Updating `.gitignore` Automatically

Assuming each generation process correctly defines its `$ARTIFACTS`{.bash}
and `$CONFIGURE`{.bash} variables, we have all the information we need to
update `.gitignore` automatically.

This is done by adding markers in `.gitignore` to define a region under the
control of **`cleopatra`**, and writing a script to update said region after
each build.

```bash
# update-gitignore.sh:
BEGIN_MARKER="# begin generated files"
END_MARKER="# begin generated files"

# remove the previous list of generated files to ignore
sed -i -e "/${BEGIN_MARKER}/,/${END_MARKER}/d" .gitignore
# remove trailing empty lines
sed -i -e :a -e '/^\n*$/{$d;N;};/\n$/ba' .gitignore

# output the list of files to ignore
echo "" >> .gitignore
echo ${BEGIN_MARKER} >> .gitignore
for f in $@; do
    echo "${f}" >> .gitignore
done
echo ${END_MARKER} >> .gitignore
```

The `ignore` rule of `makefile` is defined as follows.

```makefile
# makefile:
ignore :
	@echo "  update  gitignore"
	@scripts/update-gitignore.sh \
	   ${ARTIFACTS} \
	   ${CONFIGURE}
```

## Bootstrapping

The core purpose of `makefile` remains to bootstrap the chain of generation
processes. This chain is divided into three stages: `prebuild`, `build`, and
`postbuild`.

This translates as follows in `makefile`.

```makefile
# makefile:
default : postbuild ignore

init :
	@rm -f build.log

prebuild : init

build : prebuild

postbuild : build

.PHONY : init prebuild build postbuild ignore
```

A *generation process* in **`cleopatra`** is a Makefile which provides rules for
these three stages, along with the utilities used by these rules. More
precisely, a generation process `proc` is defined in `proc.mk`. The rules of
`proc.mk` for each stage are expected to be prefixed by `proc-`, *e.g.*,
`proc-prebuild` for the `prebuild` stage.

Eventually, the following dependencies are expected between within the chain of
generation processes for every generation process.

```makefile
prebuild : proc-prebuild
build : proc-build
postbuild : proc-postbuild

proc-build : proc-prebuild
proc-postbuild : proc build
```

**`cleopatra`** is a literate toolchain whose main purpose is to allow me to
turn the scripts I wrote to generate my website into blogposts of said website.
As such, it allows me to implement the generation processes using Org mode,
which means that before being able to start generating HTML files,
**`cleopatra`** has to tangle the generation processes.

To achieve this, **`cleopatra`** relies on a particular behavior of `make`
regarding the `include` directive. If there exists a rule to generate a
Makefile used as an operand of `include`, `make` will use this rule to update
(if necessary) said Makefile before actually including it.

Therefore, the rules of the following form achieve our ambition of extensibility.

```makefile
include ${PROC}.mk

prebuild : ${PROC}-prebuild
build : ${PROC}-build
postbuild : ${PROC}-postbuild

${PROC}-prebuild : ${PROC}.mk ${AUX}
${PROC}-build : ${PROC}-prebuild
${PROC}-postbuild : ${PROC}-build

${PROC}.mk ${AUX} &:\
   ${CLEODIR}/${IN}
	@$(emacs-tangle)

CONFIGURE += ${PROC}.mk ${AUX}

.PHONY : ${PROC}-prebuild \
         ${PROC}-build \
         ${PROC}-postbuild
```

where

- `$IN`{.bash} is the Org document which contains the generation process code
- `$PROC`{.bash} is the name of the generation process
- `$AUX`{.bash} lists the utilities of the generation process tangled from
  `$IN`{.bash} with `$PROC.mk`{.bash}

We use `&:` is used in place of `:` to separate the target from its
dependencies in the “tangle rule.”[^obscure] This tells `make` that the recipe of this
rule generates all these files.

[^obscure]: Yet another obscure Makefile trick I have never encountered again.

Rather than writing these rules manually for each generation process we want to
define, we rely on to [noweb of
Babel](https://orgmode.org/worg/org-tutorials/org-latex-export.html). We call
`extends` the primitive to generate new generation processes.

We derive the rule to tangle `bootstrap.mk` using `extends`, using the following Org mode syntax.

```org
#+BEGIN_SRC makefile :noweb yes
# makefile:
<<extends(IN="Bootstrap.org", PROC="bootstrap", AUX="scripts/update-gitignore.sh")>>
#+END_SRC
```

which gives the following result.

```makefile
include bootstrap.mk

prebuild : bootstrap-prebuild
build : bootstrap-build
postbuild : bootstrap-postbuild

bootstrap-prebuild : bootstrap.mk scripts/update-gitignore.sh
bootstrap-build : bootstrap-prebuild
bootstrap-postbuild : bootstrap-build

bootstrap.mk scripts/update-gitignore.sh &:\
   ${CLEODIR}/Bootstrap.org
	@$(emacs-tangle)

CONFIGURE += bootstrap.mk scripts/update-gitignore.sh

.PHONY : bootstrap-prebuild \
         bootstrap-build \
         bootstrap-postbuild
```

These are the last lines of `makefile`. The rest of the generation processes will be
declared in `bootstrap.mk`.

## Generation Processes

In this section, we construct `bootstrap.mk` by enumerating the generation
processes that are currently used to generate the website you are reading.

We recall that each generation process shall

1. Define `proc-prebuild`, `proc-build`, and `proc-postbuild`
2. Declare dependencies between stages of generation processes
3. Declare build outputs (see `ARTIFACTS` and `CONFIGURE`)

### Theming and Templating

The
[`theme`](https://src.soap.coffee/soap.coffee/lthms.git/tree/site/cleopatra/Theme.org?id=9329e9883a52eb95c0803a46560c396d149ef2c6)
generation process controls the general appearance of the website. More
precisely, it introduces the main template used by `soupault`
(`main/templates.html`), and the main SASS sheet used by this template.

If a generation process produces a set of styles within a specific SASS files,
the current approach is

1. To make this file a dependency of `theme-build`
2. To modify `style/main.sass` in `theme`
   to import this file

Eventually, the second step will be automated, but, in the meantime,
this customization is mandatory.

### Configuring Soupault

The
[`soupault`](https://src.soap.coffee/soap.coffee/lthms.git/tree/site/cleopatra/Soupault.org?id=9329e9883a52eb95c0803a46560c396d149ef2c6)
generation configures and run `soupault`, in order to generate a static
website.

If a generation process `proc` produces files that will eventually be
integrated to your website, its `proc-build` recipe needs to be executed
*before* the `soupault-build` recipe. This can be enforced by making the
dependency explicit to `make`, *i.e.*,

```makefile
soupault-build : proc-build
```

Eventually, generation processes shall be allowed to produce specific `soupault`
widgets to be integrated into `soupault.conf`.

### Authoring Contents

The fact that **`cleopatra`** is a literate program which gradually generates
itself was not intended: it is a consequence of my desire to be able to easily
use whatever format I so desire for writing my contents, and Org documents in
particular.

In the present website, contents can be written in the following format:

- **HTML Files:** This requires no particular set-up, since HTML is the *lingua
  franca* of `soupault`.
- **Regular Coq files:** Coq is a system which allows writing machine-checked
  proofs, and it comes with a source “prettifier” called `coqdoc`. [Learn more
  about the generation process for Coq
  files](https://src.soap.coffee/soap.coffee/lthms.git/tree/site/cleopatra/Contents/Coq.org?id=9329e9883a52eb95c0803a46560c396d149ef2c6).
- **Org documents:** Emacs comes with a powerful editing mode called [Org
  mode](https://orgmode.org/), and Org documents are really pleasant to work
  with. [Learn more about the generation process for Org
  documents](https://src.soap.coffee/soap.coffee/lthms.git/tree/site/cleopatra/Contents/Org.org?id=9329e9883a52eb95c0803a46560c396d149ef2c6)
