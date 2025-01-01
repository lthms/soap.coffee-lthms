---
published: 2024-08-16
modified: 2024-12-13
feature: yes
tags: ['satire', 'ocaml']
abstract: |
    Do you know what vestigal structures are?
---

# On Vestigial Structures

Do you know what vestigial structures are?[^gpt]

[^gpt]: This write-up is a slightly modified version of a commit description I have
    written for `$WORK`{.bash} with [some help from ChatGPT][script].

In a nutshell, they are remnants of structures that were functional in an
ancestral species but have lost much or all of their original function in the
descendant species.

For instance, some snakes, like pythons and boas, have tiny remnants of hind
leg bones, which are vestigial structures from when their ancestors had legs.
Birds like ostriches and emus have wings that are too small for flight. These
wings are vestigial structures as well, remnants of their flying ancestors.
Even humans have some, like those small muscles around their ears. These
muscles were once used by our ancestors to move their ears, similar to how many
animals can today.

Sometimes, vestigial structures are not just useless, they can be harmful. Take
our wisdom teeth. They were handy to our ancestors, who had larger jaws and a
diet that required more chewing. Sadly, they have become problematic for many
modern humans.

Anyway, `ocaml-migrate-parsetree` is a deprecated OCaml library in
`$WORK`{.bash}’s dependency tree that will never be compatible with OCaml 5,
but it turns out [we do not need it anymore][commit].

[script]: https://chatgpt.com/share/f9c72991-7502-4048-9c10-0db5c93726be
[commit]: https://gitlab.com/tezos/tezos/-/commit/9973676470b5582eb08cb430551e030abba9d5aa
