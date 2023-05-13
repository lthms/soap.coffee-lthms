---
published: 2023-05-01
modified: 2023-05-02
tags: ['ocaml', 'neovim']
abstract: |
    Can we all agree that witnessing syntax highlighting being absolutely off
    is probably the most annoying thing that can happen to anybody?
---

# Neovim, OCaml Interfaces, Tree-Sitter and LSP

Can we all agree that witnessing syntax highlighting being absolutely off is
probably the most annoying thing that can happen to anybody?

I mean, just look at this horror.

#[Syntax highlighting being absolutely wrong.](/img/wrong-highlighting.png)

What you are looking at is the result of trying to enable `tree-sitter` for
OCaml hacking and calling it a day. In a nutshell, OCaml `mli` files are
quickly turning into a random mess of nonsensical colors, and I didn’t know
why. I tried to blame
[`tree-sitter-ocaml`](https://github.com/tree-sitter/tree-sitter-ocaml/issues/72),
but, of course I was wrong.

The issue is subtle, and to be honest, I don’t know if I totally grasp it. But
from my rough understanding, it breaks down as follows.

- `tree-sitter-ocaml` defines two grammars: `ocaml` for the `ml` files, and
  `ocaml_interface` (but `ocamlinterface` also works) for the `mli` files
- By default, neovim uses the filetype `ocaml` for `mli` files, so the incorrect
  parser is being used for syntax highlighting. This explains the root issue
- Bonus: `ocamllsp` does not recognize the `ocamlinterface` filetype by
  default (but somehow use the `ocaml.interface` id for `mli` files…[^contrib]).

[^contrib]: There is probably something to be done here.

So, in order to have both `tree-sitter` and `ocamllsp` working at the same
time, I had to tweak my configuration a little bit.

``` lua
lspconfig.ocamllsp.setup({
  filetypes = vim.list_extend(
    require('lspconfig.server_configurations.ocamllsp')
      .default_config
      .filetypes,
    { 'ocamlinterface' }
  ),
})

vim.cmd([[au! BufNewFile,BufRead *.mli setfiletype ocamlinterface]])
```

And now, I am blessed with a consistent syntax highlighting for my `mli` files.

#[Syntax highlighting being absolutely right.](/img/good-highlighting.png)
