---
published: 2023-01-16
tags: ['stacked-git', 'workflow']
abstract: |
    One year has passed, and I keep using Stacked Git almost daily. How I am
    using it has slightly changed, though.
---

# How I Keep Using Stacked Git at `$WORK`{.bash}

One year ago, I have published an article summarizing [my experience using
Stacked Git at `$WORK`{.bash}](/posts/StackedGit.html). Twelve months later,
enough has changed to motivate a spin-off piece.

## Stacked Git is *Fast*

Firstly, it is important to state that my main complaint about
Stacked Git is now a thing of the past[^edit]! Stacked Git does not feel slow
anymore, and far from it. This is because [Stacked Git 2.0 has been rewritten
in Rust](https://github.com/stacked-git/stgit/discussions/185). While RiiR
(*Rewrite it in Rust*) is a running meme on the Internet, in this particular
case, the result is very exciting.

[^edit]: For fairness, I have removed the related section in my previous
    write-up.

Thanks to the performance boost, my Zsh prompt does not take 0.1s to
appear!

Speaking of Zsh prompt, basically what I ended up displaying is `(<TOP PATCH
NAME> <APPLIED PATCHES COUNT>/<PATCHSET SIZE> <HIDDEN PATCHES COUNT)`. For
instance, `(fix-1337 1/2 3)`.

In case you want to take inspiration in my somewhat working configuration, here
is the snippet of interest.

```bash
local series_top="$(stg top 2> /dev/null)"
local total="$(stg series 2> /dev/null | wc -l)"
local hidden="$(stg series --hidden 2> /dev/null | wc -l)"

if [[ "${total}" -gt 0 ]]; then
    local not_applied="$(stg series | grep -E '^-' | wc -l)"
    local applied="$(($total - $not_applied))"

    if [[ -z "${series_top}" ]]; then
        series_top="·"
    fi

    echo -n "(${status_color}${series_top} ${applied}/${total} ${hidden})"
    echo -n "  ($(current_branch))"
fi
```

## Branchless Workflow

Last year, I was using Stacked Git on top of git branches. More precisely, I
had one branch for each (stack of) Merge Request. It worked well, because my
typical MR counted 3 to 4 commits in average.

Fast forward today, and things have changed on this front too. In a nutshell, I
have become a “one commit per MR” maximalist of sort[^onecommit]. I find this
approach very effective to get more focused reviews, and to reduce the time it
takes for a given MR to be integrated into the main branch.

[^onecommit]: It goes without saying that this approach comes with its set of
    drawbacks too.

    During the past year, I’ve pushed fairly large commits which could have
    been split into several smaller ones, for the sake of keeping my “one
    commit per MR” policy. I have also had to manage large stacks of MRs.

My previous approach based on git branches did not scale well with
this new mindset, and during the course of the year, I stopped using
branches altogether[^branchless].

[^branchless]: I have not invented the branchless workflow, of
    course.

    After it was first published, someone posted a link to my Stacked Git
    article on Hacker News, and [*@arxanas* posted a comment about
    `git-branchless`](https://news.ycombinator.com/item?id=29959224). I tried
    the tool, and even if it never clicked for me, I was really compelled by
    its core ideas.

    Similarly, [Drew DeVault has published a complete article on its own
    branchless workflow in
    2020](https://drewdevault.com/2020/04/06/My-weird-branchless-git-workflow.html).

These days, I proceed as follows.

1. I name each patch after the branch to which I will push it on our
   upstream Git remote.
2. 99% of the time, I push my work using `git push -f upstream @:$(stg
   top)`{.bash}
3. I created a small git plugin I called `git-prepare` which allows
   me to select one of the patch of my current patchset using `fzf`,
   and which pops all other patches that are currently applied.

`git-prepare` is really straightforward:

```bash
#!/bin/sh
patch=$(stg series -P | fzf)

if [[ ! $? -eq 0 ]] ; then
    exit $?
fi

if [ -n "$(stg series -A)" ]; then
    stg pop -a
fi

stg push ${patch}
```

The main hurdle which I still need to figure out is how to deal with
stacked MRs. Currently, this is very manual. I need to remember
which commit belongs to the stack, the order and dependencies of
these commits, and I need to publish each commit individually using
`stg push; git push @:$(stg top)`{.bash}.

The pragmatic answer is definitely to come back to git branches *for
this particular use case*, but it's not the *fun* answer. So from
time to time, I try to experiment with alternative approaches. My current
intuition is that, by adopting a naming convention for my patches, I
could probably implement a thin tooling on top of Stacked Git to
deal with dependents commits.

## Conclusion

Putting aside stacked MRs for now, I am really satisfied with my
workflow. It’s very lightweight and intuitive, and working without
Stacked Git now feels backward and clunky.

So I will take this opportunity to thank one more time Stacked Git’s
authors and contributors. You all are making my professional like
easier with your project.
