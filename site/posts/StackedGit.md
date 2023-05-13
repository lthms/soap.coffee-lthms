---
published: 2022-01-16
modified: 2022-08-07
tags: ['stacked-git', 'workflow']
abstract: |
    I’ve been using Stacked Git at work since early 2021, and as of January
    2022, it has become a cornerstone of my daily workflow.
---

# How I Use Stacked Git at `$WORK`{.bash}

According to [my Lobste.rs history](https://lobste.rs/s/s6quvg/stacked_git), I
have run into [Stacked Git](https://stacked-git.github.io) in early April
2021, and I remember that its promises hit a soft spot. A few weeks later, I was
submitting [a *pull request* to teach Stacked Git to sign
commits](https://github.com/stacked-git/stgit/pull/100). It was all I needed to
start using it at `$WORK`{.bash}, and now it has become a cornerstone of my
development workflow.

## What is Stacked Git?

Before going any further, it is probably a good idea to take a moment and
present Stacked Git. The website introduces the tool as follows:

> Stacked Git, *StGit* for short, is an application for managing Git
> commits as a stack of patches.

There are a few things to unpack here. First and as its name suggests, Stacked
Git is a tool built on top of Git[^pijul]. It is *not* a brand new VCS, and as
a consequence you keep using all your existing tools and plugins[^magit].
Secondly, Stacked Git helps you curate your Git history, by turning your
commits into patches, and your branches into stacks of patches. This speaks to
me, maybe because I have been fascinated by email-based workflows for quite
some time.

[^pijul]: My main takeaway from my Pijul adventure is connected to this. Git
    is not limited to the `git` binary. Git comes with a collection of powerful
    forges, nice editor plugins, and years of good practices.

    To this day, it’s neither the bugs nor the breaking changes that made me
    quite Pijul. Those were expected. What I naively did not anticipate is the
    dry feeling that Pijul was just the `pijul` binary, which left me with a
    lot of tasks to do manually.

[^magit]: I am looking at you, Magit.

To me, the two core features of Stacked Git are (1) allowing you to
name your commits, and (2) to navigate among them.
Together, they create a wonderful companion to help you keep your
history clean.

## My Subset of Stacked Git

I do not want this article to be a Stacked Git tutorial.
Fortunately, I don’t really use the tool at its full potential.
I only care about a relatively small subset of commands I feel
comfortable with and use daily.

First, to decide which commits are part of my “stack of patches,” I
can count of these commands:

- `stg new NAME` creates an empty commit, and gives it the name
  `NAME`.
  Having a way to identify a patch with a meaningful name that is
  resistant to rebase and amend is very nice.
  These are two properties commit hashes do not have.
- `stg uncommit NAME` names the most recent commit under my
  stack with `NAME` and integrates it into it. I do this when I am
  tasked to work on a merge request made by a colleague, for
  instance.
- `stg commit` removes from my stack its last patch. I do this when
  said commit has been merged into `master`.

Once my stack of patches is ready, the fun begins.

At a given time, a patch can either be (1) applied, (2) unapplied, or (3)
hidden. On the one hand, if a patch is applied it is part of the Git history.
On the other hand, unapplying a patch means removing it from the working branch
(but not from the stack of patches of Stacked Git). If a patch becomes
irrelevant, but you don’t want to remove it entirely because it can become
handy later, you can hide it. A hidden patch sits beside the stack of patches,
and can be reintegrated if need be.

Analogous to `git log` ---which allows you to visualize your Git history---,
`stg series` gives you a view of the state of your stack of patches. Patches
prefixed with `+` (or `>`) are applied, while `-` means the patch is unapplied.

Then,

- `stg pop` unapplies the patch on top of the list of applied
  patches.
- `stg push` applies the patch on the bottom of the list of unapplied
  patches.
- `stg goto NAME` unapplies or applies the necessary patches so that
  `NAME` becomes the top patch of the list of applied patches.

Both `HEAD` and the work tree are updated accordingly.

In addition, `stg sink` and `stg float` allow reorganizing your
stack of patches, moving patches around.
Basically, they are like `git rebase -i`, but without having to use
`$EDITOR`.

Modifying patches is done with `stg refresh`.
It’s akin to `git commit --amend`, except it is more powerful because
you can modify any applied patches with the `-p` option.
I’d always encourage you to `stg goto` first, because `stg refresh
-p` remains unfortunately error-prone (nothing prevents you from targeting
the wrong patch).
But when used carefully, it can be very handy.

Finally, `stg rebase REF` moves your stack of patches on top of `REF`[^rebase].
It is akin to `git rebase --onto`, but more straightforward. What happens is
Stacked Git pop all the patches of my stack, reset the `HEAD` of the current
branch to `REF`, and tries applying the patches one by one In case of
conflicts, the process stop, and I am left with an empty patch, and a dirty
work tree with conflicts to solve. The hidden gem is that, contrary to `git
rebase`, the repository is not “in the middle of a rebase.”

Suppose there are many conflicting patches still waiting in my stack of patches,
and an urgent task I need to take care of first. I can just leave them here. I
can switch to another branch, and when I come back, I get my patches back. I
call this feature “incremental rebases.”

[^rebase]: Stacked Git is supposedly able to detect, during a rebase, which of
    your patches have been applied to your target branch. I’d rather use `stg
    uncommit`{.bash} before doing the rebase, though.

And that is basically it. In a nutshell, Stacked Git equips commits with the
same features as branches.

## My Stacked Git Workflow

As mentioned in the introduction of this article, Stacked Git has become a
cornerstone of my workflow. I’ve been asked a few times what this workflow is,
and why Magit is not enough[^magit2]. So let’s try to do that. But first, a
warning. Yes, because Stacked Git is only a wrapper above Git, everything I
will explain can be achieved using Git alone, especially if you are a Magit
wizard.

[^magit2]: It’s always about Magit. ;)

Stacked Git makes just everything so more convenient to me.

### Planning My Commits Ahead Of Time

I’ve been introduced to Git with a pretty simple workflow: I am
supposed to start working on a feature, and once it’s ready, I
can commit, and move on to the next task on my to-do list.

To me, this approach is backward.
It makes you set your intent after the fact.
With Stacked Git, I often try to plan my final history /before
writing the very first line of code/.
Using `stack new`, I create my patches, and take the time to write
their description.
It helps me visualize where I want to go.
Then, I use `stack goto` to go back to the beginning of my stack,
and start working.

It is not, and cannot be, an exact science. I often have to refine
them as my work progresses.
Yet, I think my Git history is cleaner, more focused, since I have
started this exercise.

### Getting My Fixup Commits Right

Reviews are a fundamental aspect of a software developer job.
At `$WORK`, we use Gitlab and their merge requests workflow,
which I find very annoying, because it does not provide meaningful
ways to compare two versions of your submission[^gitlab].

[^gitlab]: There is a notion of “versions” in Gitlab, but its ergonomics fall
    short of my expectations for such a tool.

What we end up doing is creating “fixup commits,” and we push them
to Gitlab so that reviewers can easily verify that their feedback
has correctly been taken into account.

A fixup commit is a commit that will eventually be squashed into
another.
You can understand it as a delayed `git commit --amend`.
Git has some built-in features to manipulate them.
You create them with `git commit --fixup=<HASH>`, and they are
interpreted in a specific manner by `git rebase -i`.
But they have always felt to me like a sordid hack.
It is way too easy to create a fixup commit that targets the wrong
commit, and you can end up with strange conflicts when you finally
squash them.
That being said, if used carefully, they are a powerful tool to
keep a Git history clean.

I am not sure we are using them carefully, though.

Some reviews can be excruciating, with dozens of comments to
address, and theoretically as many fixup commits to create.
Then you push all of them on Gitlab, and days later, after the
green light from the reviewer, you get to call `git rebase`
and discover your history is broken, you have tones of conflicts
to fix, and you’re good for a long afternoon of untangling.

The main reason behind this mess is that you end up fixing a commit
from the `HEAD` of your working branch, not the commit itself.
But with Stacked Git, things are different.
With `stg goto`, I put my working tree in the best state possible
to fix a commit: the commit itself.
I can use `stg new` to create a fixup commit, with a meaningful
name.
Then, I am forced to deal with the potential conflicts it brings
when I call `stg push`.

Once my reviewer is happy with my work, I can call `stg squash`.
It is less automated than `git rebase -i`, but the comfort I gained
during the development is worth this little annoyance.

### Managing Stacked Merge Requests

At `$WORK`, we are trying to change how we deliver new features to
our `master` branch.
More precisely, we want to merge smaller contributions more
frequently.
We have had our fair share of large and complex merge requests that
were a nightmare to review in the past, and it’s really not a fun
position to be put in.

For a few months, I have been involved in a project wherein we
decided /not/ to fall in the same trap again.
We agreed on a “planning of merge requests” and started working.
The first merge request was soon opened.
We’ve nominated an “owner” to take care of the review, and the rest
of the team carried on.
Before the first merge request was merged, the second one was
declared ready, and another owner was appointed.
Then, the owner of the first merge request had a baby, and yours
truly ended up having to manage two interdependent merge requests.

It turns out Stacked Git is a wonderful tool to help me keep this
under control.

I only have one branch, and I use the same workflow to deal with
feedback, even if they are coming from more than one merge
request.
To remember the structure of everything, I just prefix the name of
my patches with a merge request nickname.
So my stack will look something like this:

```
+ mr1-base
+ mr1-tests
+ mr1-doc
> mr2-command
- mr2-tests
```

A reviewer leaves a hard-truth comment that requires a significant rework of
the oldest merge request? `stg goto` reverts my work tree in the appropriate
state, and `stg push` allows me to deal with conflicts one patch at a time. If
I need to spend more time on the oldest merge request at some point, I can
continue my work, knowing the patches related to the newest one are awaiting in
my stack.

The most annoying part is when the time comes to push everything. I need to
`stg goto` at the last patch of each merge request, and `git push
HEAD:the-branch`. It’s not horrible. But I will probably try to automate it at
some point.

## Conclusion

Overall, I am really thankful to Stacked Git’s authors! Thank you! You are
making my interactions with Git fun and carefree. You provide me some of the
convenience of patch-based VCS like [Darcs](http://darcs.net) and
[Pijul](https://pijul.org), but without sacrificing the power of Git.

I encourage anyone to at least give it a try, and I really hope I
will be able to contribute back to Stacked Git in the near future.
