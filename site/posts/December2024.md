---
published: 2025-01-01
tags: ['meta', 'opinions']
series:
  parent: series/Retrospectives.html
  prev: posts/May2023.html
abstract: |
    We are done with 2024, and now is a good time to reflect on what has
    happened over the past 12 months. I was not planning to, but my feed
    convinced me to give it a try. Plus, it is a good opportunity to revive my
    “Retrospective” series.
---

# What Happened in 2024?

We are done with 2024, and now is a good time to reflect on what has happened
over the past 12 months. I was not planning to, but [my feed convinced me to
give it a try][origin]. Plus, it is a good opportunity to revive my
“[Retrospective]” series.

[origin]: https://www.paulox.net/2024/12/31/my-2024-in-review/
[Retrospective]: series/Retrospectives.html

## Free and Open Source Software

I’ve been a “prolific contributor” at `$WORK`{.bash}, but less so with my
personal projects.

- [Spatial Shell][spatial] remains my most “popular” project[^stars], but
  except for a very minor 7th release in January, I have not touched it. It’s
  basically a done project, and I very much enjoy using it on a daily basis. My
  main regret is that, contrary to what is stated in its README, Spatial Shell
  does not work _at all_ with i3.
- [`ezjsonm-encoding`][encoding] was initially written for Spatial Shell, but I
  turned it into its own OCaml package in 2024. It is a JSON-only encoding
  library heavily borrowing on [Data-encoding API][Data-encoding], but with a
  more flexible default behavior for object parsing. I enjoyed writing the
  documentation, inspired by a tweet from [Dmitrii Kovanikov][chshersh][^bsky].
  That being said, I have never bothered to benchmark this package properly, so
  if performances are important, it may not be a good fit for you.
- [`jsonrpc2`][jsonrpc2] is, as of January 1st, 2025, an experiment in
  providing a general-purpose framework for servers and clients communicating
  with the [JSON RPC 2.0] protocol. I quite like the API I’m proposing there,
  and maybe I’ll try to polish and publish it in 2025.
- [`bepo-tsrn.nvim`][plugin] is another thing I have done for myself, but
  published as if it was a public good. Now, instead of having to copy/paste
  the same Neovim configuration file on every computer I use, I can just type
  `yay -S neovim-bepo-tsrn-git` and be done with it.
- [celtchar] has seen its first commits since 2021, which is not nothing. As a
  reminder, celtchar is a little tool I have written to generate ebooks and
  static websites for the stories I write; and as I was doing the 2024 edition
  of [NaNoWriMo], I found myself in need to add a missing feature (supporting
  books split in parts, not only chapters).

[^stars]: We should reach 100 stars on GitHub in 2025 😅.
[^bsky]: Yes, cool kids moved to Bluesky in 2024, and Dmitrii is definitely a
    cool kid.

[spatial]: https://github.com/lthms/spatial-shell
[encoding]: https://github.com/lthms/ezjsonm-encoding
[jsonrpc2]: https://github.com/lthms/jsonrpc2
[plugin]: https://github.com/lthms/bepo-tsrn.nvim
[Data-encoding]: https://ocaml.org/p/data-encoding/latest
[chshersh]: https://bsky.app/profile/chshersh.com
[JSON RPC 2.0]: https://www.jsonrpc.org/specification
[celtchar]: https://github.com/lthms/celtchar
[nanowrimo]: https://nanowrimo.org

Overall, I’ve been defaulting to OCaml for the past two years or so, and I am
starting to think it is time to widen my perspective again. I will probably
start with relearning Go[^go].

[^go]: I don’t know why, but I have been mildly obsessed with this language
    lately.

## Blog posts

2024 was not a very productive year when it comes to this website. I have
published 5 articles, which is half the number of publications of 2023. As a
logical consequence, not a lot of folks have visited my website this year.
Funnily enough, the [most read article][cft] (by far) in 2024 was published in
2023[^almost].

[^almost]: To be fair, it was published on December 30, 2023.

#[Yes, 2024 was a quiet year for this website](/img/2024.png)

That being said, I am quite happy with the content published in 2024.

- [Using `git maintenance` with Encrypted SSH Keys][git] is the first article I
  published in 2024. It is a direct consequence of my trip to Brussels in
  February to attend to [FOSDEM]. If you haven’t already, you should watch
  [Scott Chacon’s talk][scott] about Git less known commands; it is the only
  reason why I learned about `git maintenance`.
- [Installing a LUKS-Encrypted Arch Linux on a Vultr VPS][luks] is mostly a
  gift I have made to Future Me. It is a very specific how-to that I can use to
  quickly set up a new server with disk encryption. Funny story, I was planning
  to publish a follow-up about [how I use systemd-nspawn to run my web services
  in containers][nspawn], but no matter how many times I tried, I’ve never
  quite found a good way to tell this story. As I plan to educate myself on
  Kubernetes in 2025, it is not clear I will ever publish it now.
- [Introducing `bepo-tsrn.nvim`][bepo] is probably the less useful article I
  have published in 2024, considering I expect the userbase to `bepo-tsrn.nvim`
  to stick to 1 until the very end[^challenge].
- [On Vestigial Structures][vestigal] hardly qualifies as a blog post, and is
  mostly a joke. It is also the only content on my website that was mostly
  generated by ChatGPT, and it is flagged as such. I don’t like using AI to
  _write_, but I do appreciate having a reviewer always at hand.
- [Serving This Article from RAM for Fun and No Real Benefit][dream] was very
  fun to write. This little experiment was stuck in my head for basically two
  years, and it turned out basically exactly as I had pictured it. That being
  said, I want to learn about CDNs now.

[^challenge]: But who knows? Maybe one of you will prove me wrong!

[git]: GitMaintenanceSshEncryptedKeys.html
[FOSDEM]: https://archive.fosdem.org/2024/
[scott]: https://www.youtube.com/watch?v=aolI_Rz0ZqY&pp=ygUZc28geW91IHRoaW5rIHlvdSBrbm93IGdpdA%3D%3D
[luks]: LUKSEncryptedVPS.html
[bepo]: BepoNvim.html
[vestigal]: VestigialStructures.html
[dream]: DreamWebsite.html
[nspawn]: https://github.com/lthms/nspawn
[cft]: SpatialShell6.html

Overall, I still enjoy having my own little corner of the Internet, but if there is
one thing I’d like to improve in 2025, it is its reach. I’d like you folks to
run into my website, instead of having to promote it every time I write
something. 2025, the year of SEO?

## `$WORK`{.bash}

2024 started with my decision to go back to a Software Engineering position,
after giving an honest try at being an Engineering Manager in late 2023.

I want to remember 2024 for two things.

This year, more than ever, I have tried to appreciate my work beyond my
individual contributions. I am confident in my programming skills (although I
have so much to learn), but being an accomplished engineer is much more than
contributing code. Making sure every engineer in the team can work to the best
of their current ability, fostering a work environment favoring growth and
initiative, estimating as precisely as possible the amount of time needed to
deliver the next important thing, collaborating efficiently with non-technical
teams... I am becoming increasingly interested in these areas.

Besides, this year was all about delivering and deploying in production. It’s
been a [wild ride], and I loved it even if it was very demanding. After having
mostly contributed to R&D projects, the focus on UX, backward compatibility,
etc. was very refreshing. I learned so much through the year, and had many
opportunities to make significant impacts.

In 2025, I want to keep learning about software engineering, and maybe start
sharing my thoughts on the subject on my website.

[wild ride]: https://medium.com/etherlink/post-mortem-etherlink-mainnet-beta-public-endpoint-denial-of-service-cfcaf1a7bb77

## Talks

I gave only one talk in 2024, at a conference called [EthCC]. It was actually a
follow-up to the talk I gave the year before. You can watch me deliver the talk
[here][video], but if you are more into written content, I have also published
a [transcript] on this very website. I actually loved writing it down, and plan
to systematically publish similar content for every recorded talk I will give
in the future.

I also had the opportunity to participate in a [Twitter Space].

This year, my public speaking opportunities were all `$WORK`{.bash}-related. I
would like to change this in the future, because there are enough events out
there for me to start speaking about something other than work[^fosdem].

[^fosdem]: It’s too late to apply to FOSDEM, but maybe I can find something to
    say to an event later in the year! I think.

[EthCC]: https://ethcc.io/
[video]: https://ethcc.io/archives/being-a-stage-2-rollup-from-day-1-etherlinks-journey
[transcript]: BeingStage2Rollup.html
[Twitter Space]: https://x.com/etherlink/status/1852378990712930664

## Sport

This year was a bit of a disappointment, sport-wise. I tried several times to
get back to running regularly, and failed miserably. I went to Lyon for a 10km
run without proper training, and skipped the half-marathon I signed up for. I
should update my [Running Log][running] nonetheless. I started swimming
regularly during the Summer, only to pierce my earlobes in September 😅.

Let’s hope I do better in 2025! I am planning to register for the [Triathlon de
Deauville][triathlon] with my sister. That promises to be fun! And I
want to commit to the [20km de Paris][20km] as well.

On the bright side, I have started to use my bike again. I love riding around
Paris, especially at night.

[triathlon]: https://triathlondeauville.com/
[running]: /running.html
[20km]: https://vredestein.20kmparis.com/

## Final Notes

Overall, I’ve devoted a large part of my time to `$WORK`{.bash} in 2024.
Hopefully, I will find a better balance over the course of 2025, which should
give me more time to explore and experiment more things.

Anyway, happy new year everyone! And happy Dry January!
