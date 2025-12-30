---
published: 2025-07-12
modified: 2025-09-07
abstract: |
    In my TezDev 2025 talk, I explained how we'll scale Etherlink tenfold
    without sacrificing its decentralized principles. This post recaps our
    plan: boosting execution speed while using Tezos' native Data Availability
    Layer to handle massive volume. This is how we'll scale "without
    compromise," keeping Etherlink fast, fair, and non-custodial.
series:
    parent: series/Talks.html
    prev: talks/BeingStage2Rollup.html
---

# Scaling Etherlink Without Compromise

> [!IMPORTANT]
> The content of this article comes directly from a talk I gave at TezDev 2025
> (Catalyst) on July 3, 2025. This is a personal transcript, and any mistakes
> in it are my own.

@[youtube](https://www.youtube.com/embed/2zezFuUBXkQ?si=d1y9aZXErWAjKHuq)

Good morning everyone! Today I’ll be talking about Etherlink—and more
specifically about how we are scaling Etherlink without making any compromise.
And before I dive too deep into the details of this talk, I think it is always
a good idea to start from the beginning. That is, what is Etherlink, really?

## What is Etherlink?

First and foremost, Etherlink is *the* EVM-compatible layer of Tezos. We have
implemented this layer as a Layer 2 blockchain powered by a Tezos smart rollup,
but that’s an implementation detail. What matters is what we wanted to achieve
with Etherlink: bringing EVM-compatibility to the Tezos ecosystem, at a time
where it could make a difference.

Now, we still ended up implementing a Layer 2 blockchain no matter our main
motivation—and one we want to be attractive. But as an EthCC speaker put it
earlier this week, there is a new L2 chain being launched every day, which
means we need to bring new things to the table that our competitors don’t, if
we want to make Etherlink a success.

This is why we have built Etherlink according to three core values, summed up
in a very simple motto: *fast*, *fair*, and (nearly) *free*.

- **Etherlink is fast.** Its sequencer is creating new blocks at a competitive
  pace (every 500ms), providing low-latency to the chain’s users. You only have
  to wait 250ms on average for your transaction to be included, which enables
  exciting opportunities (typically in DeFi).
* **Etherlink is (nearly) free.** As of today, it only costs around a tenth of
  a cent to make a tez transfer on Etherlink. This is necessary for Etherlink
  to be a welcoming platform for a wide range of use cases including some
  requiring the injection of hundreds of thousands of transactions every day.
  Paying 20 cents once is okay, but with high volumes, every cent counts.
* **Etherlink is fair.** In this area, we probably are pioneers actually.
  What we mean by *fair* is that Etherlink treats all its users equally, by
  being a permissionless platform where no arbitrary set of third-party
  entities holds dedicated rights. There is no committee, no chain owner
  capable of doing executive decision. On the contrary, we have entrusted the
  governance of Etherlink to Tezos bakers, making it [the first non-custodial
  rollup][ethcc7]. Anybody can become a baker, which means anybody can engage
  with [Etherlink governance][gov].

[ethcc7]: BeingStage2Rollup.html
[gov]: https://docs.etherlink.com/governance/how-is-etherlink-governed/

## Etherlink in July 2025

We have been building Etherlink for a while now, and it turns out that July is
a pretty busy month for us. In 2023, we announced Etherlink publicly at
[EthCC][ethcc6] and TezDev and launched the [Testnet][explorer]. One year
later, we had [launched our Mainnet][mainnet] and it had been non-custodial
from day 1. It was of significant importance for us that as an Etherlink user,
you didn’t need to trust us in gradually decentralizing a custodial solution.
If you are familiar with the Ethereum rollup space, you already know that this
approach is actually quite singular.

Now it’s July 2025, and we have once again exciting news to share. This is
especially true if you are a Tezos baker, since July will be [a voting
month][votes] for you with two key votes for Etherlink’s future[^seoul]!. One
in particular—and I mention it because it is actually a good transition for the
topic of this talk—is about a new proposal upgrade notably changing how the gas
price is computed to align it better with Etherlink’s real
capacity[^conservative].

[^seoul]: Oh, and we have also announced [Seoul], Tezos’ 19th protocol upgrade
    proposal since then.
[^conservative]: Turns out that we were a bit conservative in Dionysus. When
    testing more thoroughly, we noticed the chain was behaving better under
    load than what we previously thought.

[ethcc6]: EVMCompatibleTezos.html 
[explorer]: https://testnet.explorer.etherlink.com
[mainnet]: https://medium.com/etherlink/etherlink-mainnet-beta-paving-the-way-to-launch-14606e29cc8b
[votes]: medium.com/@etherlink/its-voting-month-for-etherlink-two-governance-votes-coming-in-july-2025-301ae7bcd29f
[Seoul]: https://research-development.nomadic-labs.com/seoul-announcement.html

That being said, I would not say that we are happy with the capacity of
Etherlink today. It’s enough for the current activity of the chain, as hinted
by how stable the gas price is nowadays. But it’s not enough for the kind of
ambitions we are having for Etherlink in particular and Tezos as a whole.

This is why we are committed to increase the capacity of Etherlink in the
short-term (the next six months) at least tenfold.

## Making Etherlink Blazing Fast

Software developers in the room are probably familiar with this expression 🦀.

But when facing such a claim, it’s only natural to ask: how do we achieve that?
In my opinion, there are two aspects to consider.

Firstly, we need to execute transactions faster. For each transaction submitted
to Etherlink, we want to spend as little time as possible executing it. For
this endeavour, we have several plans that will allow us to increase the
throughput of Etherlink.

To give a few examples:

- We are not particularly happy with the EVM implementation we are currently
  using ([SputnikVM]). We are making great progress in transitioning to [REVM].
- We want to introduce parallel execution where it matters. It is a hot topic
  in the industry, with already solid results that we can leverage.
- We have identified for a while now the shortcomings of the current runtime
  our smart rollups are built upon—and we have a team tackling this challenge
  to deliver a new RISC-V-powered runtime that will come with its own storage
  backend designed, implemented and optimised for optimistic rollups.

[SputnikVM]: https://github.com/rust-ethereum/evm
[REVM]: https://github.com/bluealloy/revm

After combining all these efforts together and throwing a few more
optimizations to the mix, we are confident Etherlink will be able to process
transactions significantly faster.

Which brings me to the second side of making Etherlink fast: volume. Processing
the transactions that we already have will make Etherlink more responsive, but
we really want is to increase the overall capacity of Etherlink so that when
you bring more activity to the chain, the system is not congested. To do that,
we need to consider the amount of transactions that you will bring. We already
have hundreds of thousands of transactions sent every day, but what happens
when they become several millions? And several dozens of millions?

As of July 2025, the sequencer publishes Etherlink transactions inside Tezos
Layer 1 blocks, but sadly block space is a scarce resource. To give you a few
numbers, Tezos Layer 1 bandwidth (provided by its block space) is around 500
KBytes every 8 seconds. We can increase the block size, we can reduce the time
between blocks, but the order of magnitude will not change. This becomes a real
concern when we want to scale Etherlink without compromising with its
non-custodial nature.

## Scaling Without Compromise

We need to keep in mind what it means to increase both the speed of your system
and the amount of data that you are processing with it. On the one hand,
processing transactions faster is first and foremost an optimization challenge.
It is a hard one, but ultimately it’s about using the hardware at your disposal
in a more clever way. Processing more transactions on the other hand raises a
**security** challenge, because it requires to *publish* more transactions. If
Tezos Layer 1 blocks are not an option, where should the sequencer publish
those?

One popular alternative to Layer 1 block space for a Layer 2 to publish its
transactions is to rely on a Data Availability Committee (DAC). In this model,
a small group of trusted entities is tasked with ensuring the data is available
to participants.

But would Etherlink have stayed a non-custodial rollup if we had done that? The
answer is a loud and clear “no.” Why? Because optimistic rollups rely on at
least one honest participant that is willing to protect its state. That
participant must have access to the full transaction data. If that data is only
available via a closed committee, we introduce trust assumptions. And the
moment you need to trust a small group for security, you're no longer truly
decentralized.

This is why I am saying processing more transactions raises a security
challenge. We knew that in 2022, when we started building the Data Availability
Layer (DAL) of Tezos..We nicknamed the DAL the [Rollup Booster], because the
goal of the DAL is to increase the available bandwidth for Tezos’ smart
rollups, and it is *now* live on Tezos Layer 1 Mainnet.

[Rollup Booster]: https://research-development.nomadic-labs.com/data-availability-layer-tezos.html

In a nutshell, the DAL is a proof of publication system. Anyone can send
arbitrary data to the DAL’s peer-to-peer network and get back an attestation
that this data has indeed been published. The same way Smart Rollups have been
*enshrined* to the Tezos Layer 1 protocol, the DAL is enshrined to its
consensus. That is, the body of the DAL’s attesters is the same one that is
participating in the consensus of Tezos: the bakers.

Now is actually a good opportunity to celebrate that more than 85% of the
baking power of Tezos is running a DAL node. DAL is already here today for
Etherlink to use in order to increase its capacity. And since Dionysus (the
current version of Etherlink), the sequencer can already decide to publish
transactions to the DAL. It’s not doing it at the moment, because going through
the DAL instead of Tezos Layer 1 blocks has a small impact on the latency of
Etherlink’s bridges—but as soon as we need to, we’ll able to enjoy the
additional bandwidth provided by the DAL[^bandwidth] without any loss in
decentralization.

[^bandwidth]: x10 compared to Tezos Layer 1 blocks today, x200 by the end of
    2025.

## It’s All Coming Together

If you have been following the work of core engineering teams from Nomadic
Labs, Trili Tech and Functori working on Tezos and Etherlink, 2025 is a really
exciting time. Everything we’ve been hard at work delivering our scaling
roadmap for the past four years is now in production. Etherlink is live, bakers
have enabled the DAL, and every piece of this technology stack remain true to
the decentralization ethos of blockchains.

July 2024 to July 2025 was about bootstrapping this EVM-compatible layer of
Tezos we call Etherlink. I want to emphasize how much work that entails.
Launching the chain was actually the easy part. Having the chain being used,
having an ecosystem in place, having the tooling, the partners, the projects
landing: that was the hard part. It’s now done—as much as “being done” in the
rapidly evolving landscape of blockchains means anything.

But we’re not done. We’re still preparing for the future to come. This talk was
about discussing Etherlink’s capacity and how we intend to increase it tenfold.
This will allow to create more room for more users to come, for more projects
to be deployed. In the meantime, I do hope you find in Etherlink a welcoming
platform for your projects!
