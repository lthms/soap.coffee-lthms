---
published: 2024-07-11
abstract: |
    Compared to Layer 1 blockchains which embraced decentralization from day
    1, Layer 2 solutions have preferred to rely on “training wheels.” But what
    happens when we decide otherwise? That's Etherlink's journey towards
    Mainnet, and I had an opportunity to discuss this at EthCC[7].
series:
    parent: series/Talks.html
    prev: talks/EVMCompatibleTezos.html
---

# Being a Stage 2 Rollup from Day 1: Etherlink’s Journey

> [!IMPORTANT]
> The content of this article comes directly from a [talk] I gave at EthCC[7]
> on July 11, 2024, as part of the “Rollups & Scaling Solutions” track. This is
> a personal transcript, and any mistakes in it are my own.

My name is Thomas Letan. I’m working for a company called [Nomadic
Labs][NL][^company], and today I am here to talk about [Etherlink]. More
specifically, I will talk about our journey to be a stage 2 rollup from day 1.

[^company]: Nomadic Labs is one of the largest R&D centers working on the Tezos
    ecosystem.

## What is Etherlink?

Before going any further, it is probably worth giving a bit of an introduction
for Etherlink, because you might not already be aware of what it is already.
Etherlink is a newcomer in the Layer 2 landscape, and has the particularity of
being part of the [Tezos] ecosystem. That is, it is not an Ethereum rollup. Our
Mainnet has been available in Beta since May 15.

Etherlink has been built with three core properties in mind: we wanted it to be
_fast_ (with a 500ms soft confirmation time delivered by a sequencer), _fair_
(as we will discuss during this talk), and nearly _free_ (your typical
transaction costing one-tenth of a cent).

Our main focus during Etherlink’s beta is onboarding new partners. We have
already onboarded several infrastructure partners, and our immediate focus now
is on bringing dApps to the chain.

### Etherlink is (nearly) a Stage 2 Rollup

Besides, what we think is interesting about Etherlink is that it is already
(nearly) what [L2beat] calls a [stage 2 rollup][stage2], and it has been since
its genesis block.

To support this claim, let's go back to the definition of what L2beat stages
are, and what a stage 2 rollup is about.

- Etherlink naturally fully qualifies as a stage 0 rollup. Every transaction is
  posted on Layer 1 (Tezos in this case), along with L2 state root hashes.
  Besides, you can recompute the state of the chain locally using free and open
  source software (released as part of the [Octez] suite).
- Etherlink fully qualifies as a stage 1 _optimistic_ rollup as well. We have
  the full implementation of the optimistic rollup infrastructure, including a
  trustless bridge and a fraud-proof system.
- Because this fraud proof system is permissionless (and has actually been
  permissionless since the genesis of Etherlink), we also meet a crucial
  requirement of stage 2 rollups. We are missing a 30-day exit window for users
  wanting to leave their funds out of Etherlink to fully qualify as a stage 2
  rollup. This is because we favor a shorter feedback loop with our early
  adopters during the course of our beta[^exit].

[^exit]: While the exit window is currently 24 hours, it is already fully
    permissionless. Users do not need the help or authorization of a
    third-party to remove funds from Etherlink.

### Etherlink is a Non-Custodial Rollup

Meeting the main requirements of being a stage 2 rollup has been a direct
consequence of our primary objective for Etherlink: to be a non-custodial
rollup. That is, it was always clear to us that no closed set of third-parties
should ever be granted exclusive, irrevocable rights on Etherlink. In other
words, we wanted Etherlink to adhere to the same standards as Layer 1
blockchains, like Ethereum or Tezos.

To that end, we built Etherlink on top of two cornerstones: a permissionless
fraud proof system, and a decentralized on-chain governance. My goal for the
remainder of this talk is to give you a peek into the kind of solutions we came
up in these two areas.

## Etherlink is Powered by a Permissionless Optimistic Rollup

I was at EthCC last year to [introduce Tezos optimistic rollup stack][EthCC6].
We won’t revisit the details of our solution in depth, but let’s use this
opportunity to give you a refresher.

### Optimistic Rollup in a Nutshell

We are in the rollup track, so we can skip the 101 course on optimistic rollup.
To me, the three points you need to keep in mind from now on is that an
optimistic rollup 

1. offloads computations away from a layer 1 blockchain in a new layer
2. enables bi-directional communications between the two layers with a
   _trustless_ bridge
3. relies on an interactive fraud proof system to ensure the safety of your
   assets while they are locked in this second layer.

You cannot remove one of these properties without making an optimistic rollup
either unsafe or useless.


### Smart Rollups are Optimistic Rollups as a Common Good

Etherlink is powered by Smart Rollups, a one-year-old feature of the Tezos
protocol. You can think of Smart Rollups as a general-purpose framework for
building optimistic rollups. I like to think that we have implemented the full
optimistic rollup infrastructure once (and —to the best of our knowledge—
correctly), and now every member of the Tezos community can benefit from this
effort.

This is not the first time I’m tasked to give an introduction to Smart Rollups,
and I like to put forward the following properties:

- You have understood it by now, but Smart Rollups are permissionless by
  default. By default, any XTZ holders[^xtz] can post and defend L2 state root
  hashes[^permissioned].
- Smart Rollups are not implemented by means of smart contracts. They are
  directly enshrined in Tezos protocol, making them a first-class citizen of
  the Layer 1 blockchain. This was instrumental in enabling several
  optimizations to increase performances and reduce end-users costs.
- They are fully programmable. Smart Rollups are not about creating
  EVM-compatible Layer 2 blockchains, they are way more general than that.
  The same way you provide a script when creating a smart contract, Smart
  Rollups come with a (WASM) program that decides the semantics ruling the
  newly created Layer 2 rollup.

Etherlink is not the only use-case for Smart Rollups! To name a few examples,

- We have been able to demonstrate Tezos can support [one million transactions
  per second on a public testnet using 1,000 smart rollups][1mtps] last year. 
- We are working on a Javascript runtime (called [jstz]) for Layer 2
  blockchains powered by a Smart Rollup.
- Engineers from [Plenty], a DeFi platform deployed on Tezos, have been
  experimenting with [Plenty Rollup][prollup] to exchange assets with
  low-latency and high-throughput.

[^xtz]: XTZ is the native token of Tezos, that is used to pay gas, validator
    fees, and participate in Tezos governance (more on that later).
[^permissioned]: It is also possible to create permissioned Smart Rollups, for
    use cases that require it. This is not the case of Etherlink, obviously.

## Etherlink Decentralized Governance

Smart Rollups are the technological foundation of Etherlink, but they are not enough to
make it a non-custodial rollup. The same way you can create a centralized smart
contract on top of a decentralized blockchain, you can definitely build a
custodial Smart Rollup by embedding a public key in its code.

This brings us to decentralized governance.

If you were aware of Tezos before this talk, it is probably because of its
on-chain governance system. If you don’t know, Tezos is a Layer 1 blockchain
officially launched in 2018, with a track record of 16 forkless upgrades. This
is possible because the governance of Tezos is embedded in its protocol. We
definitely wanted to leverage this when we started building Etherlink.

### Etherlink (Absence of) Governance Token

It was clear from the get-go that Etherlink would “inherit” from Tezos strong
and vivid governance. One consequence of this choice was to XTZ as its
governance token, instead of introducing a new token. Besides, Tezos governance
is larger than XTZ itself, because it is built on top of a pioneer liquid proof
of stake mechanism. For Tezos upgrades, only the validators vote, but their
ballot’s weight is determined not only by their personal stake but also (and
sometimes mostly) by the balances of individual holders who have “delegated”
their XTZ to them[^delegation].

This should give Etherlink a head start, because the ecosystem of Tezos has a
clear and well-established maturity when it comes to on-chain governance.

[^delegation]: It is clearly out of the scope of this talk, but for your
    information, Tezos liquid proof of stake has been significantly amended
    with the Paris upgrade to include a new [staking mechanism][staking] which
    complements the existing delegation approach.

### Handing over Etherlink to Tezos Validators

Similarly to Tezos, Etherlink governance happens on-chain, and once the vote
is finished, there is nothing we can do to prevent its consequences from
becoming a reality. Everything is embedded in Etherlink program.

The voting process is a lightweight revisit of Tezos’ one. The governance of
Etherlink is carried through the Layer 1 blockchain, because this is the place
where the voting power of the governance body (Tezos validators) is determined.

The vote proceeds as follows.

Firstly, _any_ Tezos validator can propose a new upgrade during the **proposal
period**. I believe this is a significant rule to highlight. Proposing a
candidate is not a right limited to —let’s say— Etherlink core developers. On
that, we follow the footsteps of Tezos, and what happens on Tezos during the
proposal period is often quite interesting. We have seen time and time again
the community using this opportunity to engage very actively with the
governance process. For the Ithaca proposal for instance, a validator had
submitted a counter-proposal disabling a feature they didn’t like. For the
Oxford proposal, validators proposed a variant of the proposal tweaking some
parameters of the key feature introduced at the time. This is “governance at
work,” and the governance body can then select the proposal they find the best
fit for the Tezos network.

Secondly, the **promotion period** starts with the proposal that has received
the most upvotes. Obviously, winning an election among many participants does
not ensure to the victor a majority of support[^consensus]. The question asked
to validators boils down to: “Do you approve this proposal?” The goal is to
verify that the selected candidate can gather a supermajority of support. This
additional step was designed to alleviate the risk to see unhappy validators
fork Tezos.

Finally, the **cooldown period** gives an opportunity to (1) the ecosystem to
adapt to the features and changes brought by the new software, and to (2)
dissatisfied users to exit Etherlink.

[^consensus]: For context, I gave this talk in the midst of France almost
    seeing a far-right government taking power, and the left “winning” a snap
    election with too few parliament members to apply their program.

The current parameters for the governance of Etherlink are as follows.

|                    | Regular upgrade | Security upgrade | Sequencer     |
| ------------------ | --------------- | ---------------- | ------------- |
| Voting period      | ~ 2.5 days      | ~ 7 hours        | ~ 5 days      |
| Cooldown period    | ~ 24 hours      | ~ 24 hours       | 24 hours      |
| Quorum (proposal)  | 1%              | 5%               | 1%            |
| Quorum (promotion) | 5%              | 15%              | 8%            |
| Supermajority      | 75%             | 80%              | 75%           |

I will not spend much time discussing each number individually, and instead
focus on the three kind of votes.

Firstly, and this is probably what you had in mind when I started to mention
decentralized governance, is voting on the next version of the software
powering the chain. We distinguish between “regular” upgrades (the default
case), and “security” upgrade. The latter can be used exceptionally if a bug is
found in Etherlink that can endanger the assets of Etherlink users. The
security upgrade has shorter periods of vote, but requires a higher
quorum[^security]. It is worth mentioning that we do not have a security
committee, as it is often the case for other Layer 2 blockchains.

Secondly, and I think it is a unique thing in our industry, Etherlink’s
sequencer is elected by Tezos validators. This brings a clear incentivization
for the sequencer to behave correctly. Otherwise, Tezos validators can simply
vote them out of Etherlink. It does without saying —so it’s better when
reaffirmed— that the sequencer power is limited to proposing blocks, the
validation of said blocks remains permissionless. In particular, in the context
of Etherlink being a Smart Rollup, only valid transactions that are actually
posted on Tezos can lead to funds transiting from Etherlink to Tezos through
the permissionless bridge.

[^security]: Did you know? [Etherlink has gone through a security upgrade
    already][securityupgrade]. The patch deployed fixed a critical issue in the
    withdrawal precompiled contract, which was found by [Spearbit] during their
    audit.

Another interesting fact about Etherlink and its relationship with the
sequencer is how Tezos consensus algorithm and low block time enables
Etherlink’s blocks to become final under less than a minute. Tenderbake (a
variant of Tendermint) features a 2-block finality property that is
incredibly rollup-friendly. Since the sequencer typically posts its block
proposals directly after their creation, it is not unusual for an Etherlink
block to become final in 30 seconds or so.

For partners and institutional entities that cannot rely on soft confirmation
from a sequencer, we believe this can be a game changer.

## Why Non-Custodial?

This talk is slowly coming to its end, and one way to conclude it is to come
back to this idea that we wanted Etherlink to be non-custodial from the get-go.
This should raise an interesting question: why? Why was it so important for us
to make it a priority that early in the development process?

This is particularly relevant when we take a step back and have a look at our
ecosystem. To this day, the leaders of our industry are still powered by stage
1 (Arbitrum, Optimism) and stage 0 (Base) rollups.

The origin of our decision lies in our long term goal for Etherlink. Etherlink
as a Layer 2 blockchain is important, and we have invested a significant amount
of effort and time to make it as successful as we can, *and* it is also a
component of a larger scalability roadmap we coined [Tezos X][tezosx]. Tezos X
aims to bring the full Tezos ecosystem into a scalable, decentralized
optimistic rollup compatible not only with Michelson (the home-grown smart
contract language of Tezos) and EVM, but mainstream programming languages as
well (as suggested by our efforts on jstz).

In the meantime, I can only encourage you to take interest in Etherlink today.
As mentioned, its Mainnet is already there and will soon move out of the beta
phase. Our fast, fair and (nearly) free Layer 2 blockchain awaits you.

[talk]: https://ethcc.io/archive/Being-a-Stage-2-rollup-from-day-1-Etherlinks-journey
[NL]: https://www.nomadic-labs.com/
[Etherlink]: https://www.etherlink.com
[Tezos]: https://tezos.com
[L2beat]: https://l2beat.com/scaling/summary
[stage2]: https://medium.com/l2beat/introducing-stages-a-framework-to-evaluate-rollups-maturity-d290bb22befe
[Octez]: https://tezos.gitlab.io
[EthCC6]: https://www.youtube.com/watch?v=0eRhAyE_B_8
[1mtps]: https://www.youtube.com/watch?v=2EgjMvEIGww
[jstz]: https://spotlight.tezos.com/jstz/
[Plenty]: https://www.plentydefi.com/
[prollup]: https://rollup.plenty.network/
[staking]: https://tezos.gitlab.io/active/adaptive_issuance.html#new-staking-mechanism
[securityupgrade]: https://medium.com/etherlink/post-mortem-how-and-why-etherlinks-first-security-upgrade-on-mainnet-beta-happened-600ef64622ab
[Spearbit]: https://spearbit.com/
[tezosx]: https://spotlight.tezos.com/tezos-x/
