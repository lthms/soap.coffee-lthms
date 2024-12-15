---
published: 2023-07-20
series:
    parent: series/Talks.html
    next: talks/BeingStage2Rollup.html
abstract: |
    Tezos smart rollups are a generic framework to write decentralized
    applications as optimistic rollups, ranging from App chain to generalized
    chain. Core infrastructure (L1 interop, open interactive fraud proofs) is
    provided by the Tezos protocol, as I explained during a talk at EthCC[6].
---

# Can Tezos Become EVM Compatible?

> [!IMPORTANT]
> The content of this article comes directly from a [talk] I gave at EthCC[6]
> on July 20, 2023, as part of the “Core Ethereum & Scalling” track. This is
> a personal transcript, and any mistakes in it are my own.

My name is Thomas Letan. I work for a company called [Nomadic
Labs][NL][^company], and today I am here to talk about our work to bring EVM
compatibility to the Tezos ecosystem.

[^company]: Nomadic Labs is one of the largest R&D centers working on the Tezos
    ecosystem.

## What is Tezos?

Tezos is a Layer 1 blockchain that has been around for over five years. One of
Tezos’ key differentiator —at least initially— is its on-chain governance
system. The governance system is a voting procedure to propose, select, and
automatically deploy core upgrades for the blockchain. This governance system
enabled the Tezos network to seamlessly go through 14 upgrades since the
beginning of our Mainnet. These upgrades allowed us to keep innovating at a
strong pace, and today Tezos notably features [its own smart contract language
and runtime][michelson], a 2-block finality consensus algorithm called
[Tenderbake] since April 2022[^hotswap], and a first-class citizen framework to
deploy and operate so-called [Smart Rollups][sr]. 

[^hotswap]: Tezos was initially deployed with a different consensus algorithm,
    which means we have hotswapped Tezos consensus while it was live.

Smart Rollups are optimistic rollups enshrined in their Layer 1 blockchain
(Tezos). We are today at EthCC[6] because we believe they can be a game-changer
for Tezos, and we are excited to share this with you.

The starting point of Smart Rollups was the scaling roadmap of Tezos. It has
been our main focus for the past months, leading us to demonstrate on a public
testnet how 1,000 rollups can process 1,000,000 transactions per second
together. But Smart Rollups as they came to be also enable us to explore brand
new use cases. One of them is EVM compatibility, something Tezos itself does
not provide to our users.

During the remainder of this talk, I will provide you all the keys to get a
grasp on what Smart Rollups are, and how we intend to bring EVM Compatibility
to our ecosystem through one Smart Rollup.

## A Primer on Smart Rollups

The selling pitch for Smart Rollups is to present them as new ways to implement
decentralized applications. They offer a trade-off that is slightly different
than smart contracts already propose. In a nutshell, Smart Rollups get more
computational power compared to a smart contract, but since these computations
are offloaded from the Layer 1 blockchain, you need to bring your own
infrastructure to carry it.

### Optimistic Rollups Done Once

Under the hood, Smart Rollups are an optimistic rollup framework with three
critical properties.

- They are **permissionless** by default, meaning that any Tez holder[^xtz] can
  create a rollup, and compute, publish and defend the state of any rollup
  created on Tezos. That is, we have permissionless interactive fraud proofs
  already!
- They are **enshrined**. A Smart Rollup on Tezos does not rely on a collection
  of smart contracts, but is instead of first-class citizen of the Tezos
  protocol itself with a dedicated address. Optimistic rollup maintenance
  operations are dedicated operations of Tezos, optimized for performances and
  gas efficiency. Besides, they benefit from Tezos being able to evolve and
  improve over upgrades[^nairobi].
- They are **programmable**. The same way you create a smart contract by
  providing a script, Smart Rollup are provisioned with a so-called *kernel* (a
  WASM program) when they are created, and this program will dictate the
  semantics of the rollup. This is the key property that makes Smart Rollups a
  solid contendent for addressing a wild range of use cases, from generalized
  Layer 2 blockchains to specialized AppChains.

[^xtz]: Tez is the native token of Tezos.
[^nairobi]: It’s more than a promise already. Smart Rollups have been enabled
    on Tezos Mainnet on March 2023 with the Mumbai upgrade. Since then, Nairobi
    has been activated and has improved the developer experience for every Smart Rollup
    developers.

### The Smart Rollup Runtime

But what is exactly a Smart Rollup, from a developer perspective? The best way
to answer this question is to provide a high-level description of the runtime
used to execute its kernel.

The first component a kernel can interact with is the shared inbox. The shared
inbox contains messages coming from the Layer 1 blockchain[^shared]. These
messages can be sent by wallet-owned accounts or smart contracts alike, but they
they must compete for Layer 1 block space to do so. This is fine until it
is not —in case of significant adoption for instance— so we equipped Smart
Rollups with an additional way to import data from the outside world: the
so-called reveal channel. At its core, the reveal channel is a primitive which
allows a kernel to retrieve an arbitrary data, provided it knows the data’s
hash. Although a smart rollup cannot guess a hash out of thin air, the
competition for block space becomes a lot less fierce when the competitors only
need 32 bytes per block each.

[^shared]: I want to insist on that: the inbox is _shared_ in the sense that
    all the smart rollups deployed on the Layer 1 blockchain have access to all
    messages sent at a given time.

Similar to smart contracts’ storage, a kernel can read from and write to a
“durable storage.” The key difference between the two is how a kernel does not
pay for bytes allocated in the durable storage. The rationale is the same as
for execution time: since everything happens offchain, the cost for allocating
more Layer 2 state is higher requirement for the hardware infrastructure.

A kernel can send back messages to wallet-owned address and smart
contracts of the Layer 1 blockchain through the outbox. Smart Rollups being
optimistic rollups, the usual limitations apply for this communication channel.
Messages of the outbox can only be triggered on the Layer 1 blockchain once the
Layer 2 state advertising them has been published **and** cannot be contested
with an interactive fraud proof anymore. For Smart Rollups, this means waiting
for two weeks as of today.

Finally, Smart Rollups get free execution time for every block created by the
Layer 1 blockchain. This is a very different model than gas-bounded computation
of smart contracts, and enables new use cases. For instance, you can imagine
having a kernel reorganizing its storage across several Tezos blocks in a
transparent manner, without the need to inject any message to the shared inbox.

### Smart Rollup’s Adopter Starter Kit

Implementing a kernel is only the beginning of the journey. You still need to
_execute_ it, which is more involved than deploying a smart contract.

If you work on Layer 2 solutions yourself, you may know that optimistic rollups
can be tricky to operate, and it would not be reasonable for every Smart
Rollups adopter to have to reimplement from scratch their own daemon. From this
perspective, our pledge has always been to make that as easy as possible, and
to that end, we have invested significant efforts to provide a software suite
that lets you focus on your business logic. In particular, we provide

- A high-level, type safe Rust framework to implement your kernel. This makes a
  very interesting alternative of the low-level, C-like API exposed by the
  Smart Rollup (because that is how WASM works). 
- A debugger to test, inspect, profile and benchmark the execution of your
  kernel.
- A general-purpose daemon responsible to track the state of your rollup,
  publish it on the Layer 1 blockchain, and defend it if need be.

## A Generalized, EVM-Compatible Layer 2 Blockchain for Tezos

The main reason why we have been eager to comme to EthCC this year is because
we are about to bring EVM compatibility to the Tezos ecosystem, thanks in large
part to Smart Rollups.

### Building an EVM-compatible Blockchain

When we started working on this a few months ago, we have quickly realized that
“building an EVM-compatible rollup” does not mean much... or rather, it can be
interpreted as many different things. When you build a rollup, you are
confronted to a lot of design decisions. The first of such decisions that comes
to mind is your requirements in terms of latency: do you need a sub-second
block time, or are you fine with sticking to your Layer 1 blockchain latency?
The answer to this question has a direct impact on the decentralization of your
rollup. As of now, the de facto solution to sub-second latency is the
delegation of block production to a single entity (the sequencer). Another
interesting question is about data-availibility. Are you fine with being
limited by the block space of your Layer 1 blockchain, or do you know your
requirements will far exceed them? And what about gas price in your Layer 2
blockchain? Smart Rollups do not have a notion of gas, but if you are building
a generalized rollup emulating a full blockchain, you will need gas and a gas
price to constraint what your users can do according to your infrastructure
capacity. On the other hand, if you are building an AppChain with only a
handful of Solidity contract whose execution can only be triggered by yourself,
you probably don’t need that.

What was clear to us is that we did not want to take too many decisions like
these too soon in the development process, but rather built a versatile
solution which can be adapted to end-users need. As a consequence, what we are
working on today is a twofold project[^layered], with:

[^layered]: We are providing a _layered_ answer to a complicated question.

1. A customizable “template” for generalized rollup, compatible with the
   Ethereum ecosystem at large.
2. A community instance of this template, focusing on _decentralization_ and
   _cost-efficiency_.

The key idea of this approach is to leave the door open to potential adopters
whose requirements are not addressed by the community instance we are working
on. It should be straightforward to deploy a dedicated instance that is tailored
to their needs.

To achieve this, we have drawn inspiration from the block proposer/block
validator paradigm. Our rollup program is divided into two “stages.” The stage
1 interprets messages coming from the shared inbox to reconstruct block
proposals. Then, the stage 2 validates these block proposals, and publishes the
Layer 2 history. From this perspective, most of the work required to support a
sequencer setup is focused on the stage 1, while manipulating gas fees is done
by modifying the stage 2 for instance.

### Ensuring Compatibility with the Ethereum Ecosystem

This architecture has proven itself to implement the semantics of an
EVM-compatible Layer 2 blockchain, but this was only the beginning of the
journey. For this new chain to be usable, we also need to be compatible with
the galaxy of tools and solutions that is the Ethereum ecosystem. This is
achieved by implementing the [JSON RPC API]. To be clear, this was unknown
territory for us at the beginning of this project. The nodes participating in
the Tezos network uses a different approach[^rest]. As a consequence, we are
developing a new node to fill this gap, and we are now capable of serving the
API to tools like Blockscout and MetaMask, or dApps from partners. To give you
a concrete example, [we had an improvised workshop with Arianee today][arianee]
to deploy their application on our brand new Testnet[^testnet]. As far as I
know, it worked! And [maybe your dApp is next][nl-blog]?

[^testnet]: It was deployed the day before the talk, and it is still used
    [today].
[^rest]: We have settled on a REST API.

I mention we are building a community rollup, and I am happy to unveil today
that its name will be [Etherlink].

## What’s coming next?

Our journey to scale the Tezos ecosystem and open it to new use cases and
opportunities is far from over. In the meantime, if there are two things
that you should remember from this talk, it is that:

1. EVM-compatibility is coming to Tezos this year, starting with
   Etherlink[^beta].
2. You can already test to deploy your dApp on our brand new Testnet.

[^beta]: This promise was a tad optimist. The Mainnet Beta of Etherlink was
    eventually launched on May 15, 2024.

Thank you very much, and see you on Tezos!



[talk]: https://www.youtube.com/watch?v=0eRhAyE_B_8
[NL]: https://www.nomadic-labs.com/
[michelson]: https://www.youtube.com/watch?v=0eRhAyE_B_8
[Tenderbake]: https://tezos.gitlab.io/alpha/consensus.html
[sr]: https://docs.tezos.com/architecture/smart-rollups
[JSON RPC API]: https://ethereum.org/en/developers/docs/apis/json-rpc/
[arianee]: https://x.com/ArianeeProject/status/1681644775005364225
[today]: https://testnet.explorer.etherlink.com/
[nl-blog]: https://research-development.nomadic-labs.com/evm-tezos-testnet.html
[etherlink]: https://www.etherlink.com
