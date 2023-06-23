---
published: 2019-01-15
tags: ['research']
feature: yes
abstract: |
    It has been a long journey —4 years, 10 days— but I have completed my PhD
    on October 25, 2018.

---

# I am no longer a PhD. student

It has been a long journey —4 years, 10 days— but I have completed my PhD on
October 25, 2018. The exact title of my PhD thesis is “[*Specifying and
Verifying Hardware-based Security Enforcement
Mechanisms*](https://inria.hal.science/tel-01989940v2/file/2018_LETAN_archivage.pdf)”.

## Abstract

In this thesis, we consider a class of security enforcement mechanisms we
called *Hardware-based Security Enforcement* (HSE). In such mechanisms, some
trusted software components rely on the underlying hardware architecture to
constrain the execution of untrusted software components with respect to
targeted security policies. For instance, an operating system which configures
page tables to isolate userland applications implements a HSE mechanism.

For a HSE mechanism to correctly enforce a targeted security policy, it
requires both hardware and trusted software components to play their parts.
During the past decades, several vulnerability disclosures have defeated HSE
mechanisms. We focus on the vulnerabilities that are the result of errors at
the specification level, rather than implementation errors. In some critical
vulnerabilities, the attacker makes a legitimate use of one hardware component
to circumvent the HSE mechanism provided by another one. For instance, cache
poisoning attacks leverage inconsistencies between cache and DRAM’s access
control mechanisms. We call this class of attacks, where an attacker leverages
inconsistencies in hardware specifications, *compositional attacks*.

Our goal is to explore approaches to specify and verify HSE mechanisms using
formal methods that would benefit both hardware designers and software
developers. Firstly, a formal specification of HSE mechanisms can be leveraged
as a foundation for a systematic approach to verify hardware specifications, in
the hope of uncovering potential compositional attacks ahead of time. Secondly,
it provides unambiguous specifications to software developers, in the form of a
list of requirements.

Our contribution is two-fold:

1. We propose a theory of HSE mechanisms against hardware architecture models.
   This theory can be used to specify and verify such mechanisms. To evaluate
   our approach, we propose a minimal model for a single core x86-based
   computing platform. We use it to specify and verify the HSE mechanism
   provided by Intel to isolate the code executed while the CPU is in System
   Management Mode (SMM), a highly privileged execution mode of x86
   microprocessors. We have written machine-checked proofs in the Coq proof
   assistant to that end.
2. We propose a novel approach inspired by algebraic effects to enable modular
   verification of complex systems made of interconnected components as a first
   step towards addressing the challenge posed by the scale of the x86 hardware
   architecture. This approach is not specific to hardware models, and could
   also be leveraged to reason about the composition of software components as
   well. In addition, we have implemented our approach in the Coq theorem
   prover, and the resulting framework takes advantage of Coq proof automation
   features to provide general-purpose facilities to reason about components
   interactions.

## Publications

If you are interested, you can have a look at the paper I wrote during my PhD:

- [SpecCert: Specifying and Verifying Hardware-based Security Enforcement
  Mechanisms](https://inria.hal.science/hal-01361422v1/file/speccert-fm2016.pdf),
  with Pierre Chifflier, Guillame Hiet and Benjamin Morin, at Formal Methods
  2016
- [Modular Verification of Programs with Effects and Effect Handlers in
  Coq](https://inria.hal.science/hal-01799712v1/file/main.pdf), with Yann
  Régis-Gianas, Pierre Chifflier and Guillaume Hiet, at Formal Methods 2018

You can also have a look at the Coq frameworks I have published:

- [SpecCert on Github](https://github.com/lthms/speccert) (CeCILL-B)
- [FreeSpec on Github](https://github.com/lthms/FreeSpec) (MPL-2.0)
