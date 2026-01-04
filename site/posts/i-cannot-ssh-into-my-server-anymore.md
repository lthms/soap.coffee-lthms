---
tags:
    - coreos
    - docker
    - meta
    - self-hosting
    - sysadmin
    - terraform
    - vultr
series:
    parent: series/SelfHosting.html
    prev: posts/LUKSEncryptedVPS.html
abstract: |
    To kick off 2026, I had clear objectives in mind: decommissioning my trusty
    VPS and setting up its successor. Embracing a complete paradigm shift, I
    built myself a container-centric, declarative, and low-maintenance setup
    for the years to come.
---

# I Cannot SSH Into My Server Anymore (And That’s Fine)

This week, I had clear objectives in mind: decommissioning `moana`, my trusty
$100+/month VPS, and setting up `tinkerbell`, its far less costly successor.
Now that the latter is up and running, I cannot even SSH into it. In fact,
*nothing* can.

There is no need. To publish a new article, I push a new Docker image to the
appropriate registry with the correct tag. `tinkerbell` will fetch and deploy
it. All on its own.

In this article, I walk through the journey that led me to the smoke and
mirrors behind this magic trick: [Fedora CoreOS], [Ignition] and [Podman
Quadlets] in the main roles, with [Terraform] as an essential supporting
character. This stack checks all the boxes I care about.

[Fedora CoreOS]: https://fedoraproject.org/coreos/
[Ignition]: https://coreos.github.io/ignition/
[Podman Quadlets]: https://docs.podman.io/en/latest/markdown/podman-quadlet.1.html
[Terraform]: https://developer.hashicorp.com/terraform

> [!NOTE]
> For interested readers, I have published [`tinkerbell`’s full setup][repo] on
> GitHub. This article reads as an experiment log, and if you are only
> interested in the final result, you should definitely have a look.

[repo]: https://github.com/lthms/tinkerbell

## Container-Centric, Declarative, and Low-Maintenance

Going into this, I knew I didn’t want to reproduce `moana`’s setup—it was fully
manual[^blog] and I no longer have the time or the motivation to fiddle with
the internals of a server. Instead, I wanted to embrace the principles my
DevOps colleagues had taught me over the past two years.

[^blog]: In the end, I never took the time to publish a write-up about it, so
    in a nutshell: everything relied on [a small script][nspawn] that enabled
    me to seamlessly create interconnected [nspawn containers].

[nspawn]: https://github.com/lthms/nspawn
[nspawn containers]: https://man7.org/linux/man-pages/man5/systemd.nspawn.5.html

My initial idea was to start from [the image I had already written for this
website](./DreamWebsite.html), and to look for the most straightforward and
future-proof way to deploy it in production™.

[Docker Compose] alone wasn’t a good fit. I like compose files, but one needs
to provision and manage a VM to host them. Ansible can provision VMs, but that
road comes with its own set of struggles. Writing good playbooks has always
felt surprisingly difficult to me, and I’ve never managed to keep a server tidy
over time using that approach.

[Kubernetes] was _very_ appealing on paper. I have seen engineers turn compose
files into [Helm charts] and be done with it. If I could do the same thing,
wouldn’t that be bliss? Unfortunately, Kubernetes is a notoriously complex
stack, resulting from compromises made to address challenges I simply don’t
face. Managed clusters could make things easier, but they aren’t cheap. That
would defeat the initial motivation behind retiring `moana`.

[CoreOS], being an operating system specifically built to *run containers*,
obviously stood out. That said, I had very little intuition on how it could
work in practice. So I started digging. I learned about Ignition first. Its
purpose is to provision a VM exactly once, at first boot. If you need to change
something afterwards, you throw away your VM and create a new one[^fp]. I found
out how to use systemd unit files to start containers via `podman` CLI
commands. That was way too cumbersome, so I pushed on for a way to orchestrate
containers *à la* Docker Compose. That’s when I discovered Podman Quadlets and
[auto-updates].

With that, everything clicked. I knew what I wanted to do, and I was very
excited about it.

[^fp]: CoreOS and Ignition taught me to think about virtual machines the same
    way OCaml or Haskell taught me to think about data: as immutable values.

[Docker Compose]: https://docs.docker.com/compose/
[Kubernetes]: https://kubernetes.io/
[Helm charts]: https://helm.sh/docs/topics/charts/
[CoreOS]: https://fedoraproject.org/coreos/
[auto-updates]: https://docs.podman.io/en/stable/markdown/podman-auto-update.1.html

## Shaping The Immutable VM

For more than a year now, my website has been [served from RAM by a standalone,
static binary built in OCaml][dream], with TLS termination handled by Nginx and
`certbot`’s certificates renewal performed by yours truly[^manual]. I didn’t
have any reason to fundamentally change this architecture. I was simply looking
for a way to automate their deployment.

[^manual]: I didn’t lie when I said `moana`’s setup was indeed _manual_.

### Container-Centric, …

The logical thing to do was to have `tinkerbell` run two containers:

- **The reverse proxy:** I had been firmly on Team Nginx for years now, but
  when I heard [Caddy] could “*automatically obtain* and *renew* TLS
  certificates,” I was sold on giving it a try.
- **The website itself:** Static binaries can be wrapped inside a container
  with close to zero overhead using the [`scratch`][scratch] base image, so I
  did just that. I published it to a free-plan, public Docker registry hosted
  on Vultr that I created for the occasion[^offline].

[^offline]: Which means getting an off-line copy of this website is now as
    simple as calling `docker pull ams.vultrcr.com/lthms/www/soap.coffee:live`.

[dream]: ./DreamWebsite.html
[Caddy]: https://caddyserver.com/
[scratch]: https://hub.docker.com/_/scratch

#[Nothing beats a straightforward architecture](https://mermaid.ink/img/pako:eNo9UMtOwzAQ_BVrTyCllZs4JPEBiYZjuQASEnUPTrxJLBK7ch1BafPvuC_2tDM7M7vaA9RWIXBoevtdd9J5snoVhoR6Wpe9RuM3ZDZ7PPKcEs5YciTLtYBSKrUnd--rt3sBm4t-N1atk9uOeG2-0FXY95fB8hZwJOX6A6ud9nj1oFEQQeu0Au7diBEM6AZ5gnA4SQT4DgcUwENrcPRO9gKEmYJtK82ntcPN6ezYdsAb2e8CGrdKenzWMtw0_LMuLERX2tF44AnLziHAD_ATIM3mMY3zlCZskRUPRQR74DGL58WCXrk8S6cIfs9b6TxlWZ4EcsFYkdOgR6W9dS-Xj9bWNLqF6Q97DWuS?type=png)

Nothing fancy or unexpected here, which is why it felt like a good target for a
first deployment. It was time to open Neovim to write some YAML.

### Declarative, …

At this point, the architecture was clear. The next step was to turn it into
something a machine could execute. To that end, I needed two things: first an
Ignition configuration, then a CoreOS VM to run it.

#### The Proof of Concept

Ignition configurations (`.ign`) are JSON files primarily intended to be
consumed by machines. They are produced from YAML files using a tool called
[Butane]. For instance, here is the first Butane configuration file I ended up
writing. It provisions a CoreOS VM by creating a new user (`lthms`), along with
a `.ssh/authorized_keys` file allowing me to SSH into the VM[^ssh].

[^ssh]: I didn’t know at the time that I would _deliberately_ remove these
    lines from the final Butane file.

```yaml
variant: fcos
version: 1.5.0
passwd:
  users:
    - name: lthms
      ssh_authorized_keys:
        - ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIKajIx3VWRjhqIrza4ZnVnnI1g2q6NfMfMOcnSciP1Ws lthms@vanellope
```

What’s important to keep in mind is that Ignition runs exactly once, at first
boot. Then it is never used again. This single fact has far-reaching
consequences, and is the reason why any meaningful change implies replacing the
machine, not modifying it.

[Butane]: https://coreos.github.io/butane/

Before going any further, I wanted to understand how the actual deployment was
going to work. I generated the Ignition configuration file.

```bash
butane main.bu > main.ign
```

Then, I decided to investigate how to write the Terraform module that would
create a Vultr VM. The resulting file is twofold. First, we need to configure
Terraform to be able to interact with the Vultr API, using the [Vultr
provider]. Second, I needed to [create the VM][vultr_instance][^cli] and fed it
the Ignition configuration.

[Vultr provider]: https://registry.terraform.io/providers/vultr/vultr/latest/docs
[vultr_instance]: https://registry.terraform.io/providers/vultr/vultr/latest/docs/resources/instance 

[^cli]: For discovering what values to put in most fields, `vultr-cli` is
    pretty convenient. Kudos to the Vultr team for making it in the first
    place.

```hcl
resource "vultr_instance" "tinkerbell" {
  region = "cdg"
  plan = "vc2-1c-1gb"
  os_id = "391"

  label = "tinkerbell"
  hostname = "tinkerbell"

  user_data = file("main.ign")
}
```

And that was it. I invoked `terraform apply`, waited for a little while, then
SSHed into the newly created VM with my `lthms` user. Sure enough, the
`tinkerbell` VM was now listed in the Vultr web interface. I explored for a
little while, then called `terraform destroy` and rejoiced when everything
worked as expected.

#### The MVP

At this point, I was basically done with Terraform, and I just needed to write
the Butane configuration that would bring my containers to life. As I mentioned
earlier, the first approach I tried was to define a systemd service responsible
for invoking `podman`.

```yaml
systemd:
  units:
    - name: soap.coffee.service
      enabled: true
      contents: |
        [Unit]
        Description=Web Service
        After=network-online.target
        Wants=network-online.target

        [Service]
        ExecStart=/usr/bin/podman run \
          --name soap.coffee \
          -p 8901:8901 \
          --restart=always \
          ams.vultrcr.com/lthms/www/soap.coffee:latest
        ExecStop=/usr/bin/podman stop soap.coffee

        [Install]
        WantedBy=multi-user.target
```

Adding this entry in my Butane configuration and redeploying `tinkerbell` got
me exactly what I wanted. My website was up and running. For the sake of
getting something working first, I added the necessary configuration for Caddy
(the container and the provisioning of its configuration file), redeployed
`tinkerbell` again, only to realize I also needed to create a network so that
the two containers could talk together. After half an hour or so, I got
everything working, but was left with a sour taste in my mouth.

This would simply not do. I wasn’t defining anything, I was writing a shell
script in the most cumbersome way possible.

Then, I remembered my initial train of thoughts and started to search for a way
to have Docker Compose work on CoreOS[^podman]. That is when I discovered
Quadlet, whose [initial repository does a good job
justifying][why-quadlet][^archived]. In particular,

> With quadlet, you describe how to run a container in a format that is very
> similar to regular systemd config files. From these actual systemd
> configurations are automatically generated (using [systemd generators][gen]).

[why-quadlet]: https://github.com/containers/quadlet
[gen]: https://github.com/containers/quadlet

[^podman]: Well, Podman Compose, I guess.
[^archived]: This repository is now archived, since Quadlet has got merged
    upstream.

To give a concrete example, here is the `.container` file I wrote for my
website server.

```ini
[Container]
ContainerName=soap.coffee
Image=ams.vultrcr.com/lthms/www/soap.coffee:live

[Service]
Restart=always

[Install]
WantedBy=multi-user.target
```

I wasn’t wasting my time teaching systemd how to start containers anymore. I
was now declaring what should exist, so that systemd—repurposed for the
occasion as a container orchestrator—could take care of the rest.

I excitedly turned `caddy.service` into `caddy.container`, redeployed
`tinkerbell`, ran into the exact same issue I had encountered before and
discovered the easiest way for two Quadlet-defined containers to talk to each
other was to introduce a [*pod*][pod]. In a nutshell, containers attached to
the same pod share the same localhost interface, which means they can
effectively communicate together as long as they do not try to use the same
ports.

To define a pod, one needs to create a `.pod` file, and to reference it in
their `.container` files using the `PodName=` configuration option. A “few”
redeployments later, I got everything working again, and I was ready to call it
a day.

> [!TIP]
> If your containers are basically ignored by systemd, be smarter than me. Do
> not try to blindly change your `.container` files and redeploy your VM in a
> very painful and frustrating loop. Simply ask systemd for the generator logs.
>
> ```
> sudo journalctl -b | grep -i quadlet 
> ```

And with that, `tinkerbell` was basically ready.

[pod]: https://docs.podman.io/en/latest/_static/api.html?version=latest#tag/pods

### And Low-Maintenance

Now, the end of the previous section might have given you pause.

Even a static website like this one isn’t completely “stateless.” Not only does
Caddy require a configuration file to do anything meaningful, but it is also a
stateful application as it manages TLS certificates over time. Besides, I *do*
publish technical write-ups from time to time[^2025].

[^2025]: Two in 2025, that’s true. But 2026 is only starting, you never know
    what might come!

Was I really at peace with having to destroy and redeploy `tinkerbell` every
time I need to change anything on my website?

On the one hand, _yes_. I believe I could live with that. I modify my website
only a handful of times even in good months, I think my audience could survive
with a minute of downtime before being allowed to read my latest pieces. It may
be an unpopular opinion, but considering my actual use case, it *was* good
enough. Even the fact that I do not store the TLS certificates obtained by
Caddy anywhere persistent should not be an issue. I mean, Let’s Encrypt has
fairly generous weekly issuance limits per domain [^tls]. I should be fine.

[^tls]: How do I know that? Well... I might have hit the limit while hacking my
    way to a working setup.

On the other hand, the setup was starting to grow on me, and I have _other_ use
cases in mind that could be a good fit for it. So I started researching again,
this time to understand how a deployment philosophy so focused on immutability
was managing what seemed to be conflicting requirements.

I went down other rabbit holes, looking for answers. The discovery that stood
out the most to me—to the point where it became the hook of this article—was
Podman auto-updates.

To deploy a new version of a containerized application, you pull the new image
and restart the container. When you commit to this pattern, why should you be
the one performing this action? Instead, your VM can regularly check registries
for new images, and *update the required containers when necessary*. In
practice, Podman makes this approach trivial. I just needed to label my
containers with `io.containers.autoupdate` set to `registry`, enable the
`podman-auto-update` timer[^dropin], and that was it.

And that is when I realized something. At this point, publishing an image
becomes the only deployment step. I didn’t need SSH anymore.

[^dropin]: By default, the timer is triggered once a day, which felt
    unnecessarily long, so I decided to make it hourly instead.

## The Road Ahead

`tinkerbell` has been running for a few days now, and I am quite pleased with
the system I have put in place. In retrospect, none of this is particularly
novel. It feels more like I am converging toward a set of practices the
industry has been gravitating toward for years.

#[Always has been—ah, no, it’s not the correct meme.](/img/iac-meme.jpg)

The journey is far from being over, though. `tinkerbell` is up and running, and
it served you this HTML page just fine, but the moment I put SSH out of the
picture, it became a black box. Aside from some hardware metrics kindly
provided by the Vultr dashboard, I have no real visibility into what’s going on
inside. That is fine for now, but it is not a place I want to stay in forever.
I plan to spend a few more weekends building an observability stack[^tls2].
That will come in handy when things go wrong—as they inevitably do. I would
rather have the means to understand failures than guess my way around them.

[^tls2]: Oh, and maybe I will move these TLS certificates in a block storage or
    something. That could be a good idea.

Did I ever mention I am an enthusiastic Opentelemetry convert?
