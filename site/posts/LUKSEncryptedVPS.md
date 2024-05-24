---
published: 2024-02-25
modified: 2024-05-23
series:
    parent: series/SelfHosting.html
    #next: posts/NspawnContainers.html
tags:
    - self-hosting
    - sysadmin
abstract: |
    I describe how I have set up the host (an Arch Linux system on a
    LUKS-encrypted partition) of `jasmine`.
---

# Installing a LUKS-Encrypted Arch Linux on a Vultr VPS

I’ve been a happy customer of [Vultr] for three years now. For one, this little
corner of the Internet is hosted on one of their VPS, along with other services
I have self-hosted. Recently, I have decided to migrate to a new
VPS with more disk space and more powerful vCPUs.

In this article, I describe how I have set up the host (an Arch Linux system on
a LUKS-encrypted partition) of `jasmine`[^jasmine]. I had done a similar thing
for `mulan`, `jasmine`’s predecessor. Unfortunately, I didn’t take the time to
document `mulan` installation steps three years ago. Needless to say, I had
plenty of opportunities to regret this oversight while I painfully redicovered
how to make this work.

Hopefully, most of what is in this write-up will stand the test of time and
remain true three years from now, when I migrate again 😅.

[^jasmine]: `jasmine` being my shiny new server—I have taken the habit to name
    my servers and personal computers after Disney princesses.

[Vultr]: https://vultr.com

## Booting on the Installation ISO

It is no surprise that Vultr does not propose an out-of-the-box LUKS-encrypted
Arch Linux installation in their OSes library. As a consequence, I had to boot
my brand new VPS on the [Arch Linux ISO].

1. In the Vultr dashboard, I visited the “ISOs” page (in the “Orchestrations”
   menu) to add the latest Arch Linux installation ISO.
2. Then, I went to the management panel of `jasmine`, more precisely in the
   “Settings” tab. I visited the “Custom ISO” page, and attached the Arch Linux
   ISO. This prompted a reboot.

[Arch Linux ISO]: https://geo.mirror.pkgbuild.com/iso/

`jasmine` happily booted the image, but the resulting system was lacking a SSH
server to connect to. Instead, I used the “View Console” feature to get a shell
access to my VPS[^vimium].

[^vimium]: It is noteworthy that I had to disable one of my Firefox extensions:
    Vimium. Vimium provides me vim-like keystrokes in the browser, and the keys
    I am using for motion (`t`, `s`, `r`, and `n`) were not forwarded to the
    console.

The Arch Linux installation ISO’s default keymap is qwerty, a keyboard layout I
am helpless with. The first command I always use in this situation is
`loadkeys`, which allows me to switch to the [`fr-bepo`][bepo] layout.

> [!NOTE]
> In this article, I am using `;` as the terminal prompt for [ease of
> copy/pasting](https://twitter.com/leostera/status/1740796853174596007).

```bash
; loadkeys fr-bepo
```

[bepo]: https://bepo.fr

## Remote Access to `jasmine`

The next step was to start a SSH server I could connect to using my terminal
emulator. A virtual console is nice enough, but when your muscle memory
commands you to hit `Ctrl-W` to delete the word before your cursor as soon as
you are connected to a shell, you don’t want to stay in a browser tab for
obvious reasons.

1. I set up a password for the `root` user using `passwd`.
2. I modified the `/etc/ssh/sshd_config` file to let me connect with the `root`
   user using a password (`PermitRootLogin yes`).
3. I started the SSH server using `systemctl start sshd`.

From there, I could connect `jasmine` from my terminal emulator.

```bash
# after modifying /etc/hosts to add `jasmine` IP there
; ssh root@jasmine
```

## Disk Partitions

Now that I was enjoying the comfort of my terminal emulator of choice
([kitty]), the serious business could start. Moving forward, my next task was
to set up the disk layout and the filesystems.

[kitty]: https://sw.kovidgoyal.net/kitty/

> [!WARNING]
> Did you know that Vultr VPS are using legacy boot and _not_ UEFI? I surely
> did, three years ago, but sadly I had forgotten. So I did a first
> installation setup with a EFI partition layout (GPT, `/boot` formatted with
> VFAT, etc.), only to discover that my shiny system could not boot.

To create an MBR partition system, `fdisk` is a nice enough tool. The disk is
exposed to the VPS under the name `/dev/vda`.

```bash
; fdisk /dev/vda
```

Firstly, I created a new MBR.

```
Command (m for help): o
```

Then, I created the `/boot` partition. To be sure I would not run out of space,
I allocated 3GBytes for it.

```
Command (m for help): n
Partition number (1-128, default 1): 
First sector (34-268435422, default = 2048) or {+-}size{KMGTP}: 
Last sector (2048-268435422, default = 268433407) or {+-}size{KMGTP}: +3G
```

The root partition was to take the remaining space.

```
Command (m for help): n
Partition number (2-128, default 2): 
First sector (34-268435422, default = 6293504) or {+-}size{KMGTP}: 
Last sector (6293504-268435422, default = 268433407) or {+-}size{KMGTP}: 
```

I reviewed the resulting partition layout.

```

Command (m for help): p

Disk /dev/vda: 128 GiB, 137438953472 bytes, 268435456 sectors
Units: sectors of 1 * 512 = 512 bytes
Sector size (logical/physical): 512 bytes / 512 bytes
I/O size (minimum/optimal): 512 bytes / 512 bytes
Disklabel type: dos
Disk identifier: 0xdbc3620d

Device     Boot   Start       End   Sectors  Size Id Type
/dev/vda1          2048   6293503   6291456    3G 83 Linux
/dev/vda2       6293504 268435455 262141952  125G 83 Linux
```

LGTM!

```
Command (? for help): w
```

## Filesystems

### `/boot` Partition

No need to be particularly fancy here. I formatted `/boot` with the `ext3`
filesystem. As far as I know, this is a reasonable default choice for this
partition.

```bash
; mkfs.ext3 /dev/vda1
```

## LUKS-Encrypted Root Partition

I mostly followed the [Arch Linux Wiki] for this. Generally speaking, the Arch
Linux Wiki is a wonderful source of information for anything related to Linux.

[Arch Linux Wiki]: https://wiki.archlinux.org/title/Dm-crypt/Encrypting_an_entire_system#LUKS_on_a_partition

I formatted `/dev/vda2` with `cryptsetup` to initialize the encryption scheme.

```bash
; cryptsetup -y -v luksFormat /dev/vda2
```

> [!IMPORTANT]
> Be sure to save your LUKS passphrase somewhere, otherwise you are likely to
> run in trouble at some point. I’ve personally added it to my Bitwarden.

As-is, the partition cannot be used; it needs to be “open” with `cryptsetup`.

```bash
; cryptsetup open /dev/vda2 root
```

`root` here is the name given to the usable partition. More precisely,  after
this command the partition can be manipulated through the `/dev/mapper/root`
logical volume.

Before, I had always used `ext4` for my root partition, but for a while I’ve
had an interest for alternative filesystems. And so, I decided out of the blue
to format `/dev/mapper/root` with `btrfs`[^btrfs]. I like the idea of a
filesystem compressing its contents by default.

```bash
; mkfs.btrfs -d single -m single /dev/mapper/root
; mount -t btrfs -o defaults,noatime,compress=zstd /dev/mapper/root /mnt
```

[^btrfs]: Time will tell if this was a mistake… The Internet seems to suggest
    it might be one 😅.

Finally, I could mount the two formatted partitions in `/mnt`.

```bash
; mkdir /mnt/boot
; mount /dev/vda1 /mnt/boot
```

## Installing Arch Linux

I have installed the bare minimum with `pacstrap`. I personally prefer entering
in the chroot as soon as possible.

```bash
; pacstrap -K /mnt base linux
; genfstab -U /mnt >> /mnt/etc/fstab
; arch-chroot /mnt
```

In the rest of the article, I focus on the details that are directly related to
our main subject. That is, being able to boot a LUKS-encrypted Arch Linux VPS.
To that end, I have chosen to reproduce the exact setup I did three years ago
for `mulan`. It consists in configuring the initramfs to spawn an SSH server
([tinyssh]) which let me enter the LUKS passphrase of `/dev/vda2` remotely.

[tinyssh]: https://tinyssh.org/

## `sshd`

Before configuring the boot process, it had to take a small detour and
configure the SSH server (`sshd` from OpenSSH) `jasmine` will start once it has
booted. The main reason is quite simple: I wanted tinyssh and `sshd` to use the
same host key.

tinyssh is limited in terms of the key types it supports, but I personally
always default to Ed25519 so I’m fine with that.

```bash
ssh-keygen -f /etc/ssh/ssh_host_ed25519_key -N '' -t ed25519
```

I then modified `/etc/ssh/sshd_config` to ensure `sshd` would default to it.

```bash
# in /etc/ssh/sshd_config, uncomment
HostKey /etc/ssh/ssh_host_ed25519_key
```

I used this opportunity to also (temporarily) allow login as root using a
password. Eventually, I will definitely remove this line from `sshd` config,
but while I’m configuring everything, it’s too convenient to bother with
another approach.

```bash
# in /etc/ssh/sshd_config, add
PermitRootLogin yes
```
 
This line is only useful if `root` has a password, so I initialized one.

```bash
; passwd
```

I also enabled the `sshd` service, to let systemd start `sshd` automatically at
boot time.

```bash
; systemctl enable sshd
```

## TinySSH

At this point, I knew I had only dealt with the easy bits. The hard part is
to be able the damn thing.

I have always used Busybox-based initial ramdisk. While rereading the Arch
Linux Wiki, I discovered it was also possible to use systemd, which… well,
nobody is surprised by this, I guess. I am a happy adopter of systemd multiple
features in general, but for the particular setup I am targeting, using systemd
means [installing an AUR package][aur]. So I decided to stick with Busybox.

[aur]: https://wiki.archlinux.org/title/Dm-crypt/Specialties#systemd_based_initramfs_(built_with_mkinitcpio)

I gathered and installed the packages I needed for this to work.

```
; pacman -S tinyssh mkinitcpio-tinyssh mkinitcpio-netconf mkinitcpio-utils python3
```

And I modified `/etc/mkinitcpio.conf` to modify the `HOOKS` array.

```diff
-HOOKS=(base udev autodetect modconf kms keyboard keymap consolefont block filesystems fsck)
+HOOKS=(base udev autodetect modconf block netconf tinyssh encryptssh filesystems keyboard keymap fsck)
```

I tried to keep it minimal (hence the removal of `kms` for instance, which does
not seem very useful for a remote server considering its about setting display
resolution), and I borrowed from the `/etc/mkinitcpio.conf` file of `mulan` for
`netconf`, `tinyssh` and `encryptssh`.

Turns out `mkinitcpio-tinyssh` is affected by [a long standing bug][bug], but
fortunately the patch to `/usr/lib/initcpio/install/tinyssh` worked like a
charm.

```diff
   local return_code=1
 
   if [ ! -d $destdir -a -x /usr/bin/tinyssh-convert ]; then
-      mkdir $destdir
-  fi
-  
-  if [ -s "$osshed25519" -a ! -s $destdir/.ed25519.sk -a ! -s $destdir/ed25519.pk -a -x /usr/bin/tinyssh-convert ]; then
-      tinyssh-convert -f $osshed25519 -d $destdir
+      tinyssh-convert $destdir < $osshed25519
       if [ $? -eq 0 ]; then
           return_code=0
       fi
```

[bug]: https://github.com/grazzolini/mkinitcpio-tinyssh/issues/10

On my local machine, I generated a brand new SSH key using the Ed25519 key
type.

```bash
; ssh-keygen -t ed25519 -f jasmine
```

I copy/pasteed the content of `jasmine.pub` in `/etc/tinyssh/root_key` on
`jasmine`. It was also a good idea to delete the `etc/tinyssh/sshkeydir`
directory, before running the command to generate the initial ramkdisk.

```bash
; mkinitcpio -p linux
```

## Grub

This is your periodic reminder that Vultr does not support UEFI and still
requires to the legacy MBR to boot. This means `systemd-boot` is out of the
picture. I always feel overwhelmed when i have to configure Grub. However,
three years ago I managed to make it work, so I decided to stick to this again.

```bash
; pacman -S grub
; grub-install --target=i386-pc /dev/vda
; grub-mkconfig -o /boot/grub/grub.cfg
```

`/boot/grub/grub.cfg` contains a lot of things. I looked for the line 

```
### BEGIN /etc/grub.d/10_linux ###
```

In the first `menuentry` after it, I modified one line[^ucode].


[^ucode]: My initial thought was to install the `intel-ucode` package, and to
    configure Grub to load Intel’s microcode upgrades at boot time. However,
    since `jasmine` is a VPS, it does not directly access the physical CPU it
    is running onto. As a consequence, this step is not necessary.

First, the `linux` line.

```
        linux   /vmlinuz-linux root=/dev/mapper/root rw cryptdevice=UUID=7e58f868-529
a-4d70-bdfd-31317017c30b:root ip=<server ip>::<server gateway>:<server netmask>::eth0:none logle
vel=3 quiet
```

The one is the most tricky.

- `root=/ev/mapper/root rw` is the most straightforward. It means the root
  filesystem in located in `/dev/mapper/root`, that is a logical volume.
- `cryptdevice=UUID=7e58f868-529a-4d70-bdfd-31317017c30b:root` tells the kernel
  that the `root` logical volume is inside the encrypted (`cryptdevice`)
  `/dev/vda2` partition. To get the `UUID` of `/dev/vda2`, I used `blkid`.

```bash
; blkid | grep UUID
/dev/mapper/root: UUID="0a44e4c7-10b7-4e85-8228-7663cf16a631" UUID_SUB="0c9edc1c-31c0-417d-93e2-6f035c68b7cb" BLOCK_SIZE="4096" TYPE="btrfs"
/dev/vda2: UUID="e9695de0-403c-4a6c-b8a2-9891dca2a60a" TYPE="crypto_LUKS" PARTUUID="dbc3620d-02"
/dev/vda1: UUID="fa7a24d2-fc76-4af2-b26c-58548650253f" BLOCK_SIZE="4096" TYPE="ext3" PARTUUID="dbc3620d-01"
```

- `ip=<server ip>::<server gateway>:<server netmask>::eth0:none` tells the
  kernel enough information for tinyssh to be accessible from the Internet.
  These three IPS can be found in the “Settings” tab of `jasmine` management
  panel in the Vultr dashboard.

## Networking

There was only one step remaining before rebooting `jasmine` without the
installation ISO attached: configuring the system to ensure remote access. In
practice, it means enabling DHCP for the Ethernet interface (named `ens3` in
`jasmine`’s case).

I did that by defining a `.network` unit in `/etc/systemd/networkd` to enable
DHCP so that `jasmine` can get its ip from Vultr DHCP server.

```
# /etc/systemd/network/50-ens3.network
[Match]
Name=ens3

[Network]
DHCP=yes
```

As a last touch, I enabled both `systemd-networkd` and `systemd-resolved`.


```bash
; systemctl enable systemd-networkd
; systemctl enable systemd-resolved
; ln -sf ../run/systemd/resolve/stub-resolv.conf /etc/resolv.conf
```

And I was good to go!

I exited the chroot, came back to Vultr dashboard to detach the custom ISO from
`jasmine`, which prompted a reboot of the VPS. A look a the virtual console was
enough to confirm tinyssh had started and was waiting for incoming connection.
I edited my `~/.ssh/known_hosts` to remove `jasmine` now out-dated line, and
tried to connect to `jasmine`. tinyssh asked me kindly the passphrase for
`/dev/vda1`, before closing the connection.

A new attempt at connection to `jasmin` using SSH led me to the expected
system. Hourray!

## Conclusion

Needless to say, while this article is meant to propose a linear story to its
readers, my personal journey was everything but. I had to reboot many times
into the installation ISO, to mount my root partition and tweak the
configuration until it finally worked.

Hopefully, this article lists the various pitfalls I ran into, and how I fixed
them. It’ll be helpful for Future Me, and maybe to you before that.
