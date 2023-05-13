---
published: 2023-04-27
tags: ['spatial-shell']
abstract: |
    In August, 2022, I have discovered Material Shell, and decided to implement
    a dynamic tiling management “a la Material Shell” for sway I called Spatial
    Shell. Spatial Shell works on my machine, which means it will definitely
    break on yours, and I would love to know how.
---

# Spatial Shell: Call For Testers

In August 2022, I have discovered [Material
Shell](https://material-shell.com). A few weeks later, I had pieced together a
working prototype of a dynamic tiling management “a la Material Shell” for
[sway](https://swaywm.org). By October, the project was basically fulfilling my
needs, and I had already started to use it on my workstation[^1]. The project
sat there for a while until I rediscovered this thing called *holidays*.

[^1]: I tried so you do not have to: having my graphical session going crazy
      during a work meeting because of a software I had written.

For a short week, I tried to address at many of the remaining issues and
missing features that I was aware of. Then, I started to write
[man pages](https://lthms.github.io/spatial-shell/spatial.1.html), which
turned out to be the perfect opportunity to clean up every clunkiness I could
possibly find.

I can’t help but find the result rather nice and satisfying, and I hope you
will enjoy it too! [Spatial Shell](https://github.com/lthms/spatial-shell)
works on my machine, which means it will definitely break on yours. But this is
where the fun lies, right? At this point, I definitely think the project is
ready to fall into the hands of (motivated) alpha testers.

Anyway, let me give you a tour!

## Spatial Model

At its core, Spatial Shell allows you to navigate a grid of windows.
Workspace are rows which can be individually configured to determine how many
windows (cells) you can see at once. More precisely, workspaces in Spatial
Shell can use two layouts:

- **Maximize:** One window is displayed at a time
- **Column:** Several windows are displayed side by side, to your convenience

The reason **Maximize** is not a particular case of **Column**, but instead a
layout on its own, is to easily allow you to switch to and back from maximizing
the focused window. The following picture[^2] summarizes one particular setup with
tree workspaces, each configured differently.

[^2]: Created using [Excalidraw](https://excalidraw.com/).

#[Spatial Shell allows users to configure the layout of each workspace individually.](/img/spatial-shell-example.png)

- Workspace 1 contains three windows, and uses the **Column** layout to display
  at most three windows, so each window is visible, with the focus being on
  the leftmost one.
- Workspace 2 contains four windows, and uses the **Column** layout to display at
  most two windows. As a consequence, two windows are not visible.
- Workspace 3 contains two windows, and uses the **Maximize** layout so only the
  focused window is visible.

To help users know which window is currently holding the focus, Spatial Shell
slightly reduces the opacity of unfocused windows (as poorly hinted by the gray
backgrounds in the figure). Finally, Spatial Shell can also set a background
for empty workspaces (using `swaybg`{.bash} under the hood).

And this is basically it. There is not much more to say about Spatial Shell
features.

## Configuration

From an implementation and user experience perspective, Spatial Shell is taking
inspiration from i3 and sway.

More precisely, Spatial Shell comprises two executables:

- [**spatial**(1)](https://lthms.github.io/spatial-shell/spatial.1.html), the
  daemon implementing the spatial model described in the previous section, and
- [**spatialmsg**(1)](https://lthms.github.io/spatial-shell/spatialmsg.1.html), a
  client used to control the current instance of spatial.

Assuming `$spatial`{.bash} and `$spatialmsg`{.bash} contains the paths to
spatial and spatialmsg binaries respectively, then the simplest sway
configuration to start using Spatial Shell is the following

```bash
exec $spatial

# moving the focus
bindsym $mod+h exec $spatialmsg "focus left"
bindsym $mod+l exec $spatialmsg "focus right"
bindsym $mod+k exec $spatialmsg "focus up"
bindsym $mod+j exec $spatialmsg "focus down"

# moving the focused window
bindsym $mod+Shift+h exec $spatialmsg "move left"
bindsym $mod+Shift+l exec $spatialmsg "move right"
bindsym $mod+Shift+k exec $spatialmsg "move up"
bindsym $mod+Shift+j exec $spatialmsg "move down"

# toggle between Maximize and Column layout
bindsym $mod+space exec $spatialmsg "toggle layout"

# modify the number of windows to display in the Column layout
bindsym $mod+i exec $spatialmsg "column count decrement"
bindsym $mod+o exec $spatialmsg "column count increment"

# start waybar, spatial will take care of the rest
exec waybar
```

By default, Spatial Shell sets the initial configuration of a workspace to
the Column layout with two columns at most, and sets the opacity of the
unfocused windows to 75%. This can be customized, either globally or per
workspace, by creating a configuration file in
`$XDG_CONFIG_HOME/spatial/config`{.bash}[^3].

[^3]: If unset, `$XDG_CONFIG_HOME`{.bash} defaults to
      `$HOME/.config`{.bash}.

For instance, my config file looks like that.

```bash
[workspace=3] default layout maximize
background "~/.config/spatial/wallpaper.jpg"
unfocus opacity 85
```

See [**spatial**(5)](https://lthms.github.io/spatial-shell/spatial.5.html) for
the list of commands supported by Spatial Shell.

As a side note, readers familiar with sway will definitely pick the resemblance
with sway and swaymsg, and it actually goes pretty deep. In a nutshell, swaymsg
connects to a UNIX socket created by sway at startup time, to send it commands
(see [**spatial**(5)](https://lthms.github.io/spatial-shell/spatial.5.html))
using a dedicated IPC protocol inherited from i3 (see
[**sway-ipc**(7)](https://lthms.github.io/spatial-shell/sway-ipc.7.html)). Not
only spatial also relies on sway IPC protocol to interact with sway and
implement its spatial model, it creates a UNIX of its own, and supports its own
protocol
([**spatial-ipc**(7)](https://lthms.github.io/spatial-shell/spatial-ipc.7.html][spatial-ipc.7.html)).

## Waybar Integration

It is a common practice to use a so-called “bar” with sway, to display some
useful information about the current state of the system. In the `contrib/`
directory of [Spatial Shell repository](https://github.com/lthms/spatial-shell),
interested readers will find a configuration for
[Waybar](https://github.com/Alexays/Waybar)[^design]. This configuration is
somewhat clunky at the moment, due to the limitations of the custom widget of
Waybar which does not allow to have one widget defines several “buttons.” I am
interested in investing a bit of time to see if I could write a native widget,
similarly to sway’s one.

[^design]: Readers familiar with Material Shell design will not be surprised by
           the general look and feel of the screenshot below.

#[Mandatory screenshot of Spatial Shell, with the Waybar configuration.](/img/spatial-shell.png)

That being said, the user experience with this integration is already pretty
neat. As long as you don’t need more than 6 workspaces and 8 windows per
workspaces[^constants], you are good to go!

[^constants]: These constants are totally arbitrary and can be increased by
              modifying the Waybar config, but the issue will remain that a
              limit will exist.

## Building from Source

As of April 2023, the only way to get Spatial Shell is to build it from source.

You will need the following runtime dependencies:

- sway (i3 might be supported at some point)
- gmp (for bad reasons, fortunalety this will be removed at some point)
- swaybg
- waybar (if you want the full experience)

You will need the following build dependencies:

- opam
- scdoc (for the man pages)

Then, building and installing Spatial Shell is as simple as using the two
following commands.

```bash
make build-deps
make install
```

The latter command will install Spatial Shell’s binaries in
`/usr/local/bin`{.bash}, and the man pages in `/usr/local/man`{.bash}. You can
remove them with `make uninstall`{.bash}.

To install Waybar theme, copy `contrib/waybar/spatialbar.py`{.bash} to
`/usr/local/bin/spatialbar`{.bash} for instance, and the Waybar style and
config file to `$HOME/.config/waybar`{.bash}.
