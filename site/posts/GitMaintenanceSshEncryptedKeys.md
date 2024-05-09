---
published: 2024-02-18
tags: ['workflow', 'git']
abstract: |
    `git maintenance` allows to run on the background a set of tasks which
    optimize commands like `git add` and `git fetch` for a responsive user
    experience. Out of the box, the scripts run by `git mainentance` have no
    way to use encrypted SSH keys, but it is possible to fix this.
---

# Using `git maintenance` with Encrypted SSH Keys

This year, I went to [FOSDEM 2024](https://fosdem.org/2024). It was nice and
~~cosy~~ crowded, and I really enjoyed my time there. The very last talk I
could attend to before having to leave for the train station was “[So You Think
You Know
Git](https://www.youtube.com/watch?v=aolI_Rz0ZqY&pp=ygUZc28geW91IHRoaW5rIHlvdSBrbm93IGdpdA%3D%3D)”
by [Scott Chacon](https://twitter.com/chacon). If you haven’t already, go and
watch it. It is a very good and educational presentation. You will learn what
`git blame -C -C -C` does and never be the same.

Another takeaway for me was `git maintenance`. `git maintenance` allows running
in the background a set of tasks which optimize commands like `git add` and
`git fetch` for a responsive user experience. I mean, count me in! Our git
repository at `$WORK`{.bash} has become fairly big over the years[^mono-repo].

[^mono-repo]: Not [_mono-repo_
    big](https://youtu.be/aolI_Rz0ZqY?si=-ielyNVXwREJqupo&t=1430) yet, but
    still big enough to make `git fetch --all --prune` feels… well,
    unresponsive.

So, when I came back to work the next day, I run the magic command the speaker
had mentioned[^prompt].

```bash
; git maintenance start
```

[^prompt]: Following [a petition from the
    Internet](https://twitter.com/leostera/status/1740796853174596007), my
    terminal prompt is `;`.

This created a bunch of user systemd services and timers which I decided to run
immediately to test that everything was working correctly, starting with the
hourly service responsible for prefetching remote branches.

```bash
; systemctl --user start git-maintenance@hourly.service
```

Unfortunately, this did not work out, and for predictable reasons.

```bash
; systemctl --user status git-maintenance@hourly.service
(...)
systemd[1706]: Starting Optimize Git repositories data...
git[76228]: git@gitlab.com: Permission denied (publickey).
git[76226]: error: failed to prefetch remotes
git[76226]: error: task 'prefetch' failed
systemd[1706]: git-maintenance@hourly.service: Main process exited, code=exited, status=>
systemd[1706]: git-maintenance@hourly.service: Failed with result 'exit-code'.
systemd[1706]: Failed to start Optimize Git repositories data.
```

The culprit here is the fact I am using an encrypted SSH key to connect to
Gitlab where our repository is hosted and out of the box the scripts run by
`git-maintenance` have now way to use them. This is because `git-maintenance`
is not aware of the existence of the SSH agent running on my laptop.

The solution can be read in the Man page of `git-maintenance`:

> (…) any customization should be done by creating a drop-in file, *i.e.* a
> `.conf` suffixed file in the
> `~/.config/systemd/user/git-maintenance@.service.d` directory.

I didn’t know this general purpose trick which should work for any systemd
service running on a Linux machine! Thanks, anonymous technical writer who took
the time to contribute to this Man page.

And indeed, creating a file named `10-ssh.conf`[^prefix] in
`${HOME}/.config/systemd/user/git-maintenance@.service.d/` to set the
`SSH_AUTH_SOCK` environment variable solved my issue. Its value depends on your
personal setup. In my case, I am using the systemd `ssh-agent.service` user
unit.

[^prefix]: The prefix number is as important as the `.conf` suffix mentioned in
    the `git-maintenance` Man page for systemd to load the drop-in file.

```bash
; systemctl --user show ssh-agent.service | grep Environment=SSH_AUTH_SOCK
Environment=SSH_AUTH_SOCK=/run/user/1000/ssh-agent.socket
```

We replicate this in our `10-ssh.conf`.

```systemd
[Service]
Environment=SSH_AUTH_SOCK=/run/user/1000/ssh-agent.socket
```

And we are done! This time, executing the service manually will work (assuming
the necessary encrypted key has been `ssh-add` to the agent).

```bash
; systemctl --user daemon-reload
; systemctl --user start git-maintenance@hourly.service
; systemctl --user status git-maintenance@hourly.service
(...)
systemd[1706]: Starting Optimize Git repositories data...
systemd[1706]: Finished Optimize Git repositories data.
```
