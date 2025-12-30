---
published: 2025-06-02
modified: 2025-06-03
tags:
  - ocaml
  - vibecoding
abstract: |
    A recollection of challenging myself to implement a simple tool to generate
    a summary from YouTube videos using Vosk for speech recognition and Ollama
    for generating summaries using LLMs running locally.
---

# Peer-Programming in Modern OCaml with ChatGPT and Gemini 

It is June 2025, and LLMs are everywhere and do everything now. I have never
been a diligent adopter of them myself. The past few months, I started to feel
a bit “left out,” though. Colleagues and friends are starting to integrate
LLM-powered tools into their personal toolkit, with notable successes.

Early May, I decided to challenge myself to implement a simple tool to generate
a summary from YouTube videos using [Vosk](https://alphacephei.com/vosk/) for
speech recognition and [Ollama](https://ollama.com/) for generating summaries
using LLMs running locally. I could hit two birds with one stone—experimenting
with LLMs to write and power software.

I decided to implement as much as possible in OCaml, for two main reasons.
Firstly, this is the main language I use at `$WORK`{.bash}. I wanted to get a
sense of how LLMs could help with the software stack I used 7+ hours a day.
Secondly, it was a good opportunity to catch-up with the OCaml 5 ecosystem
([Eio](https://github.com/ocaml-multicore/eio) in particular).

This write-up is a sort of dev log of this exercise. Its main focus is not to
explain in depth the code I ended up writing, but rather to recollect on my
wins and losses in adding LLMs in my developer toolkit.

## TL;DR

In this article, I am using “Tip” blocks to highlight my key findings and
lessons learned. That being said, for readers in a hurry, here’s how ChatGPT
summarizes these blocks.

* Prompting is a skill that improves through trial and error—many failed
  prompts help build intuition.  
* LLMs may suggest non-existent functions; using LSP tools helps identify these
  quickly.  
* Standard formats like WAV lead to more accurate LLM outputs.  
* LLMs without session memory tend to repeat mistakes; shared context is
  important.  
* Structuring commit message prompts (e.g., What / Why / How) produces
  consistently good results.  
* LLMs struggle with libraries like Eio, possibly due to name ambiguity or
  unstable APIs.  
* Providing project-specific context (e.g., via `direnv`) is likely to help
  reduce repeated hallucinations.  
* Prompting LLMs for MR descriptions or commits can eliminate empty submissions
  and speed up review.

You should still definitely read the full piece, though. I don’t think my
prompt was particularly good 🤫.

## Editor Integration

My first task was to grant myself the ability to leverage LLMs from my editor.
I had been using the web chat of ChatGPT for a while, but it now felt
antiquated since I had seen a freshly hired coworker get ChatGPT to generate
for themselves a dozen tests directly from VS Code.

I have returned to [Neovim](https://neovim.io) for a few years, and I am not
ready to migrate to VS Code. I would have been surprised if the Vim/Neovim
communities wouldn’t have a viable plugin for me, though.

I asked both ChatGPT and Gemini to find my candidates, but the plugins they
suggested seemed unmaintained, often outdated.

In the end, I found [CodeCompanion.nvim](https://github.com/olimorris/codecompanion.nvim)
by myself, through a good old Google research. I asked ChatGPT why it hadn’t
suggested it to me, and it seems like my prompt were biased. By asking for
“a Neovim ChatGPT plugin” or “a plugin to integrate Gemini to Neovim,” I had
unnecessarily narrowed the LLM scope.

> [!TIP]
> I guess one does not become a prompt engineer in a day. This is actually one
> of the reasons I want to use LLMs more seriously. To build myself intuitions
> of which prompts work and which don’t. After this project, I have mostly
> uncovered a bunch of the latter category 😅.

[**@yurug**](https://twitter.com/yurug) had told me he was impressed by Gemini
Pro, so I decided to make it the default adapter for the `CodeCompanionChat`
command. I tried to make Gemini Pro the default model for this adapter, it was
challenging and LLMs weren’t able to help. When I finally found the correct
`setup` option, it turns out I hadn’t generated a token allowing me to use Pro.

Well. That gave me the opportunity to benchmark Gemini Flash, then.

## Speech Recognition with Vosk

ChatGPT suggested Vosk as a way to get a transcript of an audio file, so it was
also a good opportunity to write bindings (something I had dodged for a long
time for no particular reason).

As of June 2025, there is no OCaml bindings for the [Vosk
API](https://github.com/alphacep/vosk-api/blob/master/src/vosk_api.h), so my
first task was to write my own as part of a project soberly called
[`ocaml-vosk`](https://github.com/lthms/ocaml-vosk).

Gemini Flash was able to help me understand how `ctypes` and `ctypes.foreign`
works. This was my first experience interacting with an LLM from my Neovim
window, and it was pretty convincing. It gave me the opportunity to learn that
one can declare opaque types in OCaml (not just via mli files). It makes sense,
but it was news to me.

Then, Gemini suggested me to use [EIO’s
`Switch`{.ocaml}](https://ocaml-multicore.github.io/eio/eio/Eio/Switch/index.html)
to deal with automatic memory management (in place of `Gc.finalise`). It was
the first time I heard about it, and the fact that I learned their existence
from the perspective of resource management (not fiber management) was a good
accident.

The first point of friction came when I started build a high-level interface
for my Vosk bindings. More specifically, given a
[`Cstruct.t`](https://ocaml.org/p/cstruct/latest) value, how do I get a pointer
and a length? It turns out that while both ChatGPT and Gemini Pro know how to
do so, Gemini Flash hallucinates every step of the way.

The solution is actually pretty straightforward.

```ocaml
let ptr =
  Ctypes.bigarray_start
    Ctypes.array1
    (Cstruct.to_bigarray buffer)
in
let len = buffer.Cstruct.len in
```

Gemini Flash kept suggesting I use `Ctypes.ptr_add` instead, though. Don’t
search for it, it does not exist[^gpt]. When I suggested `Cstruct.to_bigarray`,
it warned me about the fact that this call would create a copy of the
underlying buffer. ChatGPT and Gemini Pro disagreed, and I could convince
myself that they were right by looking at the code. Interestingly, I was also
able to convince Gemini Flash it was wrong by copy/pasting the relevant code
snippet.

[^gpt]: While reviewing this article, ChatGPT gently hinted that while
    `ptr_add` does not exist, `Ctypes.(+@)`{.ocaml} does.

> [!TIP]
> Having an LLM suggesting you to use a function which does not exist is *very*
> frustrating. Especially if it happens several times in a row—it recognizes
> its mistake and proposes an alternative that is as nonexistant as the first
> one. At least, with LSP it is pretty straightforward to know when it happens.

Using Vosk is one thing, but then I couldn’t find any OCaml package to read
audio files compatible with Vosk expectations. Implementing what I needed in
OCaml gave me more opportunities to learn about EIO, but most importantly, it
showed how having a chat with an LLM directly from my editor was convenient. I
was able to learn about WAV files, RIFF header and subchunks and PCB 16-bit
mono audio data without leaving Neovim. And by giving Gemini access to my
buffer, I troubleshot most of my issues fairly quickly (except when they were
EIO-specific—more on that later).

> [!TIP]
> For widespread encoding like WAV files, LLMs shine particularly bright.

In the end, EIO-specific code put aside, this task was roughly solved by (1)
writing bindings for the few functions of the Vosk API I needed, and (2)
translating C examples provided by Gemini into good-looking OCaml[^switch].

Witnessing my example program outputting the transcript of audio files as it
was processing them felt pretty good, and I was soon ready to tackle the second
part of this project: prompting a LLM to summarize it.

[^switch]: It’s a little out of scope for this article, but I discovered when
    writing the high-level API for Vosk that `Switch`{.ocaml}es are very easy
    to misuse. It is as simple as (incorrectly) turning an eager function
    consuming a buffer into a `Seq`-based alternative, while forgetting the use
    of `Switch.run` on top of the function.

## Prompting Local LLMs with Ollama

Similarly to Vosk, there is no on the shelf package available to use Ollama
from an OCaml program. As a consequence, I created a second repository
([`ocaml-ollama`](https://github.com/lthms/ocaml-ollama) if you can believe it).

### How It Started

Turns out, you don’t use Ollama the same way you use Vosk. The latter is a C
library that you can call from your binary, the former actually uses a
client/server architecture. I asked LLMs what was the best solution for
performing HTTP requests with Eio, and `cohttp-eio` came back as a good
candidate. I’m already familiar with `cohttp`, since we are using it at
`$WORK`{.bash}, but it’s actually a transitive dependency (of a framework
called [`resto`](https://ocaml.org/p/resto/latest)).

I am actually a little frustrated with `resto`, so I welcomed the opportunity
to familiar myself a little more with `cohttp` directly. I quickly implemented
the helper fetching the list of models available from a given Ollama instance.

Then, I got myself side tracked.

### More LLMs Lies

Persistent HTTP connections are a pet peeve of mine. Establishing a TCP
connection, negotiating TLS encryption, all of that takes time—creating a new
socket for each request a daemon really frustrates me as a result.

So I asked.

> Does `cohttp-eio` reuses already established connections when performing two
> requests on the same host?

ChatGPT 4o. Gemini 2.5 Flash. Gemini 2.5 Pro. They all assured me it was the
case, as long as I was careful and reused the same
`Cohttp_eio.Client.t`{.ocaml} instance. For instance, here is the first few
words of ChatGPT when prompted with this question.

> As of current behavior in `cohttp-eio-client`, **yes**, it does **reuse
> already established connections** when making multiple requests to the same
> host, provided certain conditions are met.

It’s a lie. Don’t trust them. They don’t reuse existing HTTP connection.

I was very doubtful, so I asked them how to check this. `tcpdump` was
mentioned[^trace]. I got traces I couldn’t read at first glance, so I just
copy/pasted them to the LLMs… and sure enough, they confirmed what I suspected.
`Cohttp_eio.Client`{.ocaml} does not share connections by default. It creates a
socket for each request.

[^trace]: I later discovered [`eio-trace`](https://github.com/ocaml-multicore/eio-trace)
    and it would have been much more straightforward to use this tool to
    inspect `Cohttp_eio.Client`{.ocaml}’s default behavior. No LLM thought of
    that, sadly.

It’s actually pretty easy to convince yourself that it is the case by reading
the implementation of
[`Cohttp_eio.Client`{.ocaml}](https://github.com/mirage/ocaml-cohttp/blob/main/cohttp-eio/src/client.ml#L83).

```ocaml
type connection = Eio.Flow.two_way_ty r
type t = sw:Switch.t -> Uri.t -> connection

(* simplified version of [make], omitting the support for HTTPS *)
let make () net : t = fun ~sw uri ->
  (Eio.Net.connect ~sw net (unix_address uri) :> connection)
```

There is *nothing* here dealing with persistent connections. `Eio.Net.connect`
uses a switch for resource management, but does not perform any kind of
connection caching.

That’s okay, though. Yak shaving is a real thing. I can stop working on my
Ollama client library for a while, just to *fix this*.

### The Questionable Side Quest of Implementing a Connection Pool for `cohttp-eio`

The bottom-line of this little adventure is: I should have updated my default
prompt to remind the LLMs that `Cohttp_eio.Body.drain`{.ocaml} in *not* a thing.

But let’s start from the beginning. Over the course of a few days, I have
successfully implemented a wrapper on top of `Cohttp_eio.Client`{.ocaml} to
deal with persistent connections. It’s not rocket science, but it’s still a
subtle endeavor, which necessitated a good understanding of Eio and `cohttp`. I
cannot say LLMs were instrumental for the task. They gave me good pointers to
start from, but they also misled me a bunch of times.

Sometimes, the help came in surprising ways. One anecdote in particular
stuck with me. I decided I needed a `get`{.ocaml} operation for
[`Eio.Pool`{.ocaml}](https://ocaml-multicore.github.io/eio/eio/Eio/Pool/index.html)
pools, which sadly only proposes `use`.

```ocaml
(* Provided by Eio.Pool *)
val use : 'a t -> ('a -> 'b) -> 'b

(* Not provided *)
val get : sw:Switch.t -> 'a t -> 'a
```

The key insight is that `get` allows callers to pick something from the pool,
and only put it back when the switch is released.

My first implementation of `get` was roughly as follows[^forget].

[^forget]: I didn’t even consider asking an LLM to propose me an implementation,
    now that I think about it. I really am no vibe coder yet.

```ocaml
open Eio.Std

let get ~sw t =
  let x, rx = Promise.create () in
  let never, _ = Promise.create () in
  Fiber.fork ~sw (fun () ->
      Eio.Pool.use t @@ fun conn ->
      Promise.resolve rx conn;
      Promise.await never);
  Promise.await x
```

And it didn’t work. The resulting program was hanging, because of how
`Fiber.fork ~sw`{.ocaml} works. Basically, the fiber created by `fork` becomes
part of the set of fibers the switch `sw` waits for. Since, in my case, said
fiber would never be resolved, I had created a deadlock.

I asked Gemini Pro 2.5 for help, and out of curiosity, I looked at its
reasoning steps. Very early on, it mentioned `Fiber.fork_daemon`, but
surprisingly `Fiber.fork_daemon` was not mentioned in the final answer[^bias].
Have I not been curious at that time, I would have missed the correct
solution[^alice].

[^alice]: [@alice](https://bsky.app/@welltypedwit.ch) provided me the answer a
    few minutes later, so I’d have been fine in the end 😅.

[^bias]: Once again, I had asked the wrong question. I asked for the `Fiber`
    equivalent of `Lwt.async`. I had overlooked that `Lwt.async` had a very
    particular behavior wrt. exceptions, that Gemini Pro tried very hard to
    replicate. I didn’t care at all about the exceptions I could raise, here!

I think my experience overall was made a little more frustrating than it should
have been because I have never constructed a “context” that I could share
between coding sessions. I haven’t enabled the memory saving setting in
ChatGPT. Besides, everytime I opened Neovim, Gemini was starting from scratch.
I should try to change that, to prevent the LLMs from doing the same mistakes
again and again—typically, the `Cohttp_eio.Body.drain` function they kept
bringing up.

> [!TIP]
> I need to investigate how I can specialize my default prompt for each
> software project I am working on. I imagine I can rely on an environment
> variable and [`direnv`](https://direnv.net/).

Finally, it’s when I worked on this library that I came up with a nice prompt
for Gemini to write my git commit messages for me.

> `@editor` `#buffer` Add a git commit title and message. Structure the
> description in three sections (What, Why, How). Wrap the sections at 72
> columns. Don’t forget the git title, and always insert a new line between the
> title and the description.

This prompt gives pretty cool result. It is still necessary to review it,
because in a few instances I caught false statement in the proposal. But
overall, it gives really meaningful output. Almost [all commits of the
library](https://github.com/lthms/cohttp-connpool-eio/commits/main/) have been
written with this prompt.

> [!TIP]
> If anything, I don’t think I will never open a Merge Request with an empty
> description ever again.

And that, kids, is how I released
[`cohttp-connpool-eio.0.1`](https://github.com/lthms/cohttp-connpool-eio).

### Wrapping-up a Minimal Ollama Chat

Integrating `cohttp-connpool-eio` in my `ocaml-ollama` project led me to find a
bug in the former. More specifically, the `Cohttp_connpool_eio.warm`{.ocaml}
function that can be used to pre-populate a new pool was doing so by performing
a specified `HEAD` request to the host as many time as the pool size[^change].

[^change]: In a later iteration of the library, `warm` only establishes
    connections, and does not perform any unnecessary HTTP requests.

It worked well against both `https://www.google.com` and
`https://soap.coffee/~lthms`, but when I tried with the Ollama server, it
decided to hang. Why?

Well, I tried asking my new friends the LLMs, but didn’t get any answer I felt
confident with. At this point, my trust in their EIO expertise was rather low,
and I was more skimming through their answer to find a lead I would follow
myself than anything else. In the end, I completely dropped the LLMs here, and
went back to what I usually do: experimenting, and reading code.

I reproduced the issue with `curl`: `curl -X HEAD` hangs as well with Ollama,
while `curl --head` does not. The former tries to read the response body, based
on the response headers (*e.g.*, `content-length`). The latter doesn’t, because
it knows `HEAD` always omits the body. I am not sure *why*  the hanging
behavior does not show for `curl -X HEAD https://www.google.com`, though.

But anyway, once the bug was fixed, I could return to playing with Ollama.

I then decided to implement a helper to call [`POST
/api/generate`](https://github.com/ollama/ollama/blob/main/docs/api.md#generate-a-completion).
It is the simplest way with Ollama to generate an LLM’s answer from a prompt.
Interestingly enough, it is a “streamed” RPC using the `application/x-ndjson`
content type. Instead of computing the answer *before* sending it to the
client, the server instead sends JSON-encoded chunks ([`transfer-encoding:
chunked`](https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Transfer-Encoding#chunked)).

I tried to implement that with `cohttp-eio`, and it failed miserably with
obscure parsing error messages.

After a bit of debugging, it became clear that `Eio.Buf_read.parse`{.ocaml} was
not behaving as I thought it was, which made me feel paranoid about how
`cohttp-connpool-eio` handles connection releases. In the end, I had to unpack
how the `Cohttp_eio.Body.t`{.ocaml} work under the hood wrt.
`End_of_file`{.ocaml} to move on. Once again, my LLM friends weren’t
particularly helpful: they were hallucinating `Buf_read` functions, and never
considered to mention that `parse` only works for complete response.

> [!TIP]
> My personal conclusion is that ChatGPT and Gemini quickly show their limits
> for non-trivial programming task involving Eio and its ecosystem.
> I am really curious to understand why. Do they keep hallucinating functions
> because Eio is a really generic name, and maybe they are mixing context from
> the Python library with the OCaml one? Or is it because the API of Eio has
> changed a lot over the years?
>
> I am also wondering how, as a the author of a library, I can fix a similar
> situation. Assuming ChatGPT starts assuming false statements about
> `cohttp-connpool-eio` for instance, how do I address this? I suspect being
> “LLMs-friendly” will be increasingly important for a software library’s
> success.

In the end, ChatGPT and Gemini were just another source of inputs, not the main
driver of my development process.

## Putting Everything Together

Turns out, you really need just one RPC to generate a summary for a text input,
so it wasn’t long before I could chain everything. I pulled
`mistral:7b-instruct-v0.2-q4_K_M` (over a suggestion by ChatGPT, if I remember
correctly), and got a summary from the video I had downloaded.

Just kidding. Out of nowhere, I decided to pursue yet another side quest, and
gave a try to the fancy [`dune pkg
lock`](https://dune.readthedocs.io/en/stable/tutorials/dune-package-management/dependencies.html)
command. *Then* I was able to [generate my
summary](/files/RhinocerosSummary.html), using the following prompt.

```
Generate a summary of the raw transcript of a video provided after
this paragraph. The transcript may be in a language that is not
English, but the summary should always be in English. You should
adopt a neutral point of view (i.e., even if the transcript speaks
in the first person, you should always use the third person). Each
line is an utterance. Keep the summary short and engaging, your
goal is to provide a good overview of what was said.

----

{Vosk output}
```

And with this, it was time to wrap-up. And what better way to do so than to
write this little journal entry? So I did, and when I was half way through my
first draft, I fired a new chat buffer to ask for advice from my new friend
Gemini Flash.

> #buffer Here is a very preliminary, incomplete draft of a blogpost. Can you try to
> anticipate if it will find an audience?

It wasn’t long before Gemini turned me down.

> My apologies, but I cannot anticipate whether this blog post will find an
> audience. My capabilities are focused on programming-related tasks like code
> explanation, review, generation, and tool execution within the Neovim
> environment.
>
> Let me know if you have any questions about the code itself, or need
> assistance with Neovim.

🥲[^ouf].

[^ouf]: Fortunately, ChatGPT was less opinionated.

## Final Words

Although I had already used ChatGPT and other models in the past, this was the
first time I tried to make them a central part of my workflow. I learned a lot
during this experiment, and I now have an integrated setup I enjoy using.

I need to keep digging. Try more models (there are a lot of those now). And get
better at writing good prompts which do not lead the LLMs astray. They are here
to stay, after all. I better learn how to take the most from them.
