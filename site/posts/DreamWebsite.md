---
published: 2024-12-25
modified: 2024-12-27
tags: [ocaml, meta]
abstract: |
    This article is a kind of experience report of writing an HTTP server
    serving my website directly from memory, no file system involved. Just keep
    in mind: I am pretty that you should not try to reproduce this for your own
    little corner of the Internet, but I had a lot of fun.
---

# Serving This Article from RAM for Fun and No Real Benefit

In 2022, Xe Iaso published a [transcript of their talk on how their website was
working at the time][xeiaso]. In a nutshell, their approach consisted of a
server preprocessing the website from its source at startup, then serving its
contents from memory. If you have not already, I can only encourage you to read
the article or watch the talk, as the story they tell is very interesting. For
me personally, it sparked a question: what if, instead of preprocessing the
website at startup, one decided to embed the already preprocessed website
within the program of the HTTP server tasked to serve it?

Fast-forward today, and this question has finally been answered. The webpage
you are currently reading has been served to you by an ad hoc HTTP server built
with [Dream], whose binary is the only file I need to push to my server to
deploy the latest version of my website. I have actually deployed it, and it’s
been serving the contents of this website for more than a week now.

What did I learn from this fun, little experiment? Basically, that this
approach changes nothing, as far as [Lighthouse] and my monitoring is
concerned. I couldn’t find any meaningful differences between a static website
served by Nginx, a piece of software with thousands and thousands of
engineering work behind it, and my little toy web server pieced together in an
hour or so. Still. It was fun, so why not write about it?

This article is a kind of experience report. I’ll dive into what I have done to
turn my website into a single, static binary. Not only does it mean writing
some OCaml, which is always fun, but it also requires understanding a little
some key HTTP headers, as well as using Docker to build easily deployable
binaries. All in all, I hope it will be an interesting read for the curious
minds.

## Embedding My Website in a Binary

Not much had changed much since [I stopped using **`cleopatra`** to generate
this website][august2022], and [the article I published in 2023 still
stands][thanks]. In a nutshell, I work in the `site/` directory, and [soupault]
generates my website in the `out/~lthms` directory, thanks to a collection of
built-in and ad hoc plugins[^footnotes]. To deploy the website, I was relying
on `rsync` to sync the contents of the `out/~lthms` directory with the
directory statically served by a Nginx instance on my personal server.

[^footnotes]: For instance, Markdown footnotes are turned into side notes with
    a soupault plugin.

The first step of my little toy project is to actually embed the output of
soupault into an OCaml program.

That’s where [ocaml-crunch] comes in handy. It is a [MirageOS] project, whose
only job is to generate an OCaml module from a file system directory. It is
straightforward to use it from Dune.

```lisp
; file: out/dune
(rule
 (target website_content.ml)
 (deps (source_tree ~lthms))
 (action
  (run ocaml-crunch -m plain -o %{target} -s ~lthms)))
```

This snippet generates the `website_content.ml` module, which we can then
expose through a library with the `library` stanza.

```lisp
; file: out/dune
(library
 (name website_content))
```

And we are basically done. Excluding an `Internal` module, the signature of
`Website_content` is pretty straightforward.

```ocaml
val file_list : string list
val read : string -> string option
val hash : string -> string option
val size : string -> int option
```

## Serving the content with Dream

[Dream] is a cool project, and provides a straightforward API that we can
leverage to turn our list of in-memory files into an HTTP server.

### Naive Approach

Our goal now is to create a `Dream.handler` for each item in
`file_list`{.ocaml}. Done naively (as was my first attempt), it gives you
something of the form:

```ocaml
let make_handler ~content path =
  Dream.get path (fun req ->
    Lwt.return (Dream.response content)))
```

Which we can use to build the main route we will then pass to `Dream.router`.

```ocaml
let website_route =
  Dream.scope "~lthms" []
  @@ List.map
       (fun path ->
         let content = Option.get (Website_content.read path) in
         make_handler ~content path)
       Website_content.file_list
```

With this approach, we build our handlers once, and then the lookup is done by
Dream’s router. It could be an interesting experiment to see if doing the
lookup ourselves is more performant (since Dream’s router is very generic,
while in our case we don’t really need to parse anything). I remember Xe
routing is basically going through a linked list, which seems strange at first,
but works very well in practice because they have ordered said list with the
most recent articles up front, and everybody comes to their website to read the
latest article anyway.

It does not take an extensive QA process to figure out that this approach
is far from being enough. To name a few things:

- My website assumes `http://path/index.html` can be accessed with
  `http://path/` or `http://path`. Our little snippet does not handle this.
- Browsers expect the `Content-Type` headers to be correctly set. To give an
  example, they won't load a CSS file if the `Content-Type` header is not set
  to `text/css`.
- Browsers work best for websites that take the time to provide caching
  directives. Our little snippet does not care to do so.
- Even if my website is rather lightweight[^mbytes], compressing the response
  of our HTTP server for clients that support it is always a good idea.

[^mbytes]: 20MBytes at the time of writing the first version of this article.

This is a gentle reminder of all the things Nginx can do for you with very
little configuration.

### Handling `index.html` Synonyms

This one is rather simple. For files named `index.html`, we need 3 handers, not
just one. We can achieve this with an additional helper
`make_handler_remove_suffix`.

```ocaml
let make_handler_remove_suffix ~content path suffix
    =
  if String.ends_with ~suffix path then
    let alt_path =
      String.sub path 0 (String.length path - String.length suffix)
    in
    [ make_handler ~content alt_path ]
  else []
```

Updating the `website_route` definition to use `make_handler_remove_suffix` is
quite easy as well.

```patch
 let website_route =
   Dream.scope "~lthms" []
-  @@ List.map
+  @@ List.concat_map
        (fun path ->
          let content = Option.get (Website_content.read path) in
-         make_handler ~content path)
+         if path = "index.html" then
+           (* Special case to deal with "index.html" which needs to be
+              recognized by the route "/" *)
+           [
+             make_handler ~content "/";
+             make_handler ~content "";
+             make_handler ~content "index.html";
+           ]
+         else
+           make_handler_remove_suffix ~content path
+             "/index.html"
+           @ make_handler_remove_suffix ~content
+               path "index.html"
+           @ [ make_handler ~content path ])
        Website_content.file_list
```

With that, `https://soap.coffee/~lthms/posts/index.html` returns the same pages
as `https://soap.coffee/~lthms/posts` or `https://soap.coffee/~lthms/posts`.
Check.

### Supporting `Content-Type`

`Content-Type` is an HTTP header which is used by the receiver of the HTTP
message (whether it is a request or a response) to interpret its content.

For instance, when building a RPC API, `Content-Type` is used by the server to
know how to parse the request body (`Content-Type: application/json`{.http} or
`Content-Type: application/octet-stream`{.http} being two popular choices, for
JSON or binary encoding, respectively).

In our case, the `Content-Type` header is used by the HTTP server to
communicate the nature of the content to browsers. For my website, I can just
use the file extensions to infer the correct header to set. First, we list the
extensions that are actually used.

```ocaml
let content_types =
  [
    (".html", "text/html");
    (".css", "text/css");
    (".xml", "text/xml");
    (".png", "image/png");
    (".svg", "image/svg+xml");
    (".gz", "application/gzip");
    (".pub", "text/plain");
  ]
```

A header in Dream is encoded as a `string * string`{.ocaml} value, with the
first `string`{.ocaml} being the header name and the second being the header
value.

```ocaml
let content_type_header path =
  List.filter_map
    (fun (ext, content_type) ->
      if String.ends_with ~suffix:ext path then
        Some ("Content-Type", content_type)
      else None)
    content_types
  |> assert_f
       ~error_msg:Format.(sprintf "Unsupported file type %s" path)
       (( <> ) [])
```

with `assert_f`{.ocaml} being defined as follows.

```ocaml
let assert_f ~error_msg f v =
  if f v then v else failwith error_msg
```

`assert_f`{.ocaml} is used to enforce that I don’t deploy a website which
contains route lacking a `Content-Type` header. For instance, if I remove the
`"html"`{.ocaml} entry of the `content_type`{.ocaml} list, I get this error
when I try to execute the server.

```
Fatal error: exception Failure("Unsupported file type index.html")
```

This is because the headers are only computed once, when each `route` are
defined. This is a key principle of this project: compute once, serve many
time[^compile].

[^compile]: I would love to get a compilation error instead (considering there
    are no runtime values involved), but have not looked into this just yet.

```patch
 let website_route =
   Dream.scope "~lthms" []
   @@ List.concat_map
        (fun path ->
          let content = Option.get (Website_content.read path) in
+         let headers = content_type_header path in
          if path = "index.html" then
            (* Special case to deal with "index.html" which needs to be
               recognized by the route "/" *)
            [
-             make_handler ~content "/";
-             make_handler ~content "";
-             make_handler ~content "index.html";
+             make_handler ~headers ~content "/";
+             make_handler ~headers ~content "";
+             make_handler ~headers ~content "index.html";
            ]
          else
-           make_handler_remove_suffix ~content path
+           make_handler_remove_suffix ~headers ~content path
              "/index.html"
-           @ make_handler_remove_suffix ~content
+           @ make_handler_remove_suffix ~headers ~content
                path "index.html"
-           @ [ make_handler ~content path ])
+           @ [ make_handler ~headers ~content path ])
        Website_content.file_list
```

(The changes in `make_handler` and `make_handler_remove_prefix` are left as an
exercise to enthusiast readers)

### Compressing if Requested

Nowadays, computations are cheap, while downloading data costs time (and
sometimes money). As a consequence, it is often a good idea for a server to
compress a large HTTP response, and browsers do ask them to do so, by setting
the [`Accept-Encoding`{.http}][encoding] header of their requests.

The value of the `Accept-Encoding`{.http} header is a comma-separated list of
supported compression algorithms, optionally ordered with a priority value `q`.

For instance, `Accept-Encoding: gzip;q=0.5, deflate;q=0.3, identity`{.http}
tells you that the browser supports three encoding methods: `gzip`, `deflate`
and `identity` (no compression), and the browser prefers `gzip` over `deflate`.
Besides, the request can provide several `Accept-Encoding` headers instead of
just one, so we can have 

```http
Accept-Encoding: gzip;q=0.5
Accept-Encoding: deflate;q=0.3
Accept-Encoding: identity
```

The `String` module provides everything we need to check if a browser
supports gzip as an encoding method[^spoiler].

```ocaml
(* For [method(; q=val)?], returns [method], except if
   [q=0]. *)
let to_directive str =
  match String.split_on_char ';' str |> List.map String.trim with
  | [ x ] -> Some x
  | [ x; y ] -> (
      match String.split_on_char '=' y |> List.map String.trim with
      | [ "q"; "0" ] -> None
      | [ "q"; _ ] -> Some x
      | _ -> None)
  | _ -> None

(* [contains ~value:v header] returns [true] if [v] is a
   supported method listed in [header]. *)
let contains ~value header =
  String.split_on_char ',' header
  |> List.to_seq |> Seq.map String.trim
  |> Seq.filter_map to_directive
  |> Seq.exists (( = ) value)
```

[^spoiler]: Spoiler: they do. I was even wondering at some point if I could
    just _always_ return GZIP-compressed values, ignoring the
    `Accept-Encoding`{.http} header altogether. If you do that, though, `curl`
    becomes annoying to use (it does not uncompress the response automatically,
    and instead complains about being about to write binary to the standard
    output).


We use `contains`{.ocaml} to tell us if we can return a compressed response,
which leaves us with one final question: how to compress said response?

The OCaml ecosystem seems to have picked [camlzip] library when GZIP is
involved[^docs]. What is surprising with this library is that it does not
support in-memory compression: the functions expect channels, not
`bytes`{.ocaml}. That is quite annoying, because we are specifically doing this
**not** to use files.

[^docs]: You know it is a legitimate OCaml library when one of the top-level
    modules [is not documented at all][docs].

The Internet is helpful here, and quickly suggests using pipes. It works when
you remember –or figure out– that pipes are a blocking mechanism: one does not
just write a buffer of arbitrary size in a pipe, because after something like
4KBytes, writing becomes blocking until a read happens to free some space.
That’s not a big problem: we can read and write concurrently to the pipe using
threads, and OCaml 5 makes it quite easy to do so with the `Domain`{.ocaml}
module.

```ocaml
let gzip content =
  let inc, ouc = Unix.pipe () in
  let ouc = Gzip.open_out_chan ~level:6 Unix.(out_channel_of_descr ouc) in
  let _writer =
    Domain.spawn (fun () ->
        Gzip.output_substring ouc content 0 String.(length content);
        Gzip.close_out ouc)
  in
  let res = In_channel.input_all Unix.(in_channel_of_descr inc) in
  Unix.close inc;
  res
```

> [!CAUTION]
> As rightfully [pointed out][discuss] by [Daniel Bünzli][dbuenzli], the `gzip`
> function presented in this article is full of shortcomings. To quote the
> message, _the function can leak fds in case of errors and domains are not
> meant to be used that way (it’s rather spawn one long running domain per CPU
> you have). It’s not necessarily more complicated to correct it to use
> Fun.protect invocations to make sure all your fds get closed even if the
> function blows up and use Thread.create so that the netizens cut and paste
> correct code._
>
> In my opinion, this implementation is “good enough” for my use case, which is
> compressing arbitrary strings before the HTTP server is even started. If it
> were to be called in the handlers themselves, then definitely, it would not
> be suitable.
>
> Keep that in mind if you want to borrow this code.

We know how to decide whether to compress or not, and how to compress. The next
step is to modify `make_handler` accordingly.

```patch
-let make_handler ~headers ~content path =
+let make_handler ~headers ~gzip_content ~content path =
+  let gzip_headers = ("Content-Encoding", "gzip") :: headers in
   Dream.get path (fun req ->
-    Lwt.return (Dream.response content)))
+      match Dream.headers req "Accept-Encoding" with
+      | accepted_encodings
+        when List.exists (contains ~value:"gzip") accepted_encodings ->
+          Lwt.return @@ Dream.response ~headers:gzip_headers gzip_content
+      | _ -> Lwt.return @@ Dream.response ~headers content)
```

`gzip_content` is computed only once (using our `gzip` function), and passed to
`make_handler`. This way, the only computation the handler needs to do is to
“parse” `Accept-Encoding`.

### Caching

Compressing a page to reduce the number of bytes a browser needs to download is
fine. Letting the browser know it does not need to download anything because
it's previous version is still accurate is better.

This is achieved through two complementary mechanisms: [entity tags][etag]
(`ETag`{.http})[^cookies], and [cache policies] (`Cache-Control`{.http}).

[^cookies]: My first encounter with entity tags was around the time GDPR was a
    hot topic, because you can use them as a cheap replacement for cookies to
    [track your users][tracking]. I remained at the surface level at the time,
    it was fun learning more about them through this little project.

Entity tags are used to identify a resource, and are expected to change
every time the resource is updated. The general workflow goes like this: the
first time a browser requests `https://soap.coffee/~lthms/index.html`, it
caches the result along with the value of the `ETag`{.http} header. The next
time it needs the page, it adds the header `If-None-Match`{.http}, with the
ETag as its value. For such requests, the server is expected to return an empty
response with HTTP code 304 (_Not Modified_).

I decided to use the sha256 hash algorithm to compute the entity tag of each
resource of my website. The [sha] OCaml library looked like a good enough
candidate.

```ocaml
(* in `website_route` *)
let etag = Sha256.(string content |> to_hex) in
```

Interestingly, one question I had to answer was whether the entity tag of a
page needed to be different whether it was compressed or not. Internet almost
unanimously answered yes. So be it. We just need to keep in mind ETag values
are expected to be surrounded by quotes, and we are good to go. It is just a
matter of suffixing the ETag with `+gzip` in the compressed case.

```patch
-let make_handler ~headers ~gzip_content ~content path =
-  let gzip_headers = ("Content-Encoding", "gzip") :: headers in
+let make_handler ~headers ~etag ~gzip_content ~content path =
+  let etag_gzip = Format.sprintf "\"%s+gzip\"" etag in
+  let etag = Format.sprintf "\"%s\"" etag in
+  let gzip_headers =
+    ("Content-Encoding", "gzip") :: ("ETag", etag_gzip) :: headers in
+  let identity_headers = ("ETag", etag) :: headers in
   Dream.get path (fun req ->
-      match Dream.headers req "Accept-Encoding" with
-      | accepted_encodings
-        when List.exists (contains ~value:"gzip") accepted_encodings ->
-          Lwt.return @@ Dream.response ~headers:gzip_headers gzip_content
-      | _ -> Lwt.return @@ Dream.response ~headers content)
+      match Dream.headers req "If-None-Match" with
+      | [ previous_etag ] when previous_etag = etag || previous_etag = etag_gzip
+        ->
+          Lwt.return
+          @@ Dream.response
+               ~headers:(("ETag", previous_etag) :: headers)
+               ~code:304 ""
+      | _ -> (
+          match Dream.headers req "Accept-Encoding" with
+          | accepted_encodings
+            when List.exists (contains ~value:"gzip") accepted_encodings ->
+              Lwt.return @@ Dream.response ~headers:gzip_headers gzip_content
+          | _ -> Lwt.return @@ Dream.response ~headers:identity_headers content))
```

Entity tags are useful, but you still need the browser to make an HTTP request
every single time you visit the website. By setting a cache policy, we can
remove even remove the need for this request most of the time. The
`Cache-Control`{.http} header is used to set a number of parameters, including
the `max-age` value (in seconds).

In my Nginx configuration, I had set `max-age` to a year for images. I did
the same thing here. Besides, I decided to set `max-age` for other resources
to 5 minutes. This seems like a good compromise: since my website does not
change very often, it is very unlikely that you happen to visit it when I
publish new content. Setting a 5-minute cache policy should let my readers
download each resource only once, yet get the freshest version at their next
visit[^nocode].

[^nocode]: Dealing with the `Cache-Control`{.http} header is basically the same
    exercise as setting the correct `Content-Type`{.http} header, and this
    article is already long enough, which is why there is no diff or snippet in
    this section.

And with this, we are done. We get a standalone library to server our website
in a browser-friendly manner, which I can theoretically use to replace my
current Nginx-powered setup. Although… is it _that_ simple?

## Building and Deploying the Website

Files are quite easy to share and deploy. As I mentioned earlier in this
article, you just need to `rsync`{.bash} them and be done with it. _Binaries_,
on the other hand… One cannot just assume a binary build on a machine X will
work on another machine Y. Some additional works need to be done.

The most straightforward solution I know is to rely on static binaries. [I have
already written about how to generate static binaries for OCaml
projects][static], so I had a pretty strong head start, but one drawback of the
approach I’ve described there (and that I have been using for [Spatial Shell’s
releases][releases][^few]) is that it is rather slow (I have a script creating
a new local switch each time) and requires static libraries to be installed
(which Arch Linux does not provide).

[^few]: Not that there were many of them lately.

And so, I figured, why not build the static binary in Docker? This allows me to
use Alpine to get a static version of my system dependencies, and can be quite
fast thanks to [Docker build cache][docker]. The Dockerfile is quite simple:
one stage for building the system and OCaml dependencies, and one stage for
building the static binary.

```dockerfile
FROM alpine:3.21 AS build_environment

# Use alpine /bin/ash and set shell options
# See https://docs.docker.com/build/building/best-practices/#using-pipes
SHELL ["/bin/ash", "-euo", "pipefail", "-c"]

USER root
WORKDIR /root

RUN apk add autoconf automake bash build-base ca-certificates opam gcc \ 
  git rsync gmp-dev libev-dev openssl-libs-static pkgconf zlib-static \
  openssl-dev zlib-dev
RUN opam init --bare --yes --disable-sandboxing
COPY makefile dune-project .
RUN make _opam/.init OCAML="ocaml-option-static,ocaml-option-no-compression,ocaml.5.2.1"
RUN eval $(opam env) && make server-deps

FROM build_environment AS builder

COPY server ./server
COPY out ./out
COPY dune .
RUN eval $(opam env) && dune build server/main.exe --profile=static

FROM alpine:3.21 AS soap.coffee

COPY --from=builder /root/_build/default/server/main.exe /bin/soap.coffee
```

Then, building my static binary becomes as simple as:

```bash
docker build . -f ./build.Dockerfile \
  --target soap.coffee \
  -t soap.coffee:latest
docker create --name soap-coffee-build soap.coffee:latest
docker cp soap-coffee-build:/bin/soap.coffee .
docker rm -f soap-coffee-build
```

`docker cp`{.bash} does not work on an image, but on a container, so we need to
create one which can be destroyed shortly after.

This little binary weights 38MBytes, which seems relatively reasonable to me,
considering my website weights 20MBytes. I guess it could be easy to reduce
this size by embedding the compressed version of my articles and images,
instead of the uncompressed one. But really, for my website, I’m not really
interested in investing the extra effort.

## Conclusion

I would not recommend anyone to use this in production for anything remotely
important, but from my perspective, it was both fun and insightful. I was able
to refresh my memories about HTTP “internal,” among other things. Again, as
far as I can tell, deploying my website this way did not bring me any benefit,
performance-wise; even worse, I am pretty sure the Dream server will not behave
as well as Nginx when it comes to handling the load (since it is limited to one
core, instead of several with Nginx).

That being said, I am way too invested now… which is why, yes, you are
reading a blog post served to you directly from memory 🎉.

[xeiaso]: https://xeiaso.net/talks/how-my-website-works/
[august2022]: August2022.html
[thanks]: Thanks2023.html
[soupault]: https://soupault.app
[Dream]: https://aantron.github.io/dream/
[Lighthouse]: https://chromewebstore.google.com/detail/lighthouse/blipmdconlkpinefehnmjammfjpmpbjk?pli=1
[ocaml-crunch]: https://github.com/mirage/ocaml-crunch
[MirageOS]: https://mirage.io/
[encoding]: https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Accept-Encoding
[camlzip]: https://ocaml.org/p/camlzip/latest
[docs]: https://ocaml.org/p/camlzip/latest/doc/Zlib/index.html
[etag]: https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/ETag
[tracking]: https://levelup.gitconnected.com/no-cookies-no-problem-using-etags-for-user-tracking-3e745544176b
[cache policies]: https://developer.mozilla.org/fr/docs/Web/HTTP/Headers/Cache-Control
[sha]: https://ocaml.org/p/sha/latest
[static]: OCamlStaticBinaries.html
[releases]: https://github.com/lthms/spatial-shell/releases
[docker]: https://docs.docker.com/build/cache/
[dbuenzli]: https://erratique.ch/contact.en
[discuss]: https://discuss.ocaml.org/t/serving-this-article-from-ram-with-dream-for-fun-and-no-real-benefit/15856/6?u=lthms
