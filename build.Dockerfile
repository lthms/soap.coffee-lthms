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
ENTRYPOINT ["/bin/soap.coffee"]
