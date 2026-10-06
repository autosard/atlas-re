# Build stage: compiles atlas-re from the given refs (branches or tags) of
# the tool and example repositories.
FROM alpine:3.23 AS build
ARG ATLAS_REF=jar
ARG EXAMPLES_REF=atlas-revisited
RUN apk add --no-cache build-base git curl ncurses gmp-dev z3-dev
WORKDIR /build
RUN git clone --depth 1 -b ${ATLAS_REF} https://github.com/autosard/atlas-re.git
RUN git clone --depth 1 -b ${EXAMPLES_REF} https://github.com/autosard/atlas-examples.git
# haskell-z3 411.0.1 (the version on Hackage is outdated), pinned for reproducibility
RUN git clone https://github.com/IagoAbal/haskell-z3 \
 && git -C haskell-z3 checkout --quiet b77a17e5eeb7db82656bcbcd66c6e952207e69ca
# atlas-re requires GHC 9.6 (base 4.18), ghcup installs a newer one by default
ENV BOOTSTRAP_HASKELL_NONINTERACTIVE=1 BOOTSTRAP_HASKELL_GHC_VERSION=9.6.7
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ENV PATH="$PATH:/root/.ghcup/bin"
WORKDIR /build/atlas-re
RUN cabal install exe:atlas-re

FROM alpine:3.23
# bash, coreutils and python3 are needed by bench.sh
RUN apk add --no-cache bash coreutils python3 z3-dev gmp-dev libgomp
COPY --from=build /build/atlas-examples /usr/share/atlas/examples
COPY --from=build /root/.cabal/bin/atlas-re /usr/bin/atlas-re
COPY --from=build /build/atlas-re/scripts/bench.sh /usr/bin/bench.sh
ENV ATLAS_EXAMPLES=/usr/share/atlas/examples
# proofs are written to /work/out by default; writable for any user, so the
# container can run with --user to own files in mounted directories
WORKDIR /work
RUN mkdir out && chmod -R a+rwx /work
ENTRYPOINT ["atlas-re", "--search", "/usr/share/atlas/examples"]
CMD ["--help"]
