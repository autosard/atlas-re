FROM alpine:3.23
RUN apk add --no-cache build-base git curl ncurses gmp-dev z3-dev
RUN mkdir /build
WORKDIR /build
RUN git clone -b cav26-artifact https://github.com/autosard/atlas-re.git
RUN git clone -b atlas-revisited https://github.com/autosard/atlas-examples.git 
RUN git clone https://github.com/IagoAbal/haskell-z3
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
ENV PATH="$PATH:/root/.ghcup/bin"
WORKDIR atlas-re
RUN cabal install
ENTRYPOINT ["/bin/sh"]

FROM alpine:3.23 AS wrapper
RUN apk add --no-cache bash z3-dev gmp-dev libgomp
COPY --from=0 /build/atlas-examples /usr/share/atlas/examples
COPY --from=0 /root/.cabal/bin/atlas-re /usr/bin/atlas-re
ADD wrapper.sh /usr/bin/wrapper.sh
RUN chmod +x /usr/bin/wrapper.sh
ADD smoke-test.sh /usr/bin/smoke-test.sh
RUN chmod +x /usr/bin/smoke-test.sh
ADD full-test.sh /usr/bin/full-test.sh
RUN chmod +x /usr/bin/full-test.sh
ENTRYPOINT ["wrapper.sh"]
