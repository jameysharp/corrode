FROM ubuntu:16.04
RUN apt-get update && apt-get install git ghc haskell-stack -y
RUN git clone https://github.com/jameysharp/corrode.git
RUN cd corrode && stack build && stack install
ENV PATH="/root/.local/bin:${PATH}"
