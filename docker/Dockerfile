# Created by Tomas Kolarik
# Eternal glory to him
# Eternal suffering for every mistake

FROM debian:latest
USER root

RUN apt-get update -y
RUN apt-get install -y \
    apt-utils \
    make \
    cmake \
    build-essential \
    git \
    bison \
    flex \
    libgmp-dev

RUN git clone --depth 1 https://github.com/usi-verification-and-security/opensmt.git
WORKDIR opensmt
RUN make
# RUN make install

ENTRYPOINT ["build/opensmt"]
