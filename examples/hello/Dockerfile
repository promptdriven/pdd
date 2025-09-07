FROM ubuntu:24.04

# To use:
# make sure GEMINI_API_KEY is set
# make sure pdd-setup.py is in the same directory as the Dockerfile
# docker build -t pddsyncbug .
# docker run -it --rm -e GEMINI_API_KEY=$GEMINI_API_KEY pddsyncbug bash
# inside docker shell:
# python pdd-setup.py
# choose 3
# source /root/.pdd/api-env
# cd pdd/examples/hello
# pdd --force sync hello |& tee o.txt
# The first time this runs it will spend $0.03 and give the Unknown Command error
# The subsequent times it will print $0.00 and still fail


RUN apt update -y && apt install -y gcc git python3-pip python3-requests python3-dev vim tmux && rm -rf /var/lib/apt/cache/*

COPY --from=docker.io/astral/uv:latest /uv /uvx /bin/
COPY pdd-setup.py /root

RUN uv tool install pdd-cli

RUN update-alternatives --install /usr/bin/python python /usr/bin/python3 1

WORKDIR /root

ENV PATH=$PATH:/root/.local/bin/

ENV PDD_EXAMPLE_OUTPUT_PATH=examples
ENV PDD_TEST_OUTPUT_PATH=tests

RUN git clone https://github.com/promptdriven/pdd.git

