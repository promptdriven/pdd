FROM ubuntu:24.04

# To use:
# make sure GEMINI_API_KEY is set
# docker build -t pddsyncbug .
# docker run -it --rm -e GEMINI_API_KEY=$GEMINI_API_KEY pddsyncbug bash
# inside docker shell:
# pdd setup
# source ~/.zshrc  # or source ~/.bashrc
# cd pdd/examples/hello
# pdd --force sync hello |& tee o.txt

RUN apt update -y && apt install -y gcc git python3-pip python3-requests python3-dev vim tmux && rm -rf /var/lib/apt/cache/*

COPY --from=docker.io/astral/uv:latest /uv /uvx /bin/

RUN uv tool install pdd-cli

RUN update-alternatives --install /usr/bin/python python /usr/bin/python3 1

WORKDIR /root

ENV PATH=$PATH:/root/.local/bin/

ENV PDD_EXAMPLE_OUTPUT_PATH=examples
ENV PDD_TEST_OUTPUT_PATH=tests

RUN git clone https://github.com/promptdriven/pdd.git

