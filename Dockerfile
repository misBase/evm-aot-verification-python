# Reproducible environment for chapters 4-5 and the experiments (Linux x86-64).
#   docker build -t evm-aot-artifact .
#   docker run --rm -it evm-aot-artifact make smoke
FROM python:3.13.7-slim-bookworm
RUN apt-get update \
 && apt-get install -y --no-install-recommends git make procps util-linux \
 && rm -rf /var/lib/apt/lists/*
WORKDIR /artifact
COPY . /artifact
RUN make install PYTHON=python3.13
CMD ["bash"]
