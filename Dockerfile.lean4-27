FROM ubuntu:noble

RUN apt-get update && apt-get install -y curl && rm -rf /var/lib/apt/lists/*

ENV PATH="/root/.elan/bin:${PATH}"

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.27.0

RUN elan toolchain install leanprover/lean4:v4.27.0

RUN echo '#eval 1 + 1' | lean --stdin | grep -q '^2$'

RUN echo '#eval Lean.versionString' | lean --stdin | grep -q '"4.27.0"'

CMD ["/bin/bash"]
