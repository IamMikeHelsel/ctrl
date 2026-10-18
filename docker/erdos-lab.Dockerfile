# Clean-room test environment for the Erdős lab (erdos/ + the erdos CLI).
# Works on arm64 (DGX Spark) and amd64. Build from the repo root:
#   docker build -f docker/erdos-lab.Dockerfile -t erdos-lab .
#   docker run --rm --network none erdos-lab   # ruff + pytest + erdos check --all (offline)
#   docker run --rm erdos-lab uv run erdos check 834   # one problem
# The image holds the Mathlib cache (~5 GB), so later builds that only change sources are fast.
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive LANG=C.UTF-8
RUN apt-get update && apt-get install -y --no-install-recommends \
      ca-certificates curl git build-essential ripgrep python3 \
    && rm -rf /var/lib/apt/lists/*

RUN useradd -m lab
USER lab
WORKDIR /home/lab/ctrl
ENV PATH=/home/lab/.elan/bin:/home/lab/.local/bin:$PATH

# Toolchains: elan with the exact Lean pinned by erdos/lean-toolchain, and uv.
COPY --chown=lab erdos/lean-toolchain erdos/lean-toolchain
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain "$(cat erdos/lean-toolchain)" \
    && curl -LsSf https://astral.sh/uv/install.sh | sh

# Lean dependencies first (cached layer): Formal Conjectures + prebuilt Mathlib.
COPY --chown=lab erdos/lakefile.toml erdos/lake-manifest.json erdos/
RUN cd erdos && lake exe cache get

# Python dependencies (cached layer).
COPY --chown=lab pyproject.toml uv.lock README.md ./
RUN uv sync --frozen --no-install-project

# The repo itself.
COPY --chown=lab . .
RUN uv sync --frozen

ENV ERDOS_AGENT=1 UV_OFFLINE=1 UV_FROZEN=1
CMD ["sh", "-c", "uv run ruff check . && uv run ruff format --check . && uv run pytest -q && uv run erdos check --all --plain"]
