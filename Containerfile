# Containerfile
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    TZ=UTC \
    LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

# ------------------------------------------------------------
# Base development dependencies for Lean/Lake and Tree-sitter
# ------------------------------------------------------------
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl git ca-certificates \
    build-essential clang lld cmake pkg-config \
    libgmp-dev libuv1-dev \
    # for tree-sitter (Rust + Cargo)
    rustc cargo \
  && rm -rf /var/lib/apt/lists/*

# Create a non-root user to match rootless podman runtime
RUN useradd -m -d /home/user -s /bin/bash user || true
ENV HOME=/home/user
WORKDIR /home/user

# ------------------------------------------------------------
# Install Elan + Lean 4 toolchain
# ------------------------------------------------------------
RUN bash -lc '\
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- --default-toolchain leanprover/lean4:v4.23.0-rc2 --no-modify-path \
'
ENV PATH="/home/user/.elan/bin:${PATH}"

# ------------------------------------------------------------
# Install tree-sitter CLI via Cargo
# ------------------------------------------------------------
RUN bash -lc '\
  cargo install tree-sitter-cli --version "^0.25.6" \
'

# Verify installation and version
RUN tree-sitter --version

# Default working directory (host project will mount here)
WORKDIR /work

