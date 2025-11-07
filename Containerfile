# Containerfile
FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    TZ=UTC \
    LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

# Base deps (we use rustup for a modern Rust)
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl git ca-certificates \
    build-essential clang lld cmake pkg-config \
    libgmp-dev libuv1-dev \
    xz-utils util-linux \
  && rm -rf /var/lib/apt/lists/*

# Rust (stable) + tree-sitter 0.25.10 (requires recent Cargo with edition2024)
RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y --default-toolchain stable
ENV PATH="/root/.cargo/bin:${PATH}"
RUN rustup update stable && rustup default stable
RUN cargo install tree-sitter-cli --version "0.25.10" && \
    install -m 0755 /root/.cargo/bin/tree-sitter /usr/local/bin/tree-sitter

# --- Seed Elan toolchain into a read-only location in the image ---
ARG ELAN_TOOLCHAIN=leanprover/lean4:v4.23.0-rc2
ENV ELAN_SEED=/opt/elan-seed
RUN mkdir -p "${ELAN_SEED}" && \
    curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | ELAN_HOME="${ELAN_SEED}" sh -s -- -y --default-toolchain "${ELAN_TOOLCHAIN}" --no-modify-path

# Non-root runtime user; make traversable to mapped UIDs
RUN useradd -m -d /home/user -s /bin/bash user || true
RUN chmod 755 /home/user
ENV HOME=/home/user
WORKDIR /work

# --- ENTRYPOINT: add host UID/GID to passwd, seed ~/.elan into volume once, drop privs, exec ---
RUN printf '%s\n' \
'#!/usr/bin/env bash' \
'set -euo pipefail' \
': "${HOST_UID:=1000}"' \
': "${HOST_GID:=1000}"' \
': "${HOST_USER:=user}"' \
': "${HOST_GROUP:=user}"' \
': "${ELAN_HOME:=/home/user/.elan}"' \
': "${XDG_CACHE_HOME:=/home/user/.cache}"' \
'' \
'# Ensure mapped identity exists (avoids $HOME warning).' \
'if ! getent group "${HOST_GID}" >/dev/null 2>&1; then echo "${HOST_GROUP}:x:${HOST_GID}:" >> /etc/group; fi' \
'if ! getent passwd "${HOST_UID}" >/dev/null 2>&1; then echo "${HOST_USER}:x:${HOST_UID}:${HOST_GID}:User:/home/user:/bin/bash" >> /etc/passwd; fi' \
'' \
'# First-run seed: if volume ELAN_HOME is empty/missing elan, copy from image seed (fast, no network).' \
'if [ ! -x "${ELAN_HOME}/bin/elan" ]; then' \
'  echo "[entrypoint] Seeding ${ELAN_HOME} from ${ELAN_SEED} …"' \
'  mkdir -p "${ELAN_HOME}"' \
'  cp -a "${ELAN_SEED}/." "${ELAN_HOME}/"' \
'  chown -R "${HOST_UID}:${HOST_GID}" "${ELAN_HOME}"' \
'fi' \
'' \
'# Prefer volume-managed elan in PATH so updates persist there.' \
'export PATH="${ELAN_HOME}/bin:${PATH}"' \
'' \
'# Drop to mapped user and exec.' \
'exec setpriv --reuid="${HOST_UID}" --regid="${HOST_GID}" --clear-groups -- "$@"' \
> /usr/local/bin/seeded-entrypoint.sh \
 && chmod +x /usr/local/bin/seeded-entrypoint.sh

ENTRYPOINT ["/usr/local/bin/seeded-entrypoint.sh"]
CMD ["bash"]


