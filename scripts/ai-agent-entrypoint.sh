#!/usr/bin/env bash
set -euo pipefail
# Preserve TZ from Podman -e so exec'd process sees host timezone.
SAVED_TZ="${TZ:-}"
: "${HOST_UID:=1000}"
: "${HOST_GID:=1000}"
: "${HOST_USER:=user}"
: "${HOST_GROUP:=user}"
: "${ELAN_HOME:=/home/user/.elan}"
: "${XDG_CACHE_HOME:=/home/user/.cache}"
# Container-local Codex state (config/auth/history). Overridable by wrapper.
: "${CODEX_HOME:=/home/user/.config/poison-codex}"
# Container-local Claude Code state (config/auth). Overridable by wrapper.
: "${CLAUDE_CONFIG_DIR:=/home/user/.config/poison-claude}"

AM_ROOT=0
[ "$(id -u)" -eq 0 ] && AM_ROOT=1

# Ensure mapped identity exists (avoids $HOME warning).
if [ "${AM_ROOT}" -eq 1 ]; then
  if ! getent group "${HOST_GID}" >/dev/null 2>&1; then echo "${HOST_GROUP}:x:${HOST_GID}:" >> /etc/group; fi
  if ! getent passwd "${HOST_UID}" >/dev/null 2>&1; then echo "${HOST_USER}:x:${HOST_UID}:${HOST_GID}:User:/home/user:/bin/bash" >> /etc/passwd; fi
fi

# Ensure home/config/cache dirs are writable by mapped UID/GID.
for d in "/home/user" "${XDG_CACHE_HOME}" "/home/user/.config"; do
  mkdir -p "${d}"
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${d}" 2>/dev/null || true; fi
done

# Tree-sitter CLI uses ~/.config/tree-sitter/config.json to locate grammar repos.
# Seed a minimal config pointing at the project parser directory (first run only).
mkdir -p "${HOME}/.config/tree-sitter"
if [ "${AM_ROOT}" -eq 1 ]; then chown -R "${HOST_UID}:${HOST_GID}" "${HOME}/.config/tree-sitter" 2>/dev/null || true; fi
if [ ! -f "${HOME}/.config/tree-sitter/config.json" ]; then
  jq -n '{"parser-directories": ["/work/parser"]}' > "${HOME}/.config/tree-sitter/config.json"
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${HOME}/.config/tree-sitter/config.json" 2>/dev/null || true; fi
fi

# Ensure ~/.local/bin exists and is on PATH (some CLIs expect it).
mkdir -p "/home/user/.local/bin"
if [ "${AM_ROOT}" -eq 1 ]; then chown -R "${HOST_UID}:${HOST_GID}" "/home/user/.local" 2>/dev/null || true; fi
export PATH="/home/user/.local/bin:${PATH}"

# First-run seed: gh extensions live under ~/.local/share/gh/extensions; copy from image seed so they persist with the home volume.
GH_EXT_DIR="${XDG_DATA_HOME:-/home/user/.local/share}/gh/extensions"
mkdir -p "${GH_EXT_DIR}"
if [ "${AM_ROOT}" -eq 1 ]; then chown -R "${HOST_UID}:${HOST_GID}" "${GH_EXT_DIR}" 2>/dev/null || true; fi
if [ -w "${GH_EXT_DIR}" ] && [ ! -d "${GH_EXT_DIR}/gh-sub-issue" ]; then
  if [ -d "${GH_EXTENSIONS_SEED:-/opt/gh-extensions-seed}/.local/share/gh/extensions" ]; then
    cp -a "${GH_EXTENSIONS_SEED}/.local/share/gh/extensions/." "${GH_EXT_DIR}/"
    if [ "${AM_ROOT}" -eq 1 ]; then chown -R "${HOST_UID}:${HOST_GID}" "${GH_EXT_DIR}"; fi
  fi
fi

# Claude Code: expose the seed binary via ~/.local/bin/claude (on PATH) so the CLI is found
# without putting it in /usr/local/bin (which the CLI treats as a leftover npm install).
if [ ! -e "/home/user/.local/bin/claude" ] && [ -x "${CLAUDE_SEED:-/opt/claude-seed}/.local/bin/claude" ]; then
  ln -sf "${CLAUDE_SEED:-/opt/claude-seed}/.local/bin/claude" "/home/user/.local/bin/claude" 2>/dev/null || true
fi

# Lean 4 skills plugin: env vars and symlink from image seed (no persistence needed).
LEAN4_PLUGIN_ROOT="${LEAN4_SKILLS_SEED:-/opt/lean4-skills-seed}/plugins/lean4"
export LEAN4_PLUGIN_ROOT LEAN4_SCRIPTS="${LEAN4_PLUGIN_ROOT}/lib/scripts" LEAN4_REFS="${LEAN4_PLUGIN_ROOT}/skills/lean4/references"
PLUGINS_DIR="${CLAUDE_CONFIG_DIR}/plugins"
mkdir -p "${PLUGINS_DIR}"
if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${PLUGINS_DIR}" 2>/dev/null || true; fi
if [ -w "${PLUGINS_DIR}" ] && [ -d "${LEAN4_PLUGIN_ROOT}" ]; then
  if [ ! -L "${PLUGINS_DIR}/lean4" ] || [ "$(readlink "${PLUGINS_DIR}/lean4" 2>/dev/null)" != "${LEAN4_PLUGIN_ROOT}" ]; then
    rm -f "${PLUGINS_DIR}/lean4" 2>/dev/null; ln -sf "${LEAN4_PLUGIN_ROOT}" "${PLUGINS_DIR}/lean4"
    if [ "${AM_ROOT}" -eq 1 ]; then chown -h "${HOST_UID}:${HOST_GID}" "${PLUGINS_DIR}/lean4" 2>/dev/null || true; fi
  fi
fi

# Codex: symlink lean4 skill into ~/.agents/skills (Codex discovers skills from user dir).
CODEX_SKILLS_DIR="${HOME}/.agents/skills"
mkdir -p "${CODEX_SKILLS_DIR}"
if [ "${AM_ROOT}" -eq 1 ]; then chown -R "${HOST_UID}:${HOST_GID}" "${CODEX_SKILLS_DIR}" 2>/dev/null || true; fi
LEAN4_SKILLS_PATH="${LEAN4_SKILLS_SEED:-/opt/lean4-skills-seed}/plugins/lean4/skills/lean4"
if [ -w "${CODEX_SKILLS_DIR}" ] && [ -d "${LEAN4_SKILLS_PATH}" ]; then
  if [ ! -L "${CODEX_SKILLS_DIR}/lean4" ] || [ "$(readlink "${CODEX_SKILLS_DIR}/lean4" 2>/dev/null)" != "${LEAN4_SKILLS_PATH}" ]; then
    rm -f "${CODEX_SKILLS_DIR}/lean4" 2>/dev/null; ln -sf "${LEAN4_SKILLS_PATH}" "${CODEX_SKILLS_DIR}/lean4"
    if [ "${AM_ROOT}" -eq 1 ]; then chown -h "${HOST_UID}:${HOST_GID}" "${CODEX_SKILLS_DIR}/lean4" 2>/dev/null || true; fi
  fi
fi

# Proof development skills: symlink into Claude Code, Codex, and project skill dirs.
PROOF_SKILLS_DIR="${PROOF_SKILLS_SEED:-/opt/proof-skills-seed}"
# Claude Code: ${CLAUDE_CONFIG_DIR}/skills/ when CLAUDE_CONFIG_DIR is set, else ~/.claude/skills/
CLAUDE_SKILLS_DIR="${CLAUDE_CONFIG_DIR:-${HOME}/.claude}/skills"
mkdir -p "${CLAUDE_SKILLS_DIR}"
if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CLAUDE_SKILLS_DIR}" 2>/dev/null || true; fi
# Codex: ${CODEX_HOME}/skills/ (CODEX_HOME may be overridden, e.g. /home/user/.config/poison-codex)
CODEX_CUSTOM_SKILLS="${CODEX_HOME:-${HOME}/.codex}/skills"
mkdir -p "${CODEX_CUSTOM_SKILLS}"
if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CODEX_CUSTOM_SKILLS}" 2>/dev/null || true; fi
if [ -d "${PROOF_SKILLS_DIR}" ]; then
  for skill in proof-step proof-step-review proof-planning; do
    skill_path="${PROOF_SKILLS_DIR}/${skill}"
    [ -d "${skill_path}" ] || continue
    # Claude Code
    if [ -w "${CLAUDE_SKILLS_DIR}" ]; then
      rm -f "${CLAUDE_SKILLS_DIR}/${skill}" 2>/dev/null; ln -sf "${skill_path}" "${CLAUDE_SKILLS_DIR}/${skill}"
      if [ "${AM_ROOT}" -eq 1 ]; then chown -h "${HOST_UID}:${HOST_GID}" "${CLAUDE_SKILLS_DIR}/${skill}" 2>/dev/null || true; fi
    fi
    # Codex (CODEX_HOME path)
    if [ -w "${CODEX_CUSTOM_SKILLS}" ]; then
      rm -f "${CODEX_CUSTOM_SKILLS}/${skill}" 2>/dev/null; ln -sf "${skill_path}" "${CODEX_CUSTOM_SKILLS}/${skill}"
      if [ "${AM_ROOT}" -eq 1 ]; then chown -h "${HOST_UID}:${HOST_GID}" "${CODEX_CUSTOM_SKILLS}/${skill}" 2>/dev/null || true; fi
    fi
    # Codex (default ~/.agents/skills/ fallback)
    if [ -w "${CODEX_SKILLS_DIR}" ]; then
      rm -f "${CODEX_SKILLS_DIR}/${skill}" 2>/dev/null; ln -sf "${skill_path}" "${CODEX_SKILLS_DIR}/${skill}"
      if [ "${AM_ROOT}" -eq 1 ]; then chown -h "${HOST_UID}:${HOST_GID}" "${CODEX_SKILLS_DIR}/${skill}" 2>/dev/null || true; fi
    fi
  done
fi

# Persist SSH known_hosts (agent keys stay on host; we only keep host fingerprints).
mkdir -p "${HOME}/.ssh"
chmod 700 "${HOME}/.ssh" 2>/dev/null || true
touch "${HOME}/.ssh/known_hosts" 2>/dev/null || true
chmod 600 "${HOME}/.ssh/known_hosts" 2>/dev/null || true
if ! grep -q "^github\\.com[ ,]" "${HOME}/.ssh/known_hosts" 2>/dev/null; then
  ssh-keyscan -H github.com 2>/dev/null >> "${HOME}/.ssh/known_hosts" || true
fi

# OpenSSH picks UserKnownHostsFile based on the passwd home directory for the current uid,
# not the HOME environment variable. Under rootless keep-id, the uid may map to a user whose
# home is /home/ubuntu (or similar). Ensure that home dir uses the persisted /home/user/.ssh.
USER_HOME="$(getent passwd "$(id -u)" 2>/dev/null | cut -d: -f6 || true)"
if [ -n "${USER_HOME}" ] && [ "${USER_HOME}" != "${HOME}" ]; then
  mkdir -p "${USER_HOME}" 2>/dev/null || true
  if [ ! -e "${USER_HOME}/.ssh" ]; then
    ln -s "${HOME}/.ssh" "${USER_HOME}/.ssh" 2>/dev/null || true
  fi
fi

# Ensure Claude Code config dir exists (for persistent auth); export so claude CLI finds it.
export CLAUDE_CONFIG_DIR
mkdir -p "${CLAUDE_CONFIG_DIR}"
if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CLAUDE_CONFIG_DIR}" 2>/dev/null || true; fi

# Seed installMethod so the CLI does not warn "config install method is unknown" (we run the native binary).
# jq fails and triggers script exit if JSON is malformed.
if [ ! -f "${CLAUDE_CONFIG_DIR}/.config.json" ]; then
  jq -n '.installMethod = "native"' > "${CLAUDE_CONFIG_DIR}/.config.json"
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CLAUDE_CONFIG_DIR}/.config.json" 2>/dev/null || true; fi
fi

# Seed a minimal Claude MCP config (first run only) to enable lean-lsp via uvx.
# jq fails and triggers script exit if JSON is malformed.
if [ ! -f "${CLAUDE_CONFIG_DIR}/mcp.json" ]; then
  jq -n --arg path "/work" '{
    mcpServers: {
      "lean-lsp": {
        type: "stdio",
        command: "uvx",
        args: ["lean-lsp-mcp"],
        env: {
          LEAN_PROJECT_PATH: $path,
          LEAN_LOG_LEVEL: "NONE"
        }
      }
    }
  }' > "${CLAUDE_CONFIG_DIR}/mcp.json"
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CLAUDE_CONFIG_DIR}/mcp.json" 2>/dev/null || true; fi
fi

# ccstatusline: seed display config for Claude Code status line (first run only).
CCSTATUSLINE_DIR="/home/user/.config/ccstatusline"
mkdir -p "${CCSTATUSLINE_DIR}"
if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CCSTATUSLINE_DIR}" 2>/dev/null || true; fi
if [ ! -f "${CCSTATUSLINE_DIR}/settings.json" ]; then
  cp /opt/ccstatusline-seed/settings.json "${CCSTATUSLINE_DIR}/settings.json"
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CCSTATUSLINE_DIR}/settings.json" 2>/dev/null || true; fi
fi

# Ensure Claude settings.json has statusLine config.
# Claude Code reads user settings from $CLAUDE_CONFIG_DIR/settings.json.
if [ -f "${CLAUDE_CONFIG_DIR}/settings.json" ]; then
  if ! jq -e '.statusLine' "${CLAUDE_CONFIG_DIR}/settings.json" >/dev/null 2>&1; then
    jq '. + {
      statusLine: {
        type: "command",
        command: "npx -y ccstatusline@latest",
        padding: 0
      }
    }' "${CLAUDE_CONFIG_DIR}/settings.json" > "${CLAUDE_CONFIG_DIR}/settings.json.tmp" \
      && mv "${CLAUDE_CONFIG_DIR}/settings.json.tmp" "${CLAUDE_CONFIG_DIR}/settings.json"
    if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CLAUDE_CONFIG_DIR}/settings.json" 2>/dev/null || true; fi
  fi
else
  jq -n '{
    statusLine: {
      type: "command",
      command: "npx -y ccstatusline@latest",
      padding: 0
    }
  }' > "${CLAUDE_CONFIG_DIR}/settings.json"
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CLAUDE_CONFIG_DIR}/settings.json" 2>/dev/null || true; fi
fi

# Seed a minimal Codex config in CODEX_HOME (first run only).
mkdir -p "${CODEX_HOME}"
if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CODEX_HOME}" 2>/dev/null || true; fi
if [ ! -f "${CODEX_HOME}/config.toml" ]; then
  cat > "${CODEX_HOME}/config.toml" <<'EOF'
model = "gpt-5.4"
model_reasoning_effort = "xhigh"
model_context_window = 1000000 
model_auto_compact_token_limit = 997500
sandbox_mode = "workspace-write"
approval_policy = "on-request"

[projects."/work"]
trust_level = "trusted"

[mcp_servers.lean-lsp]
command = "uvx"
args = ["lean-lsp-mcp"]

[mcp_servers.lean-lsp.env]
LEAN_PROJECT_PATH = "/work"
LEAN_LOG_LEVEL = "NONE"

web_search = "live"
EOF
  if [ "${AM_ROOT}" -eq 1 ]; then chown "${HOST_UID}:${HOST_GID}" "${CODEX_HOME}/config.toml" 2>/dev/null || true; fi
fi

# First-run seed: if volume ELAN_HOME is empty/missing elan, copy from image seed (fast, no network).
if [ ! -x "${ELAN_HOME}/bin/elan" ]; then
  if [ -w "${ELAN_HOME}" ]; then
    echo "[entrypoint] Seeding ${ELAN_HOME} from ${ELAN_SEED} …"
    mkdir -p "${ELAN_HOME}"
    cp -a "${ELAN_SEED}/." "${ELAN_HOME}/"
    if [ "${AM_ROOT}" -eq 1 ]; then chown -R "${HOST_UID}:${HOST_GID}" "${ELAN_HOME}"; fi
  else
    # e.g. ELAN_HOME bind-mounted read-only from host; fall back to using the seed elan binary.
    export PATH="${ELAN_SEED}/bin:${PATH}"
  fi
fi

# Prefer volume-managed elan in PATH so updates persist there.
export PATH="${ELAN_HOME}/bin:${PATH}"

# Ensure the project-specified toolchain exists in ELAN_HOME (if writable). This avoids
# surprising downloads when the toolchain is already available via a host mount or volume.
# Skip install when already present to avoid redundant work on every container start.
if [ -f "/work/lean-toolchain" ] && [ -w "${ELAN_HOME}" ] && [ -x "${ELAN_HOME}/bin/elan" ]; then
  TOOLCHAIN="$(tr -d '\r\n' < /work/lean-toolchain)"
  if [ -n "${TOOLCHAIN}" ] && ! "${ELAN_HOME}/bin/elan" toolchain list 2>/dev/null | grep -qF "${TOOLCHAIN}"; then
    "${ELAN_HOME}/bin/elan" toolchain install "${TOOLCHAIN}" >/dev/null 2>&1 || true
  fi
fi

# If we are already running unprivileged, we cannot (and do not need to) drop privileges.
if [ "${AM_ROOT}" -eq 0 ]; then
  [ -n "${SAVED_TZ:-}" ] && export TZ="${SAVED_TZ}"
  exec "$@"
fi

# Rootless Podman commonly maps host UID to container uid 0. In that case, dropping to
# HOST_UID (e.g. 1000) can make /work bind mounts unreadable. Detect this mapping and
# keep running as uid 0 when it maps directly to HOST_UID.
if [ "${AM_ROOT}" -eq 1 ] && awk 'NR==1{print $1, $2, $3; exit}' /proc/self/uid_map | grep -qx "0 ${HOST_UID} 1"; then
  [ -n "${SAVED_TZ:-}" ] && export TZ="${SAVED_TZ}"
  exec "$@"
fi

# Otherwise, drop to mapped user and exec. Avoid --clear-groups because setgroups is commonly
# denied in rootless user namespaces (which would break startup even when uid/gid changes are OK).
[ -n "${SAVED_TZ:-}" ] && export TZ="${SAVED_TZ}"
exec setpriv --reuid="${HOST_UID}" --regid="${HOST_GID}" --keep-groups -- "$@"
