# Podman-based Isolated AI Agent Environment

This document describes the Podman-based setup for running AI coding agents (Claude Code, OpenAI Codex, etc.) in an isolated container with access to the Poison Language project and Lean toolchain.

## Motivation

Running AI coding assistants with unrestricted host access carries risks:
* Unintended modifications to system files or other projects
* Accidental exposure of sensitive data
* Tools operating beyond their intended scope

This containerised setup provides:
* **Filesystem isolation** — Agents only see mounted directories
* **Independent Lean toolchain** — Pre-installed Elan with persistent volumes
* **Project-scoped access** — Read-write access limited to one mounted checkout (`~/src/poison-lang` by default)
* **Configuration persistence** — Agent settings stored in dedicated volumes
* **Rootless operation** — Full compatibility with rootless Podman and SELinux
* **Multi-agent support** — Single container image supports multiple AI assistants

The worst that can happen is you discard the container. Git serves as the actual safety net — commit frequently during active sessions to enable rapid rollback.

---

## Architecture Overview

The AI agent container includes:
* **Node.js LTS** and the `@anthropic-ai/claude-code` npm package (with `--dangerously-skip-permissions` enabled)
* **OpenAI Codex** via the `@openai/codex` npm package (the `codex` CLI)
* **uv/uvx** for running Python tools (lean-lsp-mcp MCP server)
* **Pre-installed Elan toolchain** seeded from the image (v4.23.0-rc2 by default)
* **Common CLI tools**: git, gh (GitHub CLI), ripgrep (rg), jq
* **Build tools** for Lean development (GMP, libuv, clang, cmake, etc.)
* **SSH agent forwarding** for git authentication (if `$SSH_AUTH_SOCK` is set on host)
* **Entrypoint script** that maps host UID/GID, seeds Elan on first run, and drops privileges

Runtime state is managed via **Podman volumes**:
* `ai_agent_elan_home` → `/home/user/.elan` (Elan toolchain installation, persistent)
* `ai_agent_cache_elan` → `/home/user/.cache/elan` (Elan cache, persistent)
* `ai_agent_cache_lake` → `/home/user/.cache/lake` (Lake build cache, persistent)
* `ai_agent_config` → `/home/user/.config` (Agent configurations, Codex login cache, and uvx cache, persistent)

The project directory is **bind-mounted** from the host at `/work`.

---

## Supported Agents

The wrapper script `ai-agent-jailed` supports multiple AI coding agents:

| Agent | Command | Description |
|-------|---------|-------------|
| `claude` | `ai-agent-jailed claude` | Anthropic Claude Code |
| `codex` | `ai-agent-jailed codex` | OpenAI Codex |

All agents share the same Lean toolchain and volumes but have independent configurations. By default, each run uses a container name derived from both agent and workspace path (`poison-ai-agent-<agent>-<workspace-tag>`), so you can run multiple agents in parallel and also run the same agent in different workspaces at the same time. Override the container name with `AI_AGENT_CONTAINER_NAME` if needed.

---

## Setup Instructions

### Step 1: Build the AI agent image

```bash
cd ~/src/poison-lang
podman build -t localhost/poison-ai-agent:latest -f Containerfile.ai-agent .
```

### Step 2: Create persistent volumes

```bash
podman volume create ai_agent_elan_home
podman volume create ai_agent_ssh
podman volume create ai_agent_cache_elan
podman volume create ai_agent_cache_lake
podman volume create ai_agent_cache_uv
podman volume create ai_agent_config
```

These volumes provide persistence across container runs and store all Elan/Lake/agent state.

**Note**: By default, `ai-agent-jailed` bind-mounts your host `~/.elan` read-only to reuse your existing Lean toolchains.
Set `AI_AGENT_HOST_ELAN=off` to use the `ai_agent_elan_home` volume instead.

### Step 3: Install the wrapper script

```bash
# Option A: Install to ~/bin (recommended)
cp scripts/ai-agent-jailed ~/bin/
chmod +x ~/bin/ai-agent-jailed

# Option B: Create a symlink
ln -sf ~/src/poison-lang/scripts/ai-agent-jailed ~/bin/ai-agent-jailed

# Option C: Add scripts/ to PATH
export PATH="$HOME/src/poison-lang/scripts:$PATH"
# (Add to ~/.bashrc or ~/.zshrc to make permanent)
```

Ensure `~/bin` is on your `PATH`.

### Step 4: (Optional) Create convenience symlinks

For quicker access, you can create agent-specific symlinks:

```bash
ln -sf ~/bin/ai-agent-jailed ~/bin/claude-jailed
ln -sf ~/bin/ai-agent-jailed ~/bin/codex-jailed
```

Then use:
```bash
# These are equivalent:
claude-jailed         # Automatically detects "claude" from script name
ai-agent-jailed claude

codex-jailed          # Automatically detects "codex" from script name
ai-agent-jailed codex

# Optional first argument after agent is the workspace/checkout to mount at /work
claude-jailed ~/src/poison-lang-issue-70
ai-agent-jailed codex ~/src/poison-lang-issue-70 --help
```

---

## Usage

### Basic usage

```bash
cd ~/src/poison-lang

# Run Claude Code
ai-agent-jailed claude

# Run OpenAI Codex
ai-agent-jailed codex
```

This starts an interactive session with:
* Read-write access to the project directory
* Access to `lean`, `lake`, `elan` from the shared Elan volumes
* Persistent agent configuration
* Terminal isolation (no access to other host directories)

### Passing arguments to agents

```bash
# Claude with arguments
ai-agent-jailed claude --help
ai-agent-jailed claude --version

# Codex with arguments
ai-agent-jailed codex --help
```

### Running against a specific workspace/checkout

The first positional argument after the agent can be a checkout directory to mount at `/work`:

```bash
# Same script, different git worktree checkout
ai-agent-jailed claude ~/src/poison-lang-issue-70

# Symlink form works too
codex-jailed ~/src/poison-lang-issue-70 --help
```

### Running with custom project directory via environment variable

```bash
POISON_PROJECT_DIR=/path/to/other/project ai-agent-jailed claude
```

### Dropping into a shell

```bash
# Get a shell inside the container
ai-agent-jailed claude bash
# or just:
podman run --rm -it \
  -v ~/src/poison-lang:/work:Z \
  -v ai_agent_elan_home:/home/user/.elan:rw \
  localhost/poison-ai-agent:latest bash
```

---

## Git and SSH Authentication

The wrapper script automatically forwards your SSH agent to the container for git authentication. This allows AI agents to perform git operations (push, pull, clone private repos) using your SSH keys without copying them into the container.

### How it works

If `$SSH_AUTH_SOCK` is set on the host (i.e., `ssh-agent` is running), the wrapper:
1. Mounts the SSH agent socket into the container at `/ssh-agent`
2. Sets `SSH_AUTH_SOCK=/ssh-agent` inside the container
3. Git commands inside the container can now authenticate using your host's SSH keys

### Verifying SSH agent forwarding

```bash
# On host, check if ssh-agent is running
echo $SSH_AUTH_SOCK
# Should show something like: /run/user/1000/keyring/ssh

# Inside container, verify git can authenticate
ai-agent-jailed claude bash
ssh -T git@github.com
# Should show: Hi <username>! You've successfully authenticated...
```

### Troubleshooting

**"Permission denied (publickey)" errors:**
- Ensure `ssh-agent` is running on the host: `eval $(ssh-agent)`
- Add your key to the agent: `ssh-add ~/.ssh/id_ed25519`
- Verify the key is loaded: `ssh-add -l`

**SSH agent not forwarded:**
- Check `$SSH_AUTH_SOCK` is set on the host
- The wrapper only forwards the agent if the socket exists and is valid

**"container name ... is already in use":**
- By default the name includes agent + workspace, but collisions can still happen if you override `AI_AGENT_CONTAINER_NAME` with a fixed value. Either remove the old container or choose a unique name: `AI_AGENT_CONTAINER_NAME=my-container claude-jailed`

### MCP Tool Support

Both Claude and Codex can use the `lean-lsp-mcp` MCP server via `uvx`:

```bash
# The tool will be downloaded on first use and cached in ai_agent_config volume
uvx lean-lsp-mcp -h
```

After the first download, subsequent invocations are fast (cached).

---

## Security Model

### What agents can access

* **Project directory** (selected workspace, `~/src/poison-lang` by default) — read-write
* **Elan toolchain** (dedicated volumes) — read-write
* **Agent configs** (dedicated volume) — read-write

### What agents cannot access

* Host home directory
* Other projects outside the mounted directory
* Host system files
* Network services on the host (unless explicitly shared)
* Other container volumes (unless explicitly mounted)

### Safety net: Git

The container provides isolation, but **git is your actual safety net**. The blog post referenced in the initial request emphasises:

> "Commit every few minutes during an active Claude session. When Claude makes unintended changes, you can quickly `git reset --hard` back to a known-good state."

Recommended workflow:
1. Commit your work before starting an agent session
2. Let the agent make changes
3. Review with `git diff`
4. Either commit or `git reset --hard` if unintended

---

## Advantages

* **Isolation** — Agents cannot accidentally modify other projects or system files
* **Fast startup** — Elan is pre-installed in the image and seeded to volumes on first run
* **Persistent state** — Toolchain updates and caches survive across sessions
* **Persistent config** — Agent settings survive across sessions
* **Multi-agent** — Single setup supports multiple AI assistants
* **Rootless** — Works with rootless Podman and SELinux enforcing
* **No network dependency** — First run doesn't require downloading Elan or toolchains

---

## Rebuilding the Image

Rebuild when:
* Updating AI agent packages (Claude Code, Codex)
* Changing the base Node.js or Python version
* Changing the Elan toolchain version
* Modifying the entrypoint script

```bash
podman build -t localhost/poison-ai-agent:latest -f Containerfile.ai-agent .
```

To update packages without rebuilding the image:

```bash
ai-agent-jailed claude bash
npm update -g @anthropic-ai/claude-code
npm update -g @openai/codex
```

(Changes persist within the container image until next rebuild.)

---

## Migration to workspace-aware container names

If you used an older `ai-agent-jailed` that gave every run the same container name (`poison-ai-agent`) or per-agent names only (`poison-ai-agent-claude`, `poison-ai-agent-codex`), you can switch to workspace-aware names without re-creating image or volumes.

**You do not need to re-create anything.** The image (`localhost/poison-ai-agent:latest`) and all volumes (`ai_agent_*`) are unchanged. Containers are ephemeral (`--rm`): they are removed when they exit, and only the *name* used at start time has changed. All persistent state (Elan, caches, agent config) lives in volumes and is shared as before.

**Steps:**

1. **Update the script**  
   Replace your `ai-agent-jailed` (in `~/bin` or wherever you use it) with the version that uses workspace-aware names (`poison-ai-agent-<agent>-<workspace-tag>`).

2. **Remove the old container name if it still exists**  
   If a container named `poison-ai-agent` is still present (e.g. from a run that did not exit cleanly), remove it so the name is free:
   ```bash
   podman rm -f poison-ai-agent
   ```
   This removes only the **container** (the named run instance), not the image. Your built image `localhost/poison-ai-agent:latest` is unchanged; no rebuild is triggered. If you get "no such container", you can ignore this.

3. **Run as usual**  
   Use `claude-jailed` or `codex-jailed` as before. You can optionally pass a workspace checkout path as first argument, and same-agent runs in different workspaces can execute in parallel.

**There is no "fork" or copy of the container.** Podman does not clone containers. The new runs simply start a new container from the same image, with the same volume mounts, under a new name. Your existing volumes and image are reused as-is.

---

## Resetting the Environment

To wipe agent configurations:

```bash
podman volume rm ai_agent_config
podman volume create ai_agent_config
```

To completely reset (including Elan):

```bash
podman volume rm ai_agent_elan_home ai_agent_cache_elan ai_agent_cache_lake ai_agent_config
# Recreate volumes
podman volume create ai_agent_elan_home
podman volume create ai_agent_cache_elan
podman volume create ai_agent_cache_lake
podman volume create ai_agent_config
```

The next invocation will trigger a fresh seed from the image.

---

## Notes on the Original Inspiration

This setup is inspired by the ["localdev-container-jail"](https://blog.herlein.com/post/localdev-container-jail/) approach, which emphasises:

* **Isolation over trust** — AI assistants run in sandboxes where "the worst that happens is you blow away the container"
* **Git as safety net** — Version control is the real protection; containers just limit the blast radius
* **Read-only reference mounts** — External code can be mounted read-only to prevent accidental modifications (not used here but available if needed)

The Poison Language setup adapts this to a Podman + RHEL-friendly architecture with independent Lean toolchain volumes.
