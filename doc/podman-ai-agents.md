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
* **Project-scoped access** — Read-write access limited to `~/src/poison-lang`
* **Configuration persistence** — Agent settings stored in dedicated volumes
* **Rootless operation** — Full compatibility with rootless Podman and SELinux
* **Multi-agent support** — Single container image supports multiple AI assistants

The worst that can happen is you discard the container. Git serves as the actual safety net — commit frequently during active sessions to enable rapid rollback.

---

## Architecture Overview

The AI agent container includes:
* **Node.js LTS** and the `@anthropic-ai/claude-code` npm package (with `--dangerously-skip-permissions` enabled)
* **Python 3** and the `openai` package for Codex access
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
* `ai_agent_config` → `/home/user/.config` (Agent configurations and uvx cache, persistent)

The project directory is **bind-mounted** from the host at `/work`.

---

## Supported Agents

The wrapper script `ai-agent-jailed` supports multiple AI coding agents:

| Agent | Command | Description |
|-------|---------|-------------|
| `claude` | `ai-agent-jailed claude` | Anthropic Claude Code |
| `codex` | `ai-agent-jailed codex` | OpenAI Codex (via openai CLI) |

All agents share the same Lean toolchain and volumes but have independent configurations.

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
podman volume create ai_agent_cache_elan
podman volume create ai_agent_cache_lake
podman volume create ai_agent_config
```

These volumes provide persistence across container runs and store all Elan/Lake/agent state.

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

### Running with custom project directory

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

* **Project directory** (`~/src/poison-lang` by default) — read-write
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
* Updating AI agent packages (Claude Code, OpenAI CLI)
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
pip3 install --upgrade openai
```

(Changes persist within the container image until next rebuild.)

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

## Troubleshooting

### "Usage: ai-agent-jailed <agent> [agent-args...]"

You must specify which agent to run:
```bash
ai-agent-jailed claude    # Not just: ai-agent-jailed
```

### "Error: Unknown agent 'xyz'"

Only `claude` and `codex` are currently supported. Check available agents:
```bash
ai-agent-jailed
```

### Agents cannot find `lean` or `lake`

Ensure the Elan volumes exist and contain a valid installation:

```bash
podman volume ls | grep ai_agent_elan
```

If the volumes exist but are empty, the entrypoint should have seeded them on first run. Check:

```bash
ai-agent-jailed claude bash
ls -la ~/.elan/bin
lean --version
```

If missing, rebuild the image or manually seed the volumes.

### Permission errors on project files

Verify that `HOST_UID` and `HOST_GID` are correctly passed:

```bash
ai-agent-jailed claude bash
id
```

Should show your host UID/GID.

### Agent config not persisting

Ensure the `ai_agent_config` volume exists:

```bash
podman volume ls | grep ai_agent_config
```

### SELinux relabeling issues

The `:Z` flag on the project bind mount handles SELinux relabeling. If you encounter issues, check:

```bash
ls -lZ ~/src/poison-lang
```

---

## Notes on the Original Inspiration

This setup is inspired by the ["localdev-container-jail"](https://blog.herlein.com/post/localdev-container-jail/) approach, which emphasises:

* **Isolation over trust** — AI assistants run in sandboxes where "the worst that happens is you blow away the container"
* **Git as safety net** — Version control is the real protection; containers just limit the blast radius
* **Read-only reference mounts** — External code can be mounted read-only to prevent accidental modifications (not used here but available if needed)

The Poison Language setup adapts this to a Podman + RHEL-friendly architecture with independent Lean toolchain volumes.
