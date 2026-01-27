# AI Agent Container Quick Start

Fast track to running AI coding agents (Claude, Codex) in an isolated Podman container.

## Prerequisites

- Podman installed
- That's it! This setup is self-contained.

## Quick Setup (5 minutes)

### 1. Build the container

```bash
cd ~/src/poison-lang
podman build -t localhost/poison-ai-agent:latest -f Containerfile.ai-agent .
```

### 2. Create persistent volumes

```bash
podman volume create ai_agent_elan_home
podman volume create ai_agent_ssh
podman volume create ai_agent_cache_elan
podman volume create ai_agent_cache_lake
podman volume create ai_agent_cache_uv
podman volume create ai_agent_config
```

**Note**: By default, the wrapper bind-mounts your host `~/.elan` read-only to reuse your existing Lean toolchains.
If you prefer a fully isolated toolchain, run agents with `AI_AGENT_HOST_ELAN=off` (then `ai_agent_elan_home` is used).

### 3. Install the wrapper script

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

Ensure `~/bin` is on your `PATH` (add `export PATH="$HOME/bin:$PATH"` to your shell config if needed).

### 4. (Optional) Create convenience symlinks

```bash
ln -sf ~/bin/ai-agent-jailed ~/bin/claude-jailed
ln -sf ~/bin/ai-agent-jailed ~/bin/codex-jailed
```

### 5. Run an agent

```bash
cd ~/src/poison-lang

# Run Claude Code
ai-agent-jailed claude

# Or run Codex
ai-agent-jailed codex

# Or drop into a shell inside the container
ai-agent-jailed bash
```

That's it! AI agents now run in an isolated container with access to:
- ✓ Your project files (read-write)
- ✓ Lean toolchain (independent installation)
- ✓ Common CLI tools (git, gh, rg, jq)
- ✓ SSH agent for git authentication (if ssh-agent is running on host)
- ✓ MCP tools via uvx (lean-lsp-mcp)
- ✓ Persistent configuration (including Codex login cache)

On first run, you'll see:
```
[entrypoint] Seeding /home/user/.elan from /opt/elan-seed …
```

This happens once and takes a few seconds. After that, startup is instant.

**Note**: Claude runs with `--dangerously-skip-permissions` for smoother operation within the isolated container.

## What You Get

**Isolation**
- Agents cannot access files outside `~/src/poison-lang`
- No access to other projects, home directory, or system files
- Worst case: delete the container and start fresh

**Multi-Agent Support**
- Single setup works for Claude Code, Codex, and future agents
- All agents share the same Lean toolchain
- Independent configurations per agent
- Both agents can use lean-lsp-mcp MCP server via uvx

**Git Integration**
- SSH agent forwarding enabled (if ssh-agent running on host)
- Agents can push, pull, and access private repos using your SSH keys
- No need to copy keys into the container

**Independent Toolchain**
- Self-contained Elan installation
- Pre-installed in the image, seeded on first run
- Commands like `lean`, `lake`, `elan` work out of the box
- Toolchain updates persist in `ai_agent_elan_home` volume

**Persistence**
- Agent settings saved in `ai_agent_config` volume
- Elan toolchain and caches persist across sessions
- Can be reset by removing volumes (see Troubleshooting)

## Safety Workflow

The container provides isolation, but **git is your safety net**:

1. **Before starting an agent:**
   ```bash
   git add -A
   git commit -m "Checkpoint before AI agent session"
   ```

2. **Let the agent work**

3. **Review changes:**
   ```bash
   git diff
   ```

4. **Keep or discard:**
   ```bash
   # Keep: commit the changes
   git add -A
   git commit -m "AI: implemented feature X"

   # Discard: reset to checkpoint
   git reset --hard HEAD~1
   ```

Commit frequently (every few minutes during active sessions) for fine-grained rollback.

## Common Tasks

### Check available agents
```bash
ai-agent-jailed
# Shows: Usage: ai-agent-jailed <agent> [agent-args...]
```

### Check agent version
```bash
ai-agent-jailed claude --version
ai-agent-jailed codex --version
```

### Get help
```bash
ai-agent-jailed claude --help
ai-agent-jailed codex --help
```

### Run with a different project
```bash
POISON_PROJECT_DIR=/path/to/other/project ai-agent-jailed claude
```

### Drop into a shell inside the container
```bash
ai-agent-jailed claude bash
# or:
ai-agent-jailed codex bash
```

From here you can run `lean`, `lake`, `npm`, `python3`, etc.

### Using convenience symlinks

If you created the optional symlinks:
```bash
claude-jailed        # Same as: ai-agent-jailed claude
codex-jailed         # Same as: ai-agent-jailed codex
```

## Troubleshooting

### "Command not found: ai-agent-jailed"
Add `~/bin` to PATH or use the full path:
```bash
~/src/poison-lang/scripts/ai-agent-jailed claude
```

### "Error: ai_agent_elan_home: no such volume"
Create the required volumes:
```bash
podman volume create ai_agent_elan_home
podman volume create ai_agent_cache_elan
podman volume create ai_agent_cache_lake
podman volume create ai_agent_config
```

### "Usage: ai-agent-jailed <agent> [agent-args...]"
You must specify which agent to run:
```bash
ai-agent-jailed claude    # Not just: ai-agent-jailed
```

### "Error: Unknown agent 'xyz'"
Only `claude` and `codex` are supported. Check spelling:
```bash
ai-agent-jailed claude    # ✓
ai-agent-jailed codex     # ✓
ai-agent-jailed gpt       # ✗ (not supported)
```

### Agent can't find `lean` or `lake`
Check if the Elan toolchain was seeded on first run:
```bash
ai-agent-jailed claude bash
ls -la ~/.elan/bin
lean --version
```

If empty, the entrypoint may have failed. Check the image was built correctly:
```bash
podman build -t localhost/poison-ai-agent:latest -f Containerfile.ai-agent .
```

### Permission errors
Verify UID/GID mapping is working:
```bash
ai-agent-jailed claude bash
id  # Should show your host UID/GID
ls -la /work  # Files should be owned by your UID
```

### Claude/Codex config not persisting
Ensure the config volume exists:
```bash
podman volume ls | grep ai_agent_config
```

### Git authentication fails (Permission denied publickey)
SSH agent forwarding may not be set up:
```bash
# On host, check if ssh-agent is running
echo $SSH_AUTH_SOCK
# Should show a socket path

# If not set, start ssh-agent
eval $(ssh-agent)
ssh-add ~/.ssh/id_ed25519

# Verify inside container
ai-agent-jailed claude bash
ssh -T git@github.com
```

See the full documentation for more details on SSH agent forwarding.

## Full Documentation

For architecture details, security model, and advanced usage, see:
- `doc/podman-ai-agents.md` - Full AI agent container documentation
- Blog post: https://blog.herlein.com/post/localdev-container-jail/

## Supported Agents

| Agent | Command | Description |
|-------|---------|-------------|
| `claude` | `ai-agent-jailed claude` | Anthropic Claude Code |
| `codex` | `ai-agent-jailed codex` | OpenAI Codex |

All agents share the same Lean toolchain but have independent configurations.
