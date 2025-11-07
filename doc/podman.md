# Podman-based Development Environment for Lean / Lake / Tree-sitter

This document describes the architecture and workflow of the project’s Podman-based development environment. The goals of this setup are:

* Reproducible and deterministic builds for Lean, Lake, and Tree-sitter.
* Fast container startup: no heavy Elan installation at runtime.
* Persistent Lean toolchains and caches across container runs.
* Full rootless Podman compatibility (RHEL, SELinux enforcing, university clusters).
* Ability to run `elan`, `lean`, and `lake` transparently from the host.

The environment consists of:

1. A **Containerfile** that builds a toolchain image with Rust, Tree-sitter, and a pre-installed Elan “seed.”
2. An **entrypoint script** inside the image that:

   * maps host UID/GID into the container’s `/etc/passwd`/`/etc/group`,
   * seeds persistent volumes from the pre-built Elan toolchain,
   * drops privileges to the mapped user.
3. A **host wrapper script** (`poison-dev`) that runs Lean tools in the container.
4. Three **Podman named volumes** that persist Elan’s runtime state and caches.

This document explains the full architecture, how it works, and how to bootstrap the system on a clean machine.

---

## 1. High-Level Architecture

The container image includes:

* Rust toolchain (via rustup), sufficient for `tree-sitter-cli 0.25.x`.
* `tree-sitter-cli` installed under `/usr/local/bin`.
* A pre-built Elan installation with the chosen Lean toolchain placed under:

  ```
  /opt/elan-seed
  ```

Runtime state is *not* stored inside the image. Instead, the following **Podman volumes** are mounted and used as persistent state:

* `poison_elan_home` → `/home/user/.elan`
* `poison_cache_elan` → `/home/user/.cache/elan`
* `poison_cache_lake` → `/home/user/.cache/lake`

On the **first run**, the entrypoint detects that `/home/user/.elan/bin/elan` is missing and **copies** the seed toolchain from `/opt/elan-seed/` into the writable volume.
This is a fast local filesystem copy — *no network access required*.

On later runs, the volumes already contain the Elan installation, so no seeding occurs.

Thus you get:

* Fast, repeatable developer environment startup.
* Persistent Lean toolchains and Lake caches.
* No rebuilds required when you update your toolchain via `elan update`.

---

## 2. Named Volumes

Create once:

```
podman volume create poison_elan_home
podman volume create poison_cache_elan
podman volume create poison_cache_lake
```

These provide persistence across container runs; they store all mutable Elan/Lake state.

---

## 3. Host-Side Wrapper (`poison-dev`)

A wrapper script on the host:

* Determines the project directory (Git root preferred).
* Passes host UID/GID into the container.
* Mounts the project and named volumes.
* Executes the requested command (`elan`, `lean`, `lake`, or any other tool).

Create symlinks:

```
ln -sf ~/bin/poison-dev ~/bin/elan
ln -sf ~/bin/poison-dev ~/bin/lean
ln -sf ~/bin/poison-dev ~/bin/lake
```

This lets you use Lean tools on the host as if they were natively installed, but they always run inside the container.

---

## 4. Container Entrypoint Behaviour

The entrypoint inside the image performs:

### 4.1 Host identity injection

Rootless Podman runs with user namespaces.
Your actual host UID (e.g. `49264`) normally does not exist inside the container’s `/etc/passwd`.

The entrypoint:

* appends a temporary passwd entry:

  ```
  HOST_USER:x:HOST_UID:HOST_GID:User:/home/user:/bin/bash
  ```
* appends a temporary group entry:

  ```
  HOST_GROUP:x:HOST_GID
  ```

so that `$HOME` and the passwd home match, avoiding all Elan warnings.

### 4.2 First-run Elan seed copy

If the runtime Elan home lacks a binary:

```
/home/user/.elan/bin/elan
```

the entrypoint runs:

* `cp -a /opt/elan-seed/. /home/user/.elan/`
* `chown -R HOST_UID:HOST_GID /home/user/.elan/`

This gives you a writable, persistent Elan home.

### 4.3 Privilege drop

After preparing the environment:

```
setpriv --reuid=HOST_UID --regid=HOST_GID -- "$@"
```

ensures that created files in the mounted project are owned by the real host user.

---

## 5. Building the Image

After placing `Containerfile` in the repository:

```
podman build -t localhost/poison-lang:dev -f Containerfile .
```

Rebuild only when:

* changing the seed toolchain version,
* upgrading the Rust/Cargo environment used to build tree-sitter,
* or modifying the base development dependencies.

Routine Elan updates do **not** require rebuilding the image.

---

## 6. Bootstrap on a New Machine

### Step 1: Create volumes

```
podman volume create poison_elan_home
podman volume create poison_cache_elan
podman volume create poison_cache_lake
```

### Step 2: Install wrapper and symlinks

Ensure `~/bin/poison-dev` exists and is executable.

Create convenient symlinks:

```
ln -sf ~/bin/poison-dev ~/bin/elan
ln -sf ~/bin/poison-dev ~/bin/lean
ln -sf ~/bin/poison-dev ~/bin/lake
```

Make sure `~/bin` is on your PATH.

### Step 3: First run

On a clean machine:

```
elan --version
```

You should see:

```
[entrypoint] Seeding /home/user/.elan from /opt/elan-seed …
```

This happens once per machine.
After that:

```
lean --version
lake build
```

should work without delay.

---

## 7. Updating the Lean Toolchain

To update Lean or install additional toolchains **without rebuilding the container**:

```
elan toolchain install <toolchain>
elan default <toolchain>
```

These operations modify the persistent volume `poison_elan_home`.

---

## 8. Resetting the Environment

If you want to completely wipe persistent state:

```
podman volume rm poison_elan_home poison_cache_elan poison_cache_lake
```

The next invocation of `elan` will trigger a fresh seed copy from the image.

---

## 9. Advantages of This Approach

* **Fast startup** — all heavy work is done at build time.
* **Reproducible builds** — tools come from the pinned container environment.
* **Host independence** — no requirement for host Elan, host Rust, or host Lean.
* **Persistent state** — toolchain updates and caches survive across runs.
* **RHEL/SELinux compatible** — avoids binding host `~/.elan`, which is unreliable on university clusters.
* **Rootless Podman friendly** — safe and stable user namespace integration.

---

## 10. Notes on Original Deployment at Tufts *Quasar* Build Server (RHEL)

This system was originally developed to run on the **Quasar** build server at Tufts University, a RHEL-based cluster environment with several constraints:

### Quasar-specific characteristics

* **Rootless Podman only**, no root privileges.
* **SELinux enforcing**; bind-mount relabeling (`:Z`) is frequently unsupported.
* **Home directories on remote/shared filesystems**, leading to:

  * missing extended attributes,
  * unreliable SELinux label propagation,
  * permission failures for host-mounted Elan directories.
* **RHEL-packaged Rust is too old** for modern `tree-sitter`, requiring rustup inside the image.
* **Large UIDs/GIDs** not present in `/etc/passwd` inside containers, triggering Elan warnings.
* **Firewall and network throttling** during scheduled builds, making runtime toolchain installation undesirable.

### Hardcoded paths and usernames (chosen to satisfy Quasar constraints)

* `user` — the container's internal username.
  Ensures a stable, known home directory structure.

* `/home/user` — container user home.
  Given `chmod 755` to allow traversal by arbitrary UIDs (rootless Podman requirement).

* `/opt/elan-seed` — *read-only system-wide seed* for Elan.
  Installed at image build time.

* `/home/user/.elan` — persistent Elan home (volume-backed).
  Never stored under the host’s `$HOME` to avoid RHEL shared filesystem issues.

* `/home/user/.cache/elan`, `/home/user/.cache/lake` — persistent caches (volume-backed).

* Default project path assumption:
  `~/src/poison-lang`
  Adjustable, but used initially for Quasar's build pipeline layout.

### Why this architecture was chosen for Quasar

* Host binds to `~/.elan` routinely failed under SELinux + rootless Podman.
* RHEL’s system Rust is too old for current Lean/Tree-sitter workflows.
* Running `elan-init` during builds is unreliable due to limited network access.
* Persistent container volumes provide a stable workaround for all these issues.
* Seeding from the image ensures immediate availability without heavy install at runtime.

This container architecture generalises well to other environments, but was specifically engineered to be robust under Quasar’s RHEL constraints.



