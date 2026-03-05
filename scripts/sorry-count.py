#!/usr/bin/env python3
"""
Pre-commit summary: build, count sorry declarations, and report diff of sorry/axiom changes.
Tracks footprint of unproven lemmas. Uses comment-aware parsing (excludes sorry/axiom in
comments and strings). Coloured output: red when sorry/axiom net increased, green when
same or decreased.

Credit: parsing inspired by sorry_analyzer.py from https://github.com/cameronfreer/lean4-skills/

Options:
  -b branchname   Compare current branch to branchname (instead of uncommitted changes)
  --no-build      Skip lake build (only report diff; use when already built)
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

# ANSI colors (disabled when not a TTY)
# 256-color green (38;5;34) for net negative - distinct from yellow
RED = "\033[0;31m" if sys.stdout.isatty() else ""
GREEN = "\033[38;5;34m" if sys.stdout.isatty() else ""
YELLOW = "\033[1;33m" if sys.stdout.isatty() else ""
BOLD = "\033[1m" if sys.stdout.isatty() else ""
ITALIC = "\033[3m" if sys.stdout.isatty() else ""
NC = "\033[0m" if sys.stdout.isatty() else ""

SORRY_TOKEN_PATTERN = re.compile(r"(?<![A-Za-z0-9_!?'])sorry(?![A-Za-z0-9_!?'])")
AXIOM_TOKEN_PATTERN = re.compile(r"(?<![A-Za-z0-9_])axiom(?![A-Za-z0-9_])")


def strip_lean_comments_and_strings(line: str, block_comment_depth: int) -> tuple[str, int]:
    """Return code-only text for a line and updated Lean block-comment depth.

    Handles: line comments (--), nested block comments (/- -/), string literals.
    Adopted from sorry_analyzer.py for accurate counting.
    """
    result: list[str] = []
    i = 0
    n = len(line)
    in_string = False

    while i < n:
        ch = line[i]
        nxt = line[i + 1] if i + 1 < n else ""

        if block_comment_depth > 0:
            if ch == "/" and nxt == "-":
                block_comment_depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_comment_depth -= 1
                i += 2
                continue
            i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            if ch == '"':
                in_string = False
            i += 1
            continue

        if ch == '"' and block_comment_depth == 0:
            in_string = True
            i += 1
            continue

        if ch == "-" and nxt == "-":
            break

        if ch == "/" and nxt == "-":
            block_comment_depth += 1
            i += 2
            continue

        result.append(ch)
        i += 1

    return "".join(result), block_comment_depth


def count_tokens_in_line(line: str, depth: int = 0) -> tuple[int, int, int]:
    """Count sorry and axiom tokens in a line (comment-aware). Returns (sorry_count, axiom_count, new_depth)."""
    code_part, new_depth = strip_lean_comments_and_strings(line, depth)
    sorry_count = len(SORRY_TOKEN_PATTERN.findall(code_part))
    axiom_count = len(AXIOM_TOKEN_PATTERN.findall(code_part))
    return sorry_count, axiom_count, new_depth


def run_lake_build(root: Path) -> tuple[int, str]:
    """Run lake build, return (exit_code, combined stdout+stderr)."""
    result = subprocess.run(
        ["lake", "build"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    output = result.stdout + result.stderr
    return result.returncode, output


def parse_build_sorry_warnings(output: str) -> tuple[list[tuple[str, int]], int]:
    """Parse 'declaration uses \'sorry\'' warnings. Returns ([(file, count), ...], total)."""
    pattern = re.compile(r"^warning:\s+([^:]+):\d+:\d+:.*declaration uses 'sorry'", re.MULTILINE)
    files: dict[str, int] = {}
    for m in pattern.finditer(output):
        f = m.group(1).strip()
        files[f] = files.get(f, 0) + 1
    items = sorted(files.items(), key=lambda x: -x[1])
    return items, sum(files.values())


def get_git_diff(root: Path, compare_branch: str | None) -> str:
    """Get git diff: vs HEAD if no branch, else vs compare_branch."""
    if compare_branch:
        result = subprocess.run(
            ["git", "diff", f"{compare_branch}..HEAD", "--no-color"],
            cwd=root,
            capture_output=True,
            text=True,
        )
    else:
        result = subprocess.run(
            ["git", "diff", "HEAD", "--no-color"],
            cwd=root,
            capture_output=True,
            text=True,
        )
    return result.stdout if result.returncode == 0 else ""


def parse_diff_sorry_axiom(diff: str) -> dict[str, tuple[int, int, int, int]]:
    """Parse diff for added/removed sorry and axiom (comment-aware).
    Returns {file: (add_sorry, rem_sorry, add_axiom, rem_axiom)}.
    """
    data: dict[str, tuple[int, int, int, int]] = {}
    current_file: str | None = None
    diff_file_re = re.compile(r"^diff --git [a-z]/(.+)\s+[a-z]/")

    for line in diff.splitlines():
        m = diff_file_re.match(line)
        if m:
            path = m.group(1).strip()
            current_file = path if path.endswith(".lean") else None
            continue

        if current_file is None:
            continue

        content: str | None = None
        is_add = False
        if line.startswith("+") and not line.startswith("+++"):
            content = line[1:]
            is_add = True
        elif line.startswith("-") and not line.startswith("---"):
            content = line[1:]
            is_add = False

        if content is not None:
            s, a, _ = count_tokens_in_line(content)
            add_s, rem_s, add_a, rem_a = data.get(current_file, (0, 0, 0, 0))
            if is_add:
                add_s += s
                add_a += a
            else:
                rem_s += s
                rem_a += a
            data[current_file] = (add_s, rem_s, add_a, rem_a)

    return data


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Pre-commit summary: build, sorry/axiom counts, and diff report."
    )
    parser.add_argument(
        "-b", "--branch",
        metavar="branchname",
        help="Compare current branch to branchname (instead of uncommitted changes)",
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Skip lake build (only report diff)",
    )
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    root = script_dir.parent

    if args.branch:
        r = subprocess.run(
            ["git", "rev-parse", args.branch],
            cwd=root,
            capture_output=True,
        )
        if r.returncode != 0:
            print(f"{RED}Branch '{args.branch}' not found.{NC}", file=sys.stderr)
            return 1

    # --- 1. Lake build (unless --no-build) ---
    if args.no_build:
        print(f"{ITALIC}Build{NC}: {YELLOW}Skipped{NC}")
        print()
    else:
        exit_code, build_out = run_lake_build(root)
        if exit_code != 0:
            print(f"{ITALIC}Build{NC}: {RED}Failed{NC}")
            print(build_out)
            return 1

        print(f"{ITALIC}Build{NC}: {GREEN}OK{NC}")

        # Parse warnings
        all_warnings = re.findall(r"^warning:", build_out, re.MULTILINE)
        sorry_items, sorry_count = parse_build_sorry_warnings(build_out)
        other_warnings = len(all_warnings) - sorry_count
        if other_warnings > 0:
            print(f"  {YELLOW}Building files emits {other_warnings} warnings (excluding sorry).{NC}")

        print()
        print(f"{ITALIC}--- Lemmas with sorry (from build warnings) ---{NC}")
        if not sorry_items:
            print("  (none)")
            print(f"  {BOLD}Total{NC}: 0")
        else:
            for filepath, count in sorry_items:
                print(f"  {BOLD}{filepath}{NC}: {count}")
            print(f"  {BOLD}Total{NC}: {sorry_count}")
    print()

    # --- 2. Git diff ---
    diff = get_git_diff(root, args.branch)
    diff_label = f"HEAD vs {args.branch}" if args.branch else "vs HEAD"

    print(f"{ITALIC}--- Git diff: sorry/axiom changes ({diff_label}) ---{NC}")
    if not diff.strip():
        no_changes = f"since {args.branch}" if args.branch else ""
        print(f"  No {'uncommitted changes' if not args.branch else 'changes ' + no_changes}.")
        print()
        print("  Total:")
        print("     sorry +0 -0 = +0")
        print("     axiom +0 -0 = +0")
        print("     net: +0")
    else:
        def color_for_net(net: int) -> str:
            if net > 0:
                return RED
            if net == 0:
                return YELLOW
            return GREEN

        diff_data = parse_diff_sorry_axiom(diff)
        tot_add_s = tot_rem_s = tot_add_a = tot_rem_a = 0
        all_files = sorted(diff_data.keys())

        for f in all_files:
            add_s, rem_s, add_a, rem_a = diff_data[f]
            if add_s or rem_s or add_a or rem_a:
                print(f"  {BOLD}{f}{NC}:")
                if add_s or rem_s:
                    net = add_s - rem_s
                    c = color_for_net(net)
                    print(f"    sorry +{add_s} -{rem_s} = {c}{net:+d}{NC}")
                if add_a or rem_a:
                    net = add_a - rem_a
                    c = color_for_net(net)
                    print(f"    axiom +{add_a} -{rem_a} = {c}{net:+d}{NC}")
                tot_add_s += add_s
                tot_rem_s += rem_s
                tot_add_a += add_a
                tot_rem_a += rem_a

        if tot_add_s == 0 and tot_rem_s == 0 and tot_add_a == 0 and tot_rem_a == 0:
            print("  No sorry/axiom changes in diff.")

        net_s = tot_add_s - tot_rem_s
        net_a = tot_add_a - tot_rem_a
        net_total = net_s + net_a
        c_s = color_for_net(net_s)
        c_a = color_for_net(net_a)
        c_total = color_for_net(net_total)
        print()
        print(f"  {BOLD}Total:{NC}")
        print(f"     sorry +{tot_add_s} -{tot_rem_s} = {c_s}{net_s:+d}{NC}")
        print(f"     axiom +{tot_add_a} -{tot_rem_a} = {c_a}{net_a:+d}{NC}")
        print(f"     net: {c_total}{net_total:+d}{NC}")

    print()
    print("Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
