#!/usr/bin/env python3
"""Find lemmas/theorems in LeanProofs that are not referenced by other code."""
import re
import subprocess
from pathlib import Path

LEANPROOFS = Path(__file__).resolve().parent.parent / "LeanProofs"


def extract_lemma_names():
    """Extract lemma/theorem names from Lean files."""
    names = []
    for f in LEANPROOFS.rglob("*.lean"):
        content = f.read_text()
        for m in re.finditer(
            r"^(?:lemma|theorem)\s+([a-zA-Z][a-zA-Z0-9_.'?]*)\b",
            content,
            re.MULTILINE,
        ):
            names.append((str(f.relative_to(LEANPROOFS.parent)), m.group(1)))
    return names


def count_references(name):
    """Count how many times name appears (including definition lookup)."""
    result = subprocess.run(
        ["rg", "-c", rf"\b{re.escape(name)}\b", str(LEANPROOFS), "--glob", "*.lean"],
        capture_output=True,
        text=True,
        cwd=str(LEANPROOFS.parent),
    )
    # rg exits 1 when no matches
    if result.returncode == 1 or not result.stdout:
        return 0
    total = 0
    for line in result.stdout.strip().split("\n"):
        if ":" in line:
            _, count = line.rsplit(":", 1)
            total += int(count)
    return total


def main():
    lemmas = extract_lemma_names()
    print(f"Found {len(lemmas)} lemmas/theorems")
    unused = []
    for rel_path, name in lemmas:
        count = count_references(name)
        if count <= 1:
            unused.append((rel_path, name))
    for rel_path, name in sorted(unused):
        print(f"  {rel_path}: {name}")
    print(f"\nTotal unused: {len(unused)}")


if __name__ == "__main__":
    main()
