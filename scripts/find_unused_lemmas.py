#!/usr/bin/env python3
"""Find declarations in LeanProofs that are not referenced by other code.

Covers private and public lemma/theorem/def/abbrev declarations.
Dotted names (e.g. `X.foo`) are skipped by default because ref-count by
grep cannot detect dot-notation usages like `x.foo` where `x : X`.
Pass --include-dotted to report them anyway.
"""
import argparse
import re
import subprocess
from pathlib import Path

LEANPROOFS = Path(__file__).resolve().parent.parent / "LeanProofs"


def extract_declaration_names():
    """Extract lemma/theorem/def/abbrev names (including private) from Lean files."""
    names = []
    pattern = re.compile(
        r"^(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:lemma|theorem|def|abbrev)\s+"
        r"([a-zA-Z][a-zA-Z0-9_.'?]*)\b",
        re.MULTILINE,
    )
    for f in LEANPROOFS.rglob("*.lean"):
        content = f.read_text()
        for m in pattern.finditer(content):
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--include-dotted",
        action="store_true",
        help="Report dotted names too (may yield false positives from dot notation).",
    )
    args = parser.parse_args()

    decls = extract_declaration_names()
    print(f"Found {len(decls)} declarations")
    unused = []
    skipped_dotted = 0
    for rel_path, name in decls:
        if "." in name and not args.include_dotted:
            skipped_dotted += 1
            continue
        if count_references(name) <= 1:
            unused.append((rel_path, name))
    for rel_path, name in sorted(unused):
        print(f"  {rel_path}: {name}")
    print(f"\nTotal unused: {len(unused)}")
    if skipped_dotted and not args.include_dotted:
        print(f"(skipped {skipped_dotted} dotted names; pass --include-dotted to inspect)")


if __name__ == "__main__":
    main()
