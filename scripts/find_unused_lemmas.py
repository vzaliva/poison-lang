#!/usr/bin/env python3
"""Find declarations in LeanProofs that are not referenced by other code.

Covers private and public lemma/theorem/def/abbrev declarations.

References are counted over *code-only* text: line comments (``--``), nested
block comments (``/- -/``) including docstrings (``/-- -/``), and string
literals are stripped before matching names (shared parser in ``lean_text``).
Without this, a declaration mentioned only in prose would look referenced and
be wrongly hidden from the unused report.

Dotted names (e.g. ``X.foo``) are included by default. Ref-count by substring
match cannot detect dot-notation usages like ``x.foo`` where ``x : X``, so
pass --skip-dotted to omit them and avoid false positives.
"""
import argparse
import re
from pathlib import Path

from lean_text import strip_text

LEANPROOFS = Path(__file__).resolve().parent.parent / "LeanProofs"

DECL_PATTERN = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:lemma|theorem|def|abbrev)\s+"
    r"([a-zA-Z][a-zA-Z0-9_.'?]*)\b",
    re.MULTILINE,
)


def find_declarations(code_text):
    """Return declaration names found in (already code-only) Lean text."""
    return [m.group(1) for m in DECL_PATTERN.finditer(code_text)]


def count_references(name, code_text):
    """Count whole-word occurrences of name in code-only text (incl. definition)."""
    return len(re.findall(rf"\b{re.escape(name)}\b", code_text))


def collect_declarations():
    """Walk LeanProofs once. Return ([(rel_path, name), ...], combined_code_text).

    Both declaration extraction and the reference corpus use comment/string
    stripped text so the two views stay consistent (a commented-out declaration
    is neither extracted nor counted).
    """
    decls = []
    code_chunks = []
    for f in sorted(LEANPROOFS.rglob("*.lean")):
        code = strip_text(f.read_text())
        rel = str(f.relative_to(LEANPROOFS.parent))
        for name in find_declarations(code):
            decls.append((rel, name))
        code_chunks.append(code)
    return decls, "\n".join(code_chunks)


def compute_unused(decls, code_text, skip_dotted=False):
    """Return (unused, skipped_dotted) given declarations and the code corpus.

    A declaration is unused when its only whole-word occurrence in code is its
    own definition (reference count <= 1).
    """
    unused = []
    skipped_dotted = 0
    for rel_path, name in decls:
        if "." in name and skip_dotted:
            skipped_dotted += 1
            continue
        if count_references(name, code_text) <= 1:
            unused.append((rel_path, name))
    return unused, skipped_dotted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-dotted",
        action="store_true",
        help="Omit dotted names (avoids false positives from dot notation).",
    )
    args = parser.parse_args()

    decls, code_text = collect_declarations()
    print(f"Found {len(decls)} declarations")
    unused, skipped_dotted = compute_unused(decls, code_text, args.skip_dotted)
    for rel_path, name in sorted(unused):
        print(f"  {rel_path}: {name}")
    print(f"\nTotal unused: {len(unused)}")
    if skipped_dotted:
        print(f"(skipped {skipped_dotted} dotted names)")


if __name__ == "__main__":
    main()
