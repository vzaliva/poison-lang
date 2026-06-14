#!/usr/bin/env python3
"""Shared helpers for parsing Lean 4 source text.

Centralises comment/string stripping so the reference- and token-counting tools
(``scripts/find_unused_lemmas.py`` and ``scripts/sorry-count.py``) share a
single parser instead of each carrying its own ad hoc one.

Credit: parsing inspired by sorry_analyzer.py from
https://github.com/cameronfreer/lean4-skills/
"""


def strip_lean_comments_and_strings(line: str, block_comment_depth: int) -> tuple[str, int]:
    """Return code-only text for a line and the updated Lean block-comment depth.

    Handles line comments (``--``), nested block comments (``/- -/``) including
    docstrings (``/-- -/``), and string literals. ``block_comment_depth`` carries
    nesting depth across lines; pass ``0`` for the first line of a file.
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


def strip_text(text: str) -> str:
    """Strip comments and string literals from a whole Lean source string.

    Line structure is preserved (newlines kept, stripped spans blanked) so
    line-anchored patterns still behave, while no identifier inside a comment,
    docstring, or string literal survives into the result.
    """
    out: list[str] = []
    depth = 0
    for line in text.splitlines():
        code, depth = strip_lean_comments_and_strings(line, depth)
        out.append(code)
    return "\n".join(out)
