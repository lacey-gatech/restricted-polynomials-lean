#!/usr/bin/env python3
"""Check that no Lean source except the Comparator Challenge contains `sorry`, `admit` or `axiom`.

Comments and string literals are masked first, so a word in a docstring is not a finding. The
Challenge module named in comparator.json may contain `sorry`, the deliberate Comparator hole;
nothing else may. Exit status 1 on any finding.

Usage (from the repository root): python3 scripts/check-no-sorry.py
"""
import json
import re
import sys
from pathlib import Path

FORBIDDEN = re.compile(r"(?<![\w.'])(sorry|admit|axiom|sorryAx)(?![\w'])")


def mask(src: str) -> str:
    """Replace comments and string literals by spaces, keeping line structure."""
    out, i, n, depth, in_str = [], 0, len(src), 0, False
    while i < n:
        c = src[i]
        if depth == 0 and not in_str:
            if src.startswith("--", i):
                j = src.find("\n", i)
                j = n if j < 0 else j
                out.append(" " * (j - i))
                i = j
                continue
            if src.startswith("/-", i):
                depth, i = 1, i + 2
                out.append("  ")
                continue
            if c == '"':
                in_str = True
                out.append(" ")
                i += 1
                continue
            out.append(c)
            i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " ")
            i += 1
        else:
            if src.startswith("/-", i):
                depth, i = depth + 1, i + 2
                out.append("  ")
            elif src.startswith("-/", i):
                depth, i = depth - 1, i + 2
                out.append("  ")
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
    return "".join(out)


def main() -> int:
    root = Path.cwd()
    config = json.loads((root / "comparator.json").read_text(encoding="utf-8"))
    challenge = root / (config["challenge_module"].replace(".", "/") + ".lean")
    findings = []
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts or ".git" in path.parts:
            continue
        text = mask(path.read_text(encoding="utf-8"))
        for number, line in enumerate(text.splitlines(), 1):
            for match in FORBIDDEN.finditer(line):
                word = match.group(1)
                if path == challenge and word == "sorry":
                    continue
                findings.append(f"{path.relative_to(root)}:{number}: {word}")
    challenge_holes = len(FORBIDDEN.findall(mask(challenge.read_text(encoding="utf-8"))))
    print("\n".join(findings))
    print(f"{len(findings)} finding(s); {challenge_holes} deliberate hole(s) in {challenge.name}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
