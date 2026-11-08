#!/usr/bin/env python3
"""Enumerate 'method sentences' in the gate's own sources, with a denominator.

codec-drift-closure §3.1, design D3 step 1. A *method sentence* is prose that
states HOW a check works — a scope ("every ..."), an ordering ("longest first"),
a comparison ("what lake build does"), or a path ("grep -rn ... Codec/"). Round
nine's review found five false ones, so this script is the enumeration that the
audit's completeness claim rests on.

## The three numbers this reports (codec-gate-denominators discipline)

1. **lines scanned** — the denominator: every comment/prose line in the audited
   files.
2. **lines matched** — by the marker vocabulary below.
3. **the vocabulary's own denominator** — the marker list is itself a filter, so
   the count of *distinct markers* and which of them fire is printed. A marker
   that never fires is dead vocabulary, and dead vocabulary is what made round
   nine's footprint arm blind to 22 docstrings.

This script ENUMERATES; it does not judge. The classification (assertable /
scope / unassertable) is recorded in tasks.md §3.2-3.5, because that judgement
is prose about prose and cannot be mechanised without answering itself.
"""
import re
import sys

# The files the audit covers. `Codec/*.lean` is deliberately NOT here: those are
# law docstrings adjudicated by the footprint arm, and including them would put
# 4000 lines of proof commentary in a denominator that no human will audit.
# README.md is included because the one live scope defect this audit found
# (`grep -rn decodeWholeOne Codec/` "shows exactly those two laws") lived there,
# not in the gate sources — an audit corpus that excludes the document the claims
# are written in would have reported a clean run on a false sentence.
FILES = ["Axioms.lean", "flake.nix", "Bench.lean", "scripts/gen-axioms.lean",
         "scripts/gen-readme-gate.sh", "README.md"]

# One vocabulary, used by every reader (the lesson from review P2-A4: three
# copies of a list is how drift happens).
MARKERS = [
    ("scope-every",   re.compile(r"\bevery\b", re.I)),
    ("scope-all",     re.compile(r"\ball\b", re.I)),
    ("scope-only",    re.compile(r"\bonly\b", re.I)),
    ("ordering",      re.compile(r"\bin order\b|\blast\b|\bfirst\b|\bthen\b", re.I)),
    ("ordering-longest", re.compile(r"\blongest\b", re.I)),
    ("path-grep",     re.compile(r"\bgrep\b", re.I)),
    ("path-grep-rn",  re.compile(r"grep\s+-[a-z]*r", re.I)),
    ("path-literal",  re.compile(r"(?<![\w/])(Codec|Bench|scripts|openspec)/[\w./]+")),
    ("comparison",    re.compile(r"\bis what\b|\bdoes the same\b|\bmirrors?\b|\bmatches?\b", re.I)),
]


def comment_lines(path):
    """Yield (lineno, text) for lines that are *prose* in the given source.

    Lean: lines inside `/- ... -/` or `--`. Nix/bash: `#`. This is the filter
    that decides what enters the audit, so it is stated rather than implied —
    and it is deliberately generous in the Lean case (any line of a block
    comment) because a method sentence does not have to start with `--`.
    """
    out = []
    in_block = False
    depth = 0
    for n, line in enumerate(open(path, encoding="utf-8").read().split("\n"), 1):
        s = line.strip()
        if path.endswith(".lean"):
            if in_block:
                out.append((n, line))
                if "-/" in s:
                    in_block = False
                continue
            if s.startswith("/-"):
                out.append((n, line))
                # nest-count: Lean block comments nest
                depth = s.count("/-") - s.count("-/")
                in_block = depth > 0
                continue
            if s.startswith("--") or s.startswith("*") or s.startswith("|"):
                out.append((n, line))
        elif path.endswith(".md"):
            # Markdown: ALL prose is prose. Only fenced code blocks are skipped,
            # because a `grep` shown inside a ``` block is an example, not a claim
            # about what a check does.
            if s.startswith("```"):
                in_block = not in_block
                continue
            if not in_block and s:
                out.append((n, line))
        else:
            if s.startswith("#"):
                out.append((n, line))
    return out


def main():
    total = 0
    per_file = {}
    hits = []
    fired = {}
    for f in FILES:
        lines = comment_lines(f)
        per_file[f] = len(lines)
        total += len(lines)
        for n, text in lines:
            names = [name for name, rx in MARKERS if rx.search(text)]
            for name in names:
                fired[name] = fired.get(name, 0) + 1
            if names:
                hits.append((f, n, names, text.strip()))

    print(f"method-sentence audit — denominator: {total} prose lines scanned "
          f"across {len(FILES)} files")
    for f, c in per_file.items():
        print(f"  {c:5d}  {f}")
    print(f"matched: {len(hits)} line(s)")
    print(f"vocabulary: {len(MARKERS)} markers declared, "
          f"{len(fired)} fire")
    dead = [name for name, _ in MARKERS if name not in fired]
    if dead:
        print(f"  DEAD MARKERS (never fire — widen or delete): {dead}")
    print("\nper-marker:")
    for name, _ in MARKERS:
        print(f"  {fired.get(name, 0):5d}  {name}")
    print("\n--- matched lines ---")
    for f, n, names, text in hits:
        print(f"{f}:{n}: [{','.join(names)}] {text[:160]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
