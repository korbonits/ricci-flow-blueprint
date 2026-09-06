#!/usr/bin/env python3
"""Verify that every declaration the blueprint points at (`\\lean{...}`) depends only on
the standard axioms, and that the project declares no axioms of its own.

Run from the project root after `lake build`:

    python3 scripts/check_axioms.py

Exit status is nonzero on any failure. `checkdecls` already verifies that the names
exist; this script verifies what they rest on.
"""
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    ok = True

    # 1. No `axiom` declarations in the project sources.
    for path in sorted((ROOT / "RicciFlowBlueprint").rglob("*.lean")):
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if re.match(r"\s*(@\[[^\]]*\]\s*)?(private\s+|protected\s+)?axiom\b", line):
                print(f"::error file={path},line={lineno}::axiom declaration: {line.strip()}")
                ok = False

    # 2. Every `\lean{}` name in the blueprint depends only on the standard axioms.
    tex = (ROOT / "blueprint" / "src" / "content.tex").read_text()
    names = []
    for match in re.finditer(r"\\lean\{([^}]*)\}", tex):
        names.extend(n.strip() for n in match.group(1).split(",") if n.strip())
    names = sorted(set(names))
    if not names:
        print("::error::no \\lean{} names found in blueprint/src/content.tex")
        return 1

    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write("import RicciFlowBlueprint\n")
        for name in names:
            f.write(f"#print axioms {name}\n")
        check = pathlib.Path(f.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(check)], cwd=ROOT, capture_output=True, text=True
        )
    finally:
        check.unlink()
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(out)
        print(f"::error::lake env lean failed with exit code {proc.returncode}")
        return 1

    # `#print axioms` output may wrap the list across lines: join and parse.
    text = re.sub(r"\s+", " ", out)
    seen = set()
    for match in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
        name = match.group(1)
        seen.add(name)
        axioms = {a.strip() for a in (match.group(3) or "").split(",") if a.strip()}
        bad = axioms - ALLOWED
        if bad:
            print(f"::error::{name} depends on non-standard axioms: {sorted(bad)}")
            ok = False
    missing = [n for n in names if n not in seen]
    if missing:
        print(f"::error::no `#print axioms` output for: {missing}")
        print(out)
        ok = False

    print(f"checked {len(names)} declarations; "
          f"{'all standard' if ok else 'FAILURES above'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
