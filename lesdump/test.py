#!/usr/bin/env python3
"""lesdump tests: golden output for difftest/corpus, determinism, explicit errors.

Usage: python3 lesdump/test.py [--update]   (--update rewrites lesdump/golden/*.json)
Requires .work/bin/lesdump (build: cd lesdump && go build -o ../.work/bin/lesdump .).
"""
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
BIN = ROOT / ".work" / "bin" / "lesdump"
CORPUS = ROOT / "difftest" / "corpus"
GOLDEN = ROOT / "lesdump" / "golden"


def run(path):
    return subprocess.run([str(BIN), str(path)], capture_output=True, text=True)


def main():
    update = "--update" in sys.argv
    if not BIN.is_file():
        sys.exit(f"missing {BIN}; build it first")
    failures = []
    GOLDEN.mkdir(exist_ok=True)
    cases = sorted(CORPUS.glob("*.les"))
    for case in cases:
        a, b = run(case), run(case)
        gold = GOLDEN / (case.stem + ".json")
        if a.returncode != 0:
            failures.append(f"{case.name}: exit {a.returncode}: {a.stderr.strip()}")
        elif a.stdout != b.stdout:
            failures.append(f"{case.name}: output differs between two runs")
        elif update:
            gold.write_text(a.stdout, encoding="utf-8")
        elif not gold.is_file() or gold.read_text(encoding="utf-8") != a.stdout:
            failures.append(f"{case.name}: differs from {gold.name}")
    # Same content at a different path must give identical output (no absolute paths in JSON).
    with tempfile.TemporaryDirectory() as d:
        copy = pathlib.Path(d) / "elsewhere.les"
        src = CORPUS / "force-basic.les"
        copy.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        if run(copy).stdout != run(src).stdout:
            failures.append("output depends on file path")
        # Explicit errors: unsupported nodes and syntax errors exit 2 with a message, no JSON.
        for name, code, needle in [
            ("float", "x = 1.5\n", "unsupported: *ast.FloatLit"),
            ("if", "if true:\n    print 1\n", "unsupported: *ast.IfStmt"),
            ("syntax", "print (\n", "syntax error"),
        ]:
            f = pathlib.Path(d) / (name + ".les")
            f.write_text(code, encoding="utf-8")
            r = run(f)
            if r.returncode != 2 or needle not in r.stderr or r.stdout:
                failures.append(f"{name}: expected exit 2 with {needle!r}, got {r.returncode} {r.stderr.strip()!r}")
        # Regression (review P2): a short relative file name that also occurs in a diagnostic
        # ("Int" in "expected Int, got String") must not change the output or the message text.
        src_text = 'def f(x: Int): Int:\n    x\n\nprint f("a")\n'
        (pathlib.Path(d) / "Int").write_text(src_text, encoding="utf-8")
        (pathlib.Path(d) / "abs.les").write_text(src_text, encoding="utf-8")
        rel = subprocess.run([str(BIN), "Int"], capture_output=True, text=True, cwd=d)
        ab = run(pathlib.Path(d) / "abs.les")
        if rel.returncode != 0 or rel.stdout != ab.stdout:
            failures.append("relative file name 'Int' gives different JSON than absolute path")
        if "expected Int, got String" not in rel.stdout:
            failures.append("diagnostic text was rewritten (expected 'expected Int, got String')")
        # Type errors are reported in analysis (as the CLI does), with the path scrubbed.
        f = pathlib.Path(d) / "typeerr.les"
        f.write_text('def f(x: Int): Int:\n    x\n\nprint f("a")\n', encoding="utf-8")
        r = run(f)
        if r.returncode != 0 or '"status": "type_error"' not in r.stdout or d in r.stdout or "<FILE>:4" not in r.stdout:
            failures.append("type error not reported as expected in analysis")
    for f in failures:
        print("FAIL", f)
    print(f"{len(cases)} corpus cases; {'updated' if update else 'checked'}; {len(failures)} failure(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
