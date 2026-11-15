#!/usr/bin/env python3
"""Pinned Go CLI oracle: compare corpus observations without changing expectations."""
import argparse
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
CORPUS = ROOT / "difftest" / "corpus"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--les", type=pathlib.Path, default=ROOT / ".work" / "bin" / "les")
    parser.add_argument("--report", type=pathlib.Path, default=ROOT / ".work" / "difftest-results.json")
    parser.add_argument("--timeout", type=float, default=5.0)
    args = parser.parse_args()
    les = args.les.resolve()
    if not les.is_file():
        parser.error(f"Go CLI missing: {les}; first run bash scripts/bootstrap.sh")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    cases = sorted(CORPUS.glob("*.les"))
    if not cases:
        parser.error("no *.les cases")
    results = []
    for case in cases:
        expected_file = case.with_suffix(".expect.json")
        if not expected_file.is_file():
            parser.error(f"missing expectation: {expected_file}")
        expected = json.loads(expected_file.read_text(encoding="utf-8"))
        if "stdout" not in expected or "exit_code" not in expected:
            parser.error(f"invalid expectation: {expected_file}")
        stdin_file = case.with_suffix(".stdin")
        data = stdin_file.read_bytes() if stdin_file.exists() else b""
        try:
            run = subprocess.run(
                [str(les), str(case)], input=data,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=args.timeout, cwd=ROOT, check=False
            )
            stdout = run.stdout.decode("utf-8", errors="replace")
            # Absorb the machine-specific absolute path; "<CASE>" stands for the case file.
            stderr = run.stderr.decode("utf-8", errors="replace").replace(str(case), "<CASE>")
            exit_code = run.returncode
            diffs = []
            if stdout != expected["stdout"]:
                diffs.append("stdout")
            if exit_code != expected["exit_code"]:
                diffs.append("exit_code")
            if "stderr" in expected and stderr != expected["stderr"]:
                diffs.append("stderr")
            item = {
                "case": case.name, "ok": not diffs, "diffs": diffs,
                "expected": expected, "actual": {
                    "stdout": stdout, "stderr": stderr, "exit_code": exit_code
                }
            }
        except subprocess.TimeoutExpired as exc:
            item = {
                "case": case.name, "ok": False, "diffs": ["timeout"],
                "expected": expected, "actual": {
                    "timeout_seconds": args.timeout,
                    "stdout_prefix": (exc.stdout or b"").decode("utf-8", errors="replace"),
                    "stderr_prefix": (exc.stderr or b"").decode("utf-8", errors="replace")
                }
            }
        results.append(item)
        print(f'{"PASS" if item["ok"] else "FAIL"} {case.name}: {", ".join(item["diffs"]) or "matched"}')
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(
        json.dumps({"upstream_commit": (ROOT / "upstream" / "LES_COMMIT").read_text().strip(),
                    "results": results}, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8"
    )
    passed = sum(x["ok"] for x in results)
    print(f"{passed}/{len(results)} passed. Full report: {args.report}")
    return 0 if passed == len(results) else 1


if __name__ == "__main__":
    sys.exit(main())
