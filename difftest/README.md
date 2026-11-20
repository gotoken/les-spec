# Go oracle verification

English | [日本語](README.ja.md)

`difftest/run.py` runs the Go CLI at the pinned commit and compares stdout and the exit code against the `*.expect.json` with the same name as each `corpus/*.les`. stderr is recorded, but compared exactly only when the expectation specifies `stderr`. **Lean differential tests are not implemented.**

```sh
bash scripts/bootstrap.sh
python3 difftest/run.py
# e.g.: python3 difftest/run.py --timeout 3 --report .work/custom-results.json
```

Expectation JSON:

```json
{"stdout": "30", "exit_code": 0, "stderr": ""}
```

stdin is given as bytes from a `*.stdin` file of the same name if present, otherwise empty. Newlines and whitespace are not normalized; stdout/stderr are compared **exactly as the UTF-8 decoding of the bytes**. The representation will be extended when binary I/O is handled.

Full results are saved to `.work/difftest-results.json`. Only failing cases are passed to the model. Timeouts fail explicitly. Expectations are never updated automatically without approval of the observations.
