import Les.Eval.Eval

/- Go CLI の観測と同じ形（docs/evaluator-design.md 5 節、difftest の expect.json）に正規化する。 -/
namespace Les.Eval

structure Observed where
  stdout : String
  stderr : String
  exitCode : Int
  deriving Repr, BEq

/-- 比較の結論。`unsupported` と `outOfFuel` は PASS にならない。 -/
inductive Verdict where
  | observed (o : Observed)
  | unsupported (what : String)
  | outOfFuel
  | internal (msg : String)
  deriving Repr

def Outcome.verdict (o : Outcome) : Verdict :=
  match o.halt with
  | none => .observed { stdout := o.stdout, stderr := "", exitCode := 0 }
  | some (.exit c) => .observed { stdout := o.stdout, stderr := "", exitCode := c }
  | some (.error msg (.at p)) =>
    .observed { stdout := o.stdout, exitCode := 1,
                stderr := s!"Runtime Error: <CASE>:{p.line}: {msg} at col {p.col}\n" }
  | some (.error msg .absent) =>
    .observed { stdout := o.stdout, exitCode := 1, stderr := s!"Runtime Error: {msg}\n" }
  | some (.error msg .pending) => .internal s!"pending position escaped run: {msg}"
  | some (.unsupported w) => .unsupported w
  | some .outOfFuel => .outOfFuel

end Les.Eval
