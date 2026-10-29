import Cpc.Diagnostics

/-!
The `logos` executable: read a CPC proof in s-expression syntax, and report
whether it is a refutation whose soundness `Cpc/ApiCorrect.lean` establishes.

Reading the file aside, all of the work is `Eo.logos_check_proof`
(`Cpc/Api.lean`): it parses the text and runs the three checks that make up
`correct___eo_is_refutation`.  `correct___logos_check_proof`
(`Cpc/ApiCorrect.lean`) is stated about that function:

```
theorem correct___logos_check_proof (input : String) (assums : List Term) (cmds : CCmdList)
    (hParse : parseProof input = Except.ok (assums, cmds))
    (hCorrect : logos_check_proof input = Except.ok Verdict.correct) :
    ∀ M : SmtModel, model_wf M ->
      ∃ A ∈ assums, __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false
```

So `correct` on the terminal means: the formulas this file `assume`s, as the
parser read them, are unsatisfiable -- every well-formed model makes one of them
`false`.

When Logos accepts the proof but a side condition fails, the run is reported as
`incomplete` instead: the proof is a valid CPC derivation, but it mentions
something the specification does not model, so the theorem says nothing about
it.

The verdict is computed here in the two steps `Eo.logos_check_proof` is defined
as -- parse, then `Eo.logos_verdict` -- so that the `incomplete` case can name
the assumption or command at fault; `Eo.logos_check_proof_of_parse`
(`Cpc/ApiChecks.lean`) is the identity of the two.
-/

open Eo

def Eo.Verdict.word : Verdict -> String
  | .correct => "correct"
  | .incorrect => "incorrect"
  | .incomplete => "incomplete"

def Eo.Verdict.status : Verdict -> UInt32
  | .correct => 0
  | .incorrect => 1
  | .incomplete => 2

/--
Report a verdict: the detail goes to stderr first and is flushed, so that a
caller merging the two streams still sees the verdict as the final line.
-/
def report (verdict : Verdict) (detail : String := "") : IO UInt32 := do
  if !detail.isEmpty then
    let err ← IO.getStderr
    err.putStrLn detail
    err.flush
  let out ← IO.getStdout
  out.putStrLn verdict.word
  out.flush
  return verdict.status

/-- Keep diagnostics readable when the offending term is large. -/
def abbreviate (s : String) : String :=
  if s.length ≤ 400 then s else String.ofList (s.toList.take 400) ++ " ..."

/--
Why a proof Logos accepted is nevertheless outside the fragment the correctness
theorem covers: the first assumption or command that fails its side condition.
-/
def incompleteDetail (assums : List Term) (cmds : CCmdList) : String :=
  match Eo.logos_untranslatable_assumption assums with
  | some (i, A) =>
    s!"Error: assumption {i} has no SMT-LIB translation, so this proof is \
       outside the fragment the correctness theorem covers:\n  \
       {abbreviate (toString (repr A))}"
  | none =>
    match Eo.logos_untranslatable_cmd cmds with
    | some (i, c) =>
      s!"Error: the arguments of command {i} have no SMT-LIB translation, so this \
         proof is outside the fragment the correctness theorem covers:\n  \
         {abbreviate (toString (repr c))}"
    | none => "Error: a translation side condition failed."

def checkProof (path : String) : IO UInt32 := do
  let proof ← IO.FS.readFile path
  match Eo.parseProof proof with
  | .ok (assums, cmds) =>
    match Eo.logos_verdict assums cmds with
    | .correct => report .correct
    | .incorrect => report .incorrect (Eo.logos_checker_failure_detail proof assums cmds)
    | .incomplete => report .incomplete (incompleteDetail assums cmds)
  | .error err =>
    IO.eprintln s!"Error parsing proof: {err}"
    return 1

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: logos <path-to-proof-file>"
      return 1
  checkProof path

-- To build, run "lake build logos" in this directory.
-- To run, use "lake exe logos <path-to-proof-file>".
