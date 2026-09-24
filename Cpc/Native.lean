module

public import Cpc.Api
import all Cpc.Api

@[expose] public section

/-!
# What the `logos-native` executable computes

`Cpc/Api.lean` is the pipeline of the `logos` executable, from the text of an
s-expression proof file to a `Verdict`.  This module is the API of the secondary,
experimental front end (`MainNative.lean`, `docs/lean-native-proofs.md`), whose
input is a Lean script that builds a proof state one command at a time and
evaluates a predicate on it:

```
def s0 : LogosState := logos_init_state
def s1 : LogosState := (logos_invoke_assume s0 t4)
def s2 : LogosState := (logos_invoke_cmd s1 (CCmd.step ...))
#eval!
(logos_state_is_refutation s2)
```

The two front ends differ only in where the assumptions and the commands come
from: `logos` gets them from `Cpc/Parser.lean`, and here the script names them
one call at a time.  Everything downstream of that is the same, and is meant to
stay the same -- the three checks of `logos_verdict` are run here too, on the
same definitions:

| component of `correct___eo_is_refutation` | in `logos_verdict`                       | here                     |
| ----------------------------------------- | ---------------------------------------- | ------------------------ |
| `eo_is_refutation F pf`                   | `logos_check_refutation`                 | `LogosState.state`       |
| `TranslatableAssumptionList F`            | `logos_check_translatableAssumptionList` | `LogosState.translationOk` |
| `CmdListTranslationOk pf`                 | `logos_check_cmdListTranslationOk`       | `LogosState.translationOk` |

`logos_state_verdict_eq_verdict` below proves that a script of the shape above
computes exactly `logos_verdict` of the assumptions and commands it names, and
`correct___logos_state_is_refutation` (`Cpc/Native/Correct.lean`) turns that into
the soundness statement.  What the script's *shape* is remains unchecked, and is
the counterpart here of the unverified parser on the `logos` side.

`LogosState` is the whole interface: a script never names `CState`, or anything
else internal to the checker.  These definitions used to be generated into
`Cpc/Logos.lean`, where they were `CState` operations that ran the checker alone.
They are hand-written here because the checks are: `Cpc/Logos.lean` is compiled
from the calculus and knows nothing of `Cpc/SmtModel.lean`, which deciding the
side conditions needs.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The state a script threads

A checker state, plus the running conjunction of the translation side conditions
of the assumptions and commands that built it.  The checker state alone is what
the generated API used to thread; the extra field is what lets the two side
conditions of `correct___eo_is_refutation` be decided as the script goes, without
it having to hand back the list of everything it has done.
-/
structure LogosState where
  /-- The checker state, as `__eo_invoke_cmd_list` would have built it. -/
  state : CState
  /-- Every assumption and command so far satisfies its translation side condition. -/
  translationOk : Bool
deriving Repr, Inhabited

/-- The empty state: no assumptions, no commands, nothing yet to translate. -/
def logos_init_state : LogosState :=
  { state := logos_checker_init_state, translationOk := true }

/--
Push one input assumption, checking it exactly as `logos` checks a parsed one.

`logos_invoke_input_assume` (`Cpc/Api.lean`) applies the well-formedness guard
that `__eo_invoke_assume_list` applies -- the assumption must be Boolean-typed and
closed, or the state goes `Stuck` -- and that guard is what `checkerTypeInvariant`
and `StableAssumptionList` need.  `decide (eoHasSmtTranslation A)` is the same
check `logos_check_translatableAssumptionList` makes of each parsed assumption.
-/
def logos_invoke_assume (s : LogosState) (A : Term) : LogosState :=
  { state := logos_invoke_input_assume s.state A,
    translationOk := s.translationOk && decide (eoHasSmtTranslation A) }

/--
Run one checker command, checking it exactly as `logos` checks a parsed one.

`decide (cmdTranslationOk c)` is the per-command half of
`logos_check_cmdListTranslationOk`, decided by the same instance of
`Cpc/Proofs/Assumptions.lean`, so the per-rule masks the rule proofs assume are
checked here too.
-/
def logos_invoke_cmd (s : LogosState) (c : CCmd) : LogosState :=
  { state := __eo_invoke_cmd s.state c,
    translationOk := s.translationOk && decide (cmdTranslationOk c) }

/-- The verdict for a state a script built: `logos_verdict`, read off the state. -/
def logos_state_verdict (s : LogosState) : Verdict :=
  if !__eo_state_is_refutation s.state then Verdict.incorrect
  else if !s.translationOk then Verdict.incomplete
  else Verdict.correct

/--
What a script evaluates: `true` exactly when the verdict is `correct`, which is
when `correct___logos_state_is_refutation` applies to it.

The `incorrect`/`incomplete` distinction the `logos` executable reports is
available from `logos_state_verdict`; a script reduced to one Boolean cannot show
it, so a proof Logos accepts but cannot translate reads as `false` here.
-/
def logos_state_is_refutation (s : LogosState) : Bool :=
  logos_state_verdict s == Verdict.correct

/-! ## The shape a script is assumed to have

Nothing checks that a script builds its state this way; `MainNative.lean`
elaborates whatever the file says.  These definitions are what the theorems below
are stated about, and they are what the scripts under `test/regress/*.cpc.lean`
(and the ones cvc5 emits) do write.
-/

/-- Run a list of commands from a state, as a script's `logos_invoke_cmd` calls do. -/
def logos_invoke_cmd_list (s : LogosState) : CCmdList -> LogosState
  | CCmdList.nil => s
  | CCmdList.cons c cmds => logos_invoke_cmd_list (logos_invoke_cmd s c) cmds

/-- The state a script that assumes `assums` and then runs `cmds` ends in. -/
def logos_run (assums : List Term) (cmds : CCmdList) : LogosState :=
  logos_invoke_cmd_list (assums.foldl logos_invoke_assume logos_init_state) cmds

/-! ## A script computes `logos_verdict`

Each field is tracked separately: the checker state is the one
`logos_check_refutation` folds, and the flag is the conjunction of the two
translation checks.
-/

private theorem state_foldl_assume (assums : List Term) :
    ∀ s : LogosState,
      (assums.foldl logos_invoke_assume s).state
        = assums.foldl logos_invoke_input_assume s.state := by
  induction assums with
  | nil => intro s; rfl
  | cons A assums ih => intro s; rw [List.foldl_cons, ih, List.foldl_cons]; rfl

private theorem translationOk_foldl_assume (assums : List Term) :
    ∀ s : LogosState,
      (assums.foldl logos_invoke_assume s).translationOk
        = (s.translationOk && logos_check_translatableAssumptionList assums) := by
  induction assums with
  | nil => intro s; simp [logos_check_translatableAssumptionList]
  | cons A assums ih =>
    intro s
    rw [List.foldl_cons, ih]
    simp [logos_invoke_assume, logos_check_translatableAssumptionList, Bool.and_assoc]

private theorem state_invoke_cmd_list :
    ∀ (cmds : CCmdList) (s : LogosState),
      (logos_invoke_cmd_list s cmds).state = __eo_invoke_cmd_list s.state cmds := by
  intro cmds
  induction cmds with
  | nil => intro s; rfl
  | cons c cmds ih => intro s; rw [logos_invoke_cmd_list, ih]; rfl

/-- `CmdListTranslationOk` of a `cons` splits, so `decide` of it splits too. -/
private theorem check_cmdListTranslationOk_cons (c : CCmd) (cmds : CCmdList) :
    logos_check_cmdListTranslationOk (CCmdList.cons c cmds)
      = (decide (cmdTranslationOk c) && logos_check_cmdListTranslationOk cmds) := by
  rw [Bool.eq_iff_iff]
  simp only [logos_check_cmdListTranslationOk, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h; cases h with | cons _ _ hc hcs => exact ⟨hc, hcs⟩
  · intro h; exact CmdListTranslationOk.cons c cmds h.1 h.2

private theorem translationOk_invoke_cmd_list :
    ∀ (cmds : CCmdList) (s : LogosState),
      (logos_invoke_cmd_list s cmds).translationOk
        = (s.translationOk && logos_check_cmdListTranslationOk cmds) := by
  intro cmds
  induction cmds with
  | nil =>
    intro s
    simp [logos_invoke_cmd_list, logos_check_cmdListTranslationOk, CmdListTranslationOk.nil]
  | cons c cmds ih =>
    intro s
    rw [logos_invoke_cmd_list, ih, check_cmdListTranslationOk_cons]
    simp [logos_invoke_cmd, Bool.and_assoc]

/--
A script that assumes `assums` and then runs `cmds` reports exactly what `logos`
reports for the same assumptions and commands.
-/
theorem logos_state_verdict_eq_verdict (assums : List Term) (cmds : CCmdList) :
    logos_state_verdict (logos_run assums cmds) = logos_verdict assums cmds := by
  have hstate : (logos_run assums cmds).state
      = __eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_checker_init_state) cmds := by
    rw [logos_run, state_invoke_cmd_list, state_foldl_assume]; rfl
  have hok : (logos_run assums cmds).translationOk
      = (logos_check_translatableAssumptionList assums
          && logos_check_cmdListTranslationOk cmds) := by
    rw [logos_run, translationOk_invoke_cmd_list, translationOk_foldl_assume]
    simp [logos_init_state]
  unfold logos_state_verdict logos_verdict logos_check_refutation
  rw [hstate, hok]
  cases __eo_state_is_refutation
      (__eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_checker_init_state) cmds) <;>
    cases logos_check_translatableAssumptionList assums <;>
      cases logos_check_cmdListTranslationOk cmds <;> rfl

/-- `logos_state_is_refutation` is the verdict being `correct`. -/
theorem logos_state_is_refutation_eq_correct (s : LogosState) :
    logos_state_is_refutation s = true ↔ logos_state_verdict s = Verdict.correct := by
  simp [logos_state_is_refutation]

end Eo
