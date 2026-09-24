module

public import Cpc.Api
import all Cpc.Api
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions

@[expose] public section

/-!
# The checks in `Cpc/Api.lean` are the components of `correct___eo_is_refutation`

`Cpc/Api.lean` computes four things from the parser's output; this module proves
that each one means what its name claims, against the definitions the soundness
proof actually uses.

| computed in `Cpc/Api.lean`                 | proved here to give              |
| ------------------------------------------ | -------------------------------- |
| `logos_check_refutation assums cmds`        | `eo_is_refutation F cmds`        |
| `logos_check_translatableAssumptionList`    | `TranslatableAssumptionList F`   |
| `logos_check_cmdListTranslationOk`          | `CmdListTranslationOk cmds`      |

throughout with `F = logos_assumption_arglist assums`.  `Cpc/ApiCorrect.lean`
feeds these into `correct___eo_is_refutation`.

Only the direction soundness needs is proved -- a check that returned `true` too
rarely would only reject proofs the theorem would not have covered anyway.

This module deliberately does not import the checker correctness proof, so that
it stays cheap enough to build in CI.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The refutation check computes `eo_is_refutation`

`__eo_invoke_assume_list` walks a `CArgList` and pushes each entry with the
guard `(and (is_bool_type A) (is_closed A))`.  `logos_check_refutation` folds
`logos_invoke_input_assume` over the parser's list instead, which applies the
same guard in the same order with no stack growth.  These lemmas prove the two
agree, so that the executable's check is literally the theorem's hypothesis.
-/

/-- Generalized over the accumulator, so the induction goes through. -/
private theorem invoke_assume_list_foldl (assums : List Term) :
    ∀ (rest : CArgList) (S : CState),
      __eo_invoke_assume_list S (assums.foldl logos_assumption_list_step rest)
        = assums.foldl logos_invoke_input_assume (__eo_invoke_assume_list S rest) := by
  induction assums with
  | nil => intro rest S; rfl
  | cons A assums ih =>
    intro rest S
    rw [List.foldl_cons, ih, List.foldl_cons]
    congr 1

/--
Folding the guarded push over the parser's assumptions builds exactly the state
`__eo_invoke_assume_list` builds from the corresponding `CArgList`.
-/
theorem invoke_assume_list_eq_fold (assums : List Term) :
    __eo_invoke_assume_list logos_checker_init_state (logos_assumption_arglist assums)
      = assums.foldl logos_invoke_input_assume logos_checker_init_state := by
  simpa [logos_assumption_arglist, logos_checker_init_state, __eo_invoke_assume_list]
    using invoke_assume_list_foldl assums CArgList.nil logos_checker_init_state

/-- The executable's refutation check is the generated `__eo_checker_is_refutation`. -/
theorem logos_check_refutation_eq_checker (assums : List Term) (cmds : CCmdList) :
    logos_check_refutation assums cmds
      = __eo_checker_is_refutation (logos_assumption_arglist assums) cmds := by
  unfold logos_check_refutation __eo_checker_is_refutation
  rw [← invoke_assume_list_eq_fold]
  rfl

/-- `logos_check_refutation` returning `true` is `eo_is_refutation` on the same data. -/
theorem eo_is_refutation_of_check (assums : List Term) (cmds : CCmdList)
    (h : logos_check_refutation assums cmds = true) :
    eo_is_refutation (logos_assumption_arglist assums) cmds :=
  eo_is_refutation.intro _ _ (by rwa [logos_check_refutation_eq_checker] at h)

/-! ## The two translation side conditions

Both checks are `decide` of the predicate the theorem uses, so the only thing
left to prove is that checking the parser's *list* of assumptions gives
`TranslatableAssumptionList` of the `CArgList` built from it.
-/

/-- Generalized over the accumulator, mirroring `invoke_assume_list_foldl`. -/
private theorem translatableAssumptionList_foldl (assums : List Term) :
    ∀ rest : CArgList,
      logos_check_translatableAssumptionList assums = true ->
      TranslatableAssumptionList rest ->
      TranslatableAssumptionList (assums.foldl logos_assumption_list_step rest) := by
  induction assums with
  | nil => intro rest _ hrest; exact hrest
  | cons A assums ih =>
    intro rest h hrest
    simp only [logos_check_translatableAssumptionList, List.all_cons, Bool.and_eq_true,
      decide_eq_true_eq] at h
    exact ih _ (by simpa [logos_check_translatableAssumptionList] using h.2)
      (show eoHasSmtTranslation A ∧ TranslatableAssumptionList rest from ⟨h.1, hrest⟩)

/--
`logos_check_translatableAssumptionList` gives the first hypothesis of
`correct___eo_is_refutation` for the list the executable uses as `F`.
-/
theorem translatableAssumptionList_of_check (assums : List Term)
    (h : logos_check_translatableAssumptionList assums = true) :
    TranslatableAssumptionList (logos_assumption_arglist assums) :=
  translatableAssumptionList_foldl assums CArgList.nil h trivial

/--
`logos_check_cmdListTranslationOk` gives the second hypothesis of
`correct___eo_is_refutation`; it is `decide` of that hypothesis.
-/
theorem cmdListTranslationOk_of_check (cmds : CCmdList)
    (h : logos_check_cmdListTranslationOk cmds = true) : CmdListTranslationOk cmds :=
  of_decide_eq_true h

/-! ## The verdict -/

/-- `correct` means all three checks returned `true`. -/
theorem checks_of_verdict_correct (assums : List Term) (cmds : CCmdList)
    (h : logos_verdict assums cmds = Verdict.correct) :
    logos_check_refutation assums cmds = true ∧
      logos_check_translatableAssumptionList assums = true ∧
        logos_check_cmdListTranslationOk cmds = true := by
  unfold logos_verdict at h
  cases hRef : logos_check_refutation assums cmds <;>
    cases hAssums : logos_check_translatableAssumptionList assums <;>
      cases hCmds : logos_check_cmdListTranslationOk cmds <;>
        simp_all

/--
What the executable computes on a file it could parse: the verdict of the
parser's output.  This is the step `Main.lean` performs by hand, so that it can
report *why* an accepted proof is `incomplete`.
-/
theorem logos_check_proof_of_parse (input : String) (assums : List Term) (cmds : CCmdList)
    (h : parseProof input = Except.ok (assums, cmds)) :
    logos_check_proof input = Except.ok (logos_verdict assums cmds) := by
  simp [logos_check_proof, h]

end Eo
