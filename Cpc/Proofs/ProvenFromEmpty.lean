module

public import Cpc.Proofs.Checker
import all Cpc.Proofs.Checker
public import Cpc.Proofs.TypePreservation.Nonvacuity
import all Cpc.Proofs.TypePreservation.Nonvacuity

/-!
# Facts proven from the empty state

A command list run from the empty checker state, with no input assumptions,
proves facts that are valid: well typed and true in every well-formed model.
This is the checker's soundness argument (`correct___eo_is_refutation`) with no
assumptions and without the refutation at the end. It lets a downstream tool
justify one rewrite step by running a short command list.

Side conditions, both decidable at run time:

* `CmdListTranslationOk cs`: the per-command translation side conditions.
  It is decidable (`decide (CmdListTranslationOk cs)`; `Cpc/Api.lean` exposes
  it as `logos_check_cmdListTranslationOk`).
* `__eo_state_is_closed (__eo_invoke_cmd_list CState.nil cs) = true`: the run did
  not get stuck, and every `assume_push` was discharged by a `step_pop`. Without
  it the statement is false: after an unpopped `assume_push A`, fact 0 is `A`
  itself. A list of `step` commands only meets it whenever it does not get stuck.

The calculus's extra invariant (`CmdListExtraOk`, assumption stability) needs no
hypothesis: a run that does not get stuck establishes it
(`cmdListExtraOk_of_stateOk_invoke_cmd_list`).
-/

public section

open Eo
open SmtEval
open Smtm

/-- A closed state is not stuck. -/
theorem stateOk_of_state_closed_true :
    ∀ {s : CState}, __eo_state_is_closed s = true -> stateOk s := by
  intro s hClosed
  induction s with
  | nil => trivial
  | Stuck => cases hClosed
  | cons so s ih =>
      cases so with
      | assume_push F => simp [__eo_state_is_closed] at hClosed
      | assume F => exact ih (by simpa [__eo_state_is_closed] using hClosed)
      | proven F => exact ih (by simpa [__eo_state_is_closed] using hClosed)

/--
A fact proven by a command list run from the empty state (no assumptions) is
well typed and true in every well-formed model, provided the commands meet their
translation side conditions and the final state is closed.
-/
theorem proven_from_empty_valid (cs : CCmdList) (P : Term) :
    CmdListTranslationOk cs ->
    __eo_state_is_closed (__eo_invoke_cmd_list CState.nil cs) = true ->
    __eo_state_proven_nth (__eo_invoke_cmd_list CState.nil cs) 0 = P ->
    RuleProofs.eo_has_bool_type P ∧ ∀ M, model_wf M -> eo_interprets M P true := by
  intro hTrans hClosed hP
  have hOk : stateOk (__eo_invoke_cmd_list CState.nil cs) :=
    stateOk_of_state_closed_true hClosed
  have hTrue : ∀ M, model_wf M -> eo_interprets M P true := by
    intro M hM
    have hInit : checkerStateInvariant M CState.nil := by
      simpa [__eo_invoke_assume_list] using
        checkerStateInvariant_after_assume_list M CArgList.nil trivial trivial
          (extraAssumptionListOk_of_stateOk_assume_list M (F := CArgList.nil)
            trivial)
    have hInv :
        checkerStateInvariant M (__eo_invoke_cmd_list CState.nil cs) :=
      invoke_cmd_list_preserves_stateInvariant M hM CState.nil cs hInit hTrans
        (cmdListExtraOk_of_stateOk_invoke_cmd_list M CState.nil cs hOk)
    have hAssumes :
        stateAssumes (__eo_invoke_cmd_list CState.nil cs) = Term.Boolean true := by
      rw [stateAssumes_invoke_cmd_list CState.nil cs trivial hOk]
      rfl
    have hPushes :
        statePushes (__eo_invoke_cmd_list CState.nil cs) = Term.Boolean true :=
      statePushes_of_state_closed_true hClosed
    rw [← hP]
    exact checkerTruthInvariant_at M
      (checkerLocalTruthInvariant_implies_truthInvariant M hInv.2.1) 0
      (by rw [hAssumes]; exact RuleProofs.eo_interprets_true M)
      (by rw [hPushes]; exact RuleProofs.eo_interprets_true M)
  rcases model_wf_nonvacuous with ⟨M, hM⟩
  exact ⟨RuleProofs.eo_has_bool_type_of_interprets_true M P (hTrue M hM), hTrue⟩
