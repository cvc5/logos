module

public import Cpc.Proofs.RuleSupport.TrueElimSupport
import all Cpc.Proofs.RuleSupport.TrueElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

public theorem cmd_step_true_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.true_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.true_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.true_elim args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.true_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgTrueElim : __eo_prog_true_elim (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_true_elim (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_true_elim (Proof.pf X1)) true
                exact facts___eo_prog_true_elim_impl M hM X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgTrueElim
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_true_elim (Proof.pf X1))
                    exact typed___eo_prog_true_elim_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgTrueElim)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
