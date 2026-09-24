module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shows that the EO program for `true_intro` is well typed. -/
theorem typed___eo_prog_true_intro_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_true_intro (Proof.pf x1)) := by
  intro hX1Bool
  have hX1Trans : RuleProofs.eo_has_smt_translation x1 :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type x1 hX1Bool
  change RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq x1) (Term.Boolean true))
  have hTyX1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool := hX1Bool
  have hTyEq :
      __smtx_typeof (__eo_to_smt x1) =
        __smtx_typeof (__eo_to_smt (Term.Boolean true)) := by
    have hTrueTy : __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
      change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
      rw [__smtx_typeof.eq_1]
    exact hTyX1.trans hTrueTy.symm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type x1 (Term.Boolean true) hTyEq hX1Trans

/-- Derives the checker facts exposed by the EO program for `true_intro`. -/
theorem facts___eo_prog_true_intro_impl (M : SmtModel) (x1 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M (__eo_prog_true_intro (Proof.pf x1)) true := by
  intro hX1True
  have hBool : RuleProofs.eo_has_bool_type (__eo_prog_true_intro (Proof.pf x1)) :=
    typed___eo_prog_true_intro_impl x1
      (RuleProofs.eo_has_bool_type_of_interprets_true M x1 hX1True)
  change eo_interprets M (Term.Apply (Term.Apply Term.eq x1) (Term.Boolean true)) true
  apply RuleProofs.eo_interprets_eq_of_rel M x1 (Term.Boolean true)
  · exact hBool
  · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hX1True
    cases hX1True with
    | intro_true _ hEvalX1 =>
        have hTrueEval : __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) = SmtValue.Boolean true := by
          change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
          rw [__smtx_model_eval.eq_1]
        rw [hEvalX1, hTrueEval]
        exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

public theorem cmd_step_true_intro_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.true_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.true_intro args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.true_intro args premises) := by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.true_intro args premises ≠ Term.Stuck :=
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
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_true_intro (Proof.pf X1)) true
                exact facts___eo_prog_true_intro_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_true_intro (Proof.pf X1))
                    exact typed___eo_prog_true_intro_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList])))
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
