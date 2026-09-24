module

public import CpcMini.Proofs.RuleSupport.Support
import all CpcMini.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shows that the EO program for `refl_impl` is well typed. -/
theorem typed___eo_prog_refl_impl (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_refl x1 ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) :=
by
  intro hTrans _hProg
  by_cases hStuck : x1 = Term.Stuck
  · exfalso
    apply hTrans
    simp [hStuck, __eo_to_smt, __smtx_typeof]
  · have hRefl :
        __eo_prog_refl x1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) x1) x1 := by
      simp [__eo_prog_refl]
    rw [hRefl]
    unfold RuleProofs.eo_has_bool_type
    simpa [__eo_to_smt, __smtx_typeof] using
      RuleProofs.smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTrans

namespace RuleProofs

/-- Proves correctness of the EO program for `refl_of_smt_translation`. -/
theorem correct___eo_prog_refl_of_smt_translation (M : SmtModel) (x1 : Term) :
  eo_has_smt_translation x1 ->
  eo_has_bool_type (__eo_prog_refl x1) ->
  eo_interprets M (__eo_prog_refl x1) true := by
  intro hTy _
  have hNotEqStuck : x1 ≠ Term.Stuck := by
    intro hStuck
    subst hStuck
    simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof] at hTy
  rw [eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M (__eo_to_smt (__eo_prog_refl x1)) ?_ ?_
  · simp [__eo_prog_refl, __eo_to_smt, __smtx_typeof]
    exact smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTy
  · simpa [__eo_prog_refl, hNotEqStuck, __eo_to_smt, __smtx_model_eval] using
      smtx_model_eval_eq_refl M (__smtx_model_eval M (__eo_to_smt x1))

end RuleProofs

/-- Proves correctness of the EO program for `refl_impl`. -/
theorem correct___eo_prog_refl_impl
    (M : SmtModel) (_hM : model_wf M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact RuleProofs.correct___eo_prog_refl_of_smt_translation M x1

/-- Derives the checker facts exposed by the EO program for `refl_impl`. -/
theorem facts___eo_prog_refl_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_refl x1 ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_refl x1) true :=
by
  intro hTrans hProg
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_refl x1) :=
    typed___eo_prog_refl_impl x1 hTrans hProg
  exact correct___eo_prog_refl_impl M hM x1 hTrans hBool

/-- Packages the properties required for the `refl` checker step. -/
public theorem cmd_step_refl_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.refl args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.refl args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.refl args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  eoHasSmtTranslation, RuleProofs.eo_has_smt_translation]
                  using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              refine ⟨?_, ?_⟩
              · intro _hEvidence
                exact facts___eo_prog_refl_impl M hM a1 hATrans
                  (by simpa [__eo_cmd_step_proven] using hProg)
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_refl_impl a1 hATrans
                    (by simpa [__eo_cmd_step_proven] using hProg))
          | cons n premises =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a2 args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
