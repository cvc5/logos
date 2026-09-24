module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Simplifies EO-to-SMT translation for `stuck`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

/-- Simplifies EO-to-SMT translation for `eq`. -/
private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem smtx_model_eval_eq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq x y) =
      __smtx_model_eval_eq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Expands `__eo_prog_refl` on non-stuck inputs. -/
private theorem eo_prog_refl_eq_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_prog_refl x = Term.Apply (Term.Apply Term.eq x) x := by
  intro h
  cases x <;> simp [__eo_prog_refl] at h ⊢

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
    subst hStuck
    change __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None
    simp [eo_to_smt_stuck_eq, TranslationProofs.smtx_typeof_none]
  · rw [eo_prog_refl_eq_of_ne_stuck x1 hStuck]
    unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_eq_eq x1 x1]
    rw [typeof_eq_eq]
    exact RuleProofs.smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTrans

namespace RuleProofs

/-- Derives `correct___eo_prog_refl` from `smt_translation`. -/
theorem correct___eo_prog_refl_of_smt_translation (M : SmtModel) (x1 : Term) :
  eo_has_smt_translation x1 ->
  eo_has_bool_type (__eo_prog_refl x1) ->
  eo_interprets M (__eo_prog_refl x1) true := by
  intro hTy _
  have hNotEqStuck : x1 ≠ Term.Stuck := by
    intro hStuck
    subst hStuck
    change __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.None at hTy
    rw [eo_to_smt_stuck_eq, TranslationProofs.smtx_typeof_none] at hTy
    exact hTy rfl
  rw [eo_interprets_iff_smt_interprets]
  rw [eo_prog_refl_eq_of_ne_stuck x1 hNotEqStuck, eo_to_smt_eq_eq x1 x1]
  refine smt_interprets.intro_true M
      (SmtTerm.eq (__eo_to_smt x1) (__eo_to_smt x1)) ?_ ?_
  · rw [typeof_eq_eq]
    exact smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTy
  · rw [smtx_model_eval_eq_term_eq]
    exact smtx_model_eval_eq_refl (__smtx_model_eval M (__eo_to_smt x1))

end RuleProofs

/-- Proves correctness of the EO program for `refl_impl`. -/
theorem correct___eo_prog_refl_impl
    (M : SmtModel) (_hM : model_wf M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  eo_interprets M (__eo_prog_refl x1) true :=
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
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
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
              have hProgRefl : __eo_prog_refl a1 ≠ Term.Stuck := by
                change __eo_prog_refl a1 ≠ Term.Stuck at hProg
                exact hProg
              refine ⟨?_, ?_⟩
              · intro _hTrue
                exact facts___eo_prog_refl_impl M hM a1 hATrans hProgRefl
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_refl_impl a1 hATrans hProgRefl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
