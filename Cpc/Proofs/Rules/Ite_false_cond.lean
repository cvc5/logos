module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_ite_false_cond_eq_of_ne_stuck (x1 y1 : Term) :
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_prog_ite_false_cond x1 y1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean false)) x1) y1))
        y1 := by
  intro hX1 hY1
  cases x1 <;> cases y1 <;> simp [__eo_prog_ite_false_cond] at hX1 hY1 ⊢

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem branch_types_of_prog_ite_false_cond_bool (x1 y1 : Term) :
    x1 ≠ Term.Stuck ->
    y1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_ite_false_cond x1 y1) = Term.Bool ->
    __eo_typeof x1 = __eo_typeof y1 ∧ __eo_typeof y1 ≠ Term.Stuck := by
  intro hX1 hY1 hTy
  rw [prog_ite_false_cond_eq_of_ne_stuck x1 y1 hX1 hY1] at hTy
  change __eo_typeof_eq
    (__eo_typeof_ite Term.Bool (__eo_typeof x1) (__eo_typeof y1))
    (__eo_typeof y1) = Term.Bool at hTy
  rcases eo_typeof_eq_bool_same
      (__eo_typeof_ite Term.Bool (__eo_typeof x1) (__eo_typeof y1))
      (__eo_typeof y1) hTy with ⟨hIteEq, hIteNonStuck⟩
  cases hXTy : __eo_typeof x1 <;> cases hYTy : __eo_typeof y1 <;>
    simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not, hXTy, hYTy] at hIteEq hIteNonStuck ⊢
  all_goals
    simp [hIteNonStuck]

private theorem smt_type_ite_false_same_as_else
    (x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof x1 = __eo_typeof y1 ->
  __smtx_typeof
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean false)) x1) y1)) =
    __smtx_typeof (__eo_to_smt y1) := by
  intro hX1Trans hY1Trans hTypes
  have hX1SmtTy :
      __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 (__eo_typeof x1) (__eo_to_smt x1) rfl hX1Trans rfl
  have hY1SmtTy :
      __smtx_typeof (__eo_to_smt y1) = __eo_to_smt_type (__eo_typeof y1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y1 (__eo_typeof y1) (__eo_to_smt y1) rfl hY1Trans rfl
  rw [show __eo_to_smt
      (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean false)) x1) y1) =
      SmtTerm.ite (__eo_to_smt (Term.Boolean false)) (__eo_to_smt x1) (__eo_to_smt y1) by
      rfl]
  change __smtx_typeof (SmtTerm.ite (SmtTerm.Boolean false) (__eo_to_smt x1)
    (__eo_to_smt y1)) = __smtx_typeof (__eo_to_smt y1)
  rw [typeof_ite_eq, __smtx_typeof.eq_1]
  simp [__smtx_typeof_ite, hX1SmtTy, hY1SmtTy, hTypes, native_Teq,
    native_ite]

private theorem typed___eo_prog_ite_false_cond_impl (x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_false_cond x1 y1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_ite_false_cond x1 y1) := by
  intro hX1Trans hY1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  rcases branch_types_of_prog_ite_false_cond_bool x1 y1 hX1NotStuck hY1NotStuck
      hResultTy with ⟨hTypes, _hYTypeNonStuck⟩
  let iteTerm :=
    Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean false)) x1) y1
  have hIteSame : __smtx_typeof (__eo_to_smt iteTerm) =
      __smtx_typeof (__eo_to_smt y1) := by
    simpa [iteTerm] using smt_type_ite_false_same_as_else x1 y1
      hX1Trans hY1Trans hTypes
  have hIteNonNone : __smtx_typeof (__eo_to_smt iteTerm) ≠ SmtType.None := by
    rw [hIteSame]
    exact hY1Trans
  rw [prog_ite_false_cond_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type iteTerm y1
    (by simpa [iteTerm] using hIteSame)
    (by simpa [iteTerm] using hIteNonNone)

private theorem facts___eo_prog_ite_false_cond_impl
    (M : SmtModel) (hM : model_wf M) (x1 y1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation y1 ->
  __eo_typeof (__eo_prog_ite_false_cond x1 y1) = Term.Bool ->
  eo_interprets M (__eo_prog_ite_false_cond x1 y1) true := by
  intro hX1Trans hY1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hY1NotStuck : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hY1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_ite_false_cond x1 y1) :=
    typed___eo_prog_ite_false_cond_impl x1 y1 hX1Trans hY1Trans hResultTy
  rw [prog_ite_false_cond_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_ite_false_cond_eq_of_ne_stuck x1 y1 hX1NotStuck hY1NotStuck]
      using hProgBool
  · have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
      rw [__smtx_model_eval.eq_1]
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite (Term.Boolean false)) x1) y1) =
        SmtTerm.ite (__eo_to_smt (Term.Boolean false)) (__eo_to_smt x1)
          (__eo_to_smt y1) by
        rfl]
    rw [smtx_eval_ite_term_eq, hFalseEval]
    simpa [__smtx_model_eval_ite] using
      RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt y1))

public theorem cmd_step_ite_false_cond_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_false_cond args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_false_cond args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_false_cond args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_false_cond args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_ite_false_cond a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_ite_false_cond a1 a2) true
                    exact facts___eo_prog_ite_false_cond_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_ite_false_cond_impl a1 a2 hA1Trans hA2Trans
                        hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
