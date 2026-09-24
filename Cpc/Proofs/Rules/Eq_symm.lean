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

private theorem prog_eq_symm_eq_of_ne_stuck (t1 s1 : Term) :
    t1 ≠ Term.Stuck ->
    s1 ≠ Term.Stuck ->
    __eo_prog_eq_symm t1 s1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply Term.eq t1) s1))
        (Term.Apply (Term.Apply Term.eq s1) t1) := by
  intro hT1 hS1
  cases t1 <;> cases s1 <;> simp [__eo_prog_eq_symm] at hT1 hS1 ⊢

private theorem eo_typeof_eq_bool_same (A B : Term) :
    __eo_typeof_eq A B = Term.Bool ->
    A = B ∧ A ≠ Term.Stuck := by
  intro hTy
  exact RuleProofs.eo_typeof_eq_bool_same A B hTy

private theorem eo_typeof_eq_nonstuck_bool (A B : Term) :
    __eo_typeof_eq A B ≠ Term.Stuck ->
    __eo_typeof_eq A B = Term.Bool := by
  intro hNonStuck
  exact RuleProofs.eo_typeof_eq_eq_bool_of_ne_stuck A B hNonStuck

private theorem operand_types_of_prog_eq_symm_bool (t1 s1 : Term) :
    t1 ≠ Term.Stuck ->
    s1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_eq_symm t1 s1) = Term.Bool ->
    __eo_typeof t1 = __eo_typeof s1 ∧ __eo_typeof t1 ≠ Term.Stuck := by
  intro hT1 hS1 hTy
  rw [prog_eq_symm_eq_of_ne_stuck t1 s1 hT1 hS1] at hTy
  change __eo_typeof_eq (__eo_typeof_eq (__eo_typeof t1) (__eo_typeof s1))
    (__eo_typeof_eq (__eo_typeof s1) (__eo_typeof t1)) = Term.Bool at hTy
  rcases eo_typeof_eq_bool_same
      (__eo_typeof_eq (__eo_typeof t1) (__eo_typeof s1))
      (__eo_typeof_eq (__eo_typeof s1) (__eo_typeof t1)) hTy with
    ⟨_hInnerTypes, hInnerLeftNonStuck⟩
  have hInnerLeftBool :
      __eo_typeof_eq (__eo_typeof t1) (__eo_typeof s1) = Term.Bool :=
    eo_typeof_eq_nonstuck_bool (__eo_typeof t1) (__eo_typeof s1)
      hInnerLeftNonStuck
  exact eo_typeof_eq_bool_same (__eo_typeof t1) (__eo_typeof s1) hInnerLeftBool

private theorem native_veq_false_symm_local {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    native_veq v2 v1 = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

private theorem smtx_model_eval_eq_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

private theorem smtx_model_eval_eq_false_symm_local
    {v1 v2 : SmtValue} :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false ->
    __smtx_model_eval_eq v2 v1 = SmtValue.Boolean false := by
  intro hEq
  by_cases hReg :
      ∃ r1 r2, v1 = SmtValue.RegLan r1 ∧ v2 = SmtValue.RegLan r2
  · rcases hReg with ⟨r1, r2, rfl, rfl⟩
    change SmtValue.Boolean (native_re_ext_eq r2 r1) = SmtValue.Boolean false
    change SmtValue.Boolean (native_re_ext_eq r1 r2) = SmtValue.Boolean false at hEq
    simp at hEq ⊢
    rcases hEq with ⟨s, hs, hNe⟩
    exact ⟨s, hs, fun h => hNe h.symm⟩
  · cases v1 <;> cases v2 <;>
      simp [__smtx_model_eval_eq] at hEq hReg ⊢
    all_goals
      exact native_veq_false_symm_local hEq

private theorem smt_value_rel_eq_eval_symm (v1 v2 : SmtValue) :
    RuleProofs.smt_value_rel (__smtx_model_eval_eq v1 v2)
      (__smtx_model_eval_eq v2 v1) := by
  by_cases hTrue : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true
  · have hSymmTrue : RuleProofs.smt_value_rel v2 v1 :=
      RuleProofs.smt_value_rel_symm v1 v2 hTrue
    rw [hTrue, hSymmTrue]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)
  · rcases smtx_model_eval_eq_boolean v1 v2 with ⟨b, hBool⟩
    cases b with
    | false =>
        have hSymmFalse := smtx_model_eval_eq_false_symm_local hBool
        rw [hBool, hSymmFalse]
        exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)
    | true =>
        exact False.elim (hTrue hBool)

private theorem typed___eo_prog_eq_symm_impl (t1 s1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  __eo_typeof (__eo_prog_eq_symm t1 s1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_eq_symm t1 s1) := by
  intro hT1Trans hS1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  rcases operand_types_of_prog_eq_symm_bool t1 s1 hT1NotStuck hS1NotStuck
      hResultTy with ⟨hTypes, _hTTypeNonStuck⟩
  have hT1SmtTy :
      __smtx_typeof (__eo_to_smt t1) = __eo_to_smt_type (__eo_typeof t1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 (__eo_typeof t1) (__eo_to_smt t1) rfl hT1Trans rfl
  have hS1SmtTy :
      __smtx_typeof (__eo_to_smt s1) = __eo_to_smt_type (__eo_typeof s1) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s1 (__eo_typeof s1) (__eo_to_smt s1) rfl hS1Trans rfl
  have hSameSmt :
      __smtx_typeof (__eo_to_smt t1) = __smtx_typeof (__eo_to_smt s1) := by
    rw [hT1SmtTy, hS1SmtTy, hTypes]
  have hInnerBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t1) s1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t1 s1 hSameSmt hT1Trans
  have hSymmBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s1) t1) :=
    RuleProofs.eo_has_bool_type_eq_symm t1 s1 hInnerBool
  rw [prog_eq_symm_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply Term.eq t1) s1)
    (Term.Apply (Term.Apply Term.eq s1) t1)
    (hInnerBool.trans hSymmBool.symm)
    (by
      rw [hInnerBool]
      decide)

private theorem facts___eo_prog_eq_symm_impl
    (M : SmtModel) (hM : model_wf M) (t1 s1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  __eo_typeof (__eo_prog_eq_symm t1 s1) = Term.Bool ->
  eo_interprets M (__eo_prog_eq_symm t1 s1) true := by
  intro hT1Trans hS1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_eq_symm t1 s1) :=
    typed___eo_prog_eq_symm_impl t1 s1 hT1Trans hS1Trans hResultTy
  rw [prog_eq_symm_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_eq_symm_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
      using hProgBool
  · rw [show __eo_to_smt (Term.Apply (Term.Apply Term.eq t1) s1) =
        SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt s1) by
        rfl]
    rw [show __eo_to_smt (Term.Apply (Term.Apply Term.eq s1) t1) =
        SmtTerm.eq (__eo_to_smt s1) (__eo_to_smt t1) by
        rfl]
    rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq]
    exact smt_value_rel_eq_eval_symm
      (__smtx_model_eval M (__eo_to_smt t1))
      (__smtx_model_eval M (__eo_to_smt s1))

public theorem cmd_step_eq_symm_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.eq_symm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_symm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.eq_symm args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_eq_symm a1 a2) = Term.Bool at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_eq_symm a1 a2) true
                    exact facts___eo_prog_eq_symm_impl M hM a1 a2 hA1Trans hA2Trans
                      hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_eq_symm_impl a1 a2 hA1Trans hA2Trans hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
