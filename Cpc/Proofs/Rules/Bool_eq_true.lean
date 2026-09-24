module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_bool_eq_true_eq_of_ne_stuck (t1 : Term) :
    t1 ≠ Term.Stuck ->
    __eo_prog_bool_eq_true t1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply Term.eq t1) (Term.Boolean true))) t1 := by
  intro hT1
  cases t1 <;> simp [__eo_prog_bool_eq_true] at hT1 ⊢

private theorem typeof_arg_of_prog_bool_eq_true_bool (t1 : Term) :
    __eo_typeof (__eo_prog_bool_eq_true t1) = Term.Bool ->
    __eo_typeof t1 = Term.Bool := by
  intro hTy
  by_cases hT1 : t1 = Term.Stuck
  · subst t1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bool_eq_true_eq_of_ne_stuck t1 hT1] at hTy
    change __eo_typeof_eq (__eo_typeof (Term.Apply (Term.Apply Term.eq t1)
      (Term.Boolean true))) (__eo_typeof t1) = Term.Bool at hTy
    change __eo_typeof_eq (__eo_typeof_eq (__eo_typeof t1) Term.Bool)
      (__eo_typeof t1) = Term.Bool at hTy
    cases hT : __eo_typeof t1 <;>
      simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not, hT] at hTy ⊢

private theorem typed___eo_prog_bool_eq_true_impl (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  __eo_typeof (__eo_prog_bool_eq_true t1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_bool_eq_true t1) := by
  intro hT1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT1Type : __eo_typeof t1 = Term.Bool :=
    typeof_arg_of_prog_bool_eq_true_bool t1 hResultTy
  have hT1Bool : RuleProofs.eo_has_bool_type t1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Bool (__eo_to_smt t1) rfl hT1Trans hT1Type
  have hEqTrueBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq t1) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t1 (Term.Boolean true)
      (hT1Bool.trans RuleProofs.eo_has_bool_type_true.symm)
      (by
        rw [hT1Bool]
        decide)
  rw [prog_bool_eq_true_eq_of_ne_stuck t1 hT1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply Term.eq t1) (Term.Boolean true)) t1
    (hEqTrueBool.trans hT1Bool.symm)
    (by
      rw [hEqTrueBool]
      decide)

private theorem facts___eo_prog_bool_eq_true_impl
    (M : SmtModel) (hM : model_wf M) (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  __eo_typeof (__eo_prog_bool_eq_true t1) = Term.Bool ->
  eo_interprets M (__eo_prog_bool_eq_true t1) true := by
  intro hT1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bool_eq_true t1) :=
    typed___eo_prog_bool_eq_true_impl t1 hT1Trans hResultTy
  have hT1Type : __eo_typeof t1 = Term.Bool :=
    typeof_arg_of_prog_bool_eq_true_bool t1 hResultTy
  have hT1Bool : RuleProofs.eo_has_bool_type t1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Bool (__eo_to_smt t1) rfl hT1Trans hT1Type
  rw [prog_bool_eq_true_eq_of_ne_stuck t1 hT1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bool_eq_true_eq_of_ne_stuck t1 hT1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t1 hT1Bool with
      ⟨b, hEvalT1⟩
    have hTrueEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
          SmtValue.Boolean true := by
      change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
      rw [__smtx_model_eval.eq_1]
    rw [show __eo_to_smt (Term.Apply (Term.Apply Term.eq t1) (Term.Boolean true)) =
      SmtTerm.eq (__eo_to_smt t1) (__eo_to_smt (Term.Boolean true)) by
      rfl]
    rw [smtx_eval_eq_term_eq, hEvalT1, hTrueEval]
    cases b <;> simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq]

public theorem cmd_step_bool_eq_true_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_eq_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_eq_true args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_eq_true args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_eq_true args premises ≠ Term.Stuck :=
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
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              change __eo_typeof (__eo_prog_bool_eq_true a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bool_eq_true a1) true
                exact facts___eo_prog_bool_eq_true_impl M hM a1 hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bool_eq_true_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
