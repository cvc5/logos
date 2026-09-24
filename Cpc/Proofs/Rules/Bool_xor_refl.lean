module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_bool_xor_refl_eq_of_ne_stuck (x1 : Term) :
    x1 ≠ Term.Stuck ->
    __eo_prog_bool_xor_refl x1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply Term.xor x1) x1)) (Term.Boolean false) := by
  intro hX1
  cases x1 <;> simp [__eo_prog_bool_xor_refl] at hX1 ⊢

private theorem typeof_arg_of_prog_bool_xor_refl_bool (x1 : Term) :
    __eo_typeof (__eo_prog_bool_xor_refl x1) = Term.Bool ->
    __eo_typeof x1 = Term.Bool := by
  intro hTy
  by_cases hX1 : x1 = Term.Stuck
  · subst x1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · rw [prog_bool_xor_refl_eq_of_ne_stuck x1 hX1] at hTy
    change __eo_typeof_eq (__eo_typeof (Term.Apply (Term.Apply Term.xor x1) x1))
      Term.Bool = Term.Bool at hTy
    change __eo_typeof_eq (__eo_typeof_or (__eo_typeof x1) (__eo_typeof x1))
      Term.Bool = Term.Bool at hTy
    cases hT : __eo_typeof x1 <;>
      simp [__eo_typeof_eq, __eo_typeof_or, __eo_requires, __eo_eq,
        native_ite, native_teq, native_not, hT] at hTy ⊢

private theorem typed___eo_prog_bool_xor_refl_impl (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof (__eo_prog_bool_xor_refl x1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_bool_xor_refl x1) := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hX1Type : __eo_typeof x1 = Term.Bool :=
    typeof_arg_of_prog_bool_xor_refl_bool x1 hResultTy
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  have hXorBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.xor x1) x1) :=
    CnfSupport.eo_has_bool_type_xor_of_bool_args x1 x1 hX1Bool hX1Bool
  rw [prog_bool_xor_refl_eq_of_ne_stuck x1 hX1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply Term.xor x1) x1) (Term.Boolean false)
    (hXorBool.trans RuleProofs.eo_has_bool_type_false.symm)
    (by
      rw [hXorBool]
      decide)

private theorem facts___eo_prog_bool_xor_refl_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof (__eo_prog_bool_xor_refl x1) = Term.Bool ->
  eo_interprets M (__eo_prog_bool_xor_refl x1) true := by
  intro hX1Trans hResultTy
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bool_xor_refl x1) :=
    typed___eo_prog_bool_xor_refl_impl x1 hX1Trans hResultTy
  have hX1Type : __eo_typeof x1 = Term.Bool :=
    typeof_arg_of_prog_bool_xor_refl_bool x1 hResultTy
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  rw [prog_bool_xor_refl_eq_of_ne_stuck x1 hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bool_xor_refl_eq_of_ne_stuck x1 hX1NotStuck] using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x1 hX1Bool with
      ⟨b, hEvalX1⟩
    have hFalseEval :
        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
          SmtValue.Boolean false := by
      change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
      rw [__smtx_model_eval.eq_1]
    rw [show __eo_to_smt (Term.Apply (Term.Apply Term.xor x1) x1) =
      SmtTerm.xor (__eo_to_smt x1) (__eo_to_smt x1) by
      rfl]
    rw [__smtx_model_eval.eq_11, hEvalX1, hFalseEval]
    cases b <;> simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
      __smtx_model_eval_xor, __smtx_model_eval_not, native_veq,
      SmtEval.native_not]

public theorem cmd_step_bool_xor_refl_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_xor_refl args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_refl args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_xor_refl args premises ≠ Term.Stuck :=
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
              change __eo_typeof (__eo_prog_bool_xor_refl a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_bool_xor_refl a1) true
                exact facts___eo_prog_bool_xor_refl_impl M hM a1 hATrans hResultTy
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_bool_xor_refl_impl a1 hATrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
