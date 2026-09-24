module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_ite_then_false_eq_of_ne_stuck (c1 x1 : Term) :
    c1 ≠ Term.Stuck ->
    x1 ≠ Term.Stuck ->
    __eo_prog_ite_then_false c1 x1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean false)) x1))
        (Term.Apply (Term.Apply Term.and (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true))) := by
  intro hC1 hX1
  cases c1 <;> cases x1 <;> simp [__eo_prog_ite_then_false] at hC1 hX1 ⊢

private theorem typeof_args_of_prog_ite_then_false_bool (c1 x1 : Term) :
    __eo_typeof (__eo_prog_ite_then_false c1 x1) = Term.Bool ->
    __eo_typeof c1 = Term.Bool ∧ __eo_typeof x1 = Term.Bool := by
  intro hTy
  by_cases hC1 : c1 = Term.Stuck
  · subst c1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hX1 : x1 = Term.Stuck
    · subst x1
      simp [__eo_prog_ite_then_false] at hTy
      have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
        native_decide
      exact False.elim (hStuckTy hTy)
    · rw [prog_ite_then_false_eq_of_ne_stuck c1 x1 hC1 hX1] at hTy
      change __eo_typeof_eq
          (__eo_typeof_ite (__eo_typeof c1) Term.Bool (__eo_typeof x1))
          (__eo_typeof_or (__eo_typeof_not (__eo_typeof c1))
            (__eo_typeof_or (__eo_typeof x1) Term.Bool)) =
        Term.Bool at hTy
      cases hC : __eo_typeof c1 <;> cases hX : __eo_typeof x1 <;>
        simp [__eo_typeof_eq, __eo_typeof_ite, __eo_typeof_or, __eo_typeof_not,
          __eo_requires, __eo_eq, native_ite, native_teq, native_not, hC, hX]
          at hTy ⊢

private theorem typed___eo_prog_ite_then_false_impl (c1 x1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof (__eo_prog_ite_then_false c1 x1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_ite_then_false c1 x1) := by
  intro hC1Trans hX1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  rcases typeof_args_of_prog_ite_then_false_bool c1 x1 hResultTy with
    ⟨hC1Type, hX1Type⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  have hIteBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean false)) x1) :=
    CnfSupport.eo_has_bool_type_ite_of_bool_args c1 (Term.Boolean false) x1
      hC1Bool RuleProofs.eo_has_bool_type_false hX1Bool
  have hNotC1Bool :
      RuleProofs.eo_has_bool_type (Term.Apply Term.not c1) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg c1 hC1Bool
  have hInnerAndBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args x1 (Term.Boolean true)
      hX1Bool RuleProofs.eo_has_bool_type_true
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.and (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true))) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args (Term.Apply Term.not c1)
      (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true))
      hNotC1Bool hInnerAndBool
  rw [prog_ite_then_false_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hIteBool.trans hRightBool.symm)
    (by
      rw [hIteBool]
      decide)

private theorem facts___eo_prog_ite_then_false_impl
    (M : SmtModel) (hM : model_wf M) (c1 x1 : Term) :
  RuleProofs.eo_has_smt_translation c1 ->
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof (__eo_prog_ite_then_false c1 x1) = Term.Bool ->
  eo_interprets M (__eo_prog_ite_then_false c1 x1) true := by
  intro hC1Trans hX1Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hX1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_ite_then_false c1 x1) :=
    typed___eo_prog_ite_then_false_impl c1 x1 hC1Trans hX1Trans hResultTy
  rcases typeof_args_of_prog_ite_then_false_bool c1 x1 hResultTy with
    ⟨hC1Type, hX1Type⟩
  have hC1Bool : RuleProofs.eo_has_bool_type c1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 Term.Bool (__eo_to_smt c1) rfl hC1Trans hC1Type
  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x1 Term.Bool (__eo_to_smt x1) rfl hX1Trans hX1Type
  rw [prog_ite_then_false_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_ite_then_false_eq_of_ne_stuck c1 x1 hC1NotStuck hX1NotStuck]
      using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM c1 hC1Bool with
      ⟨bc, hEvalC1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM x1 hX1Bool with
      ⟨bx, hEvalX1⟩
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply Term.ite c1) (Term.Boolean false)) x1) =
        SmtTerm.ite (__eo_to_smt c1) (SmtTerm.Boolean false) (__eo_to_smt x1) by
        rfl]
    rw [show __eo_to_smt
        (Term.Apply (Term.Apply Term.and (Term.Apply Term.not c1))
          (Term.Apply (Term.Apply Term.and x1) (Term.Boolean true))) =
        SmtTerm.and (SmtTerm.not (__eo_to_smt c1))
          (SmtTerm.and (__eo_to_smt x1) (SmtTerm.Boolean true)) by
        rfl]
    simp only [__smtx_model_eval.eq_1, __smtx_model_eval.eq_7,
      __smtx_model_eval.eq_9, smtx_eval_ite_term_eq, hEvalC1, hEvalX1]
    cases bc <;> cases bx <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, __smtx_model_eval_ite,
        __smtx_model_eval_and, __smtx_model_eval_not, native_veq,
        SmtEval.native_and, SmtEval.native_not]

public theorem cmd_step_ite_then_false_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_then_false args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_false args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.ite_then_false args premises ≠ Term.Stuck :=
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
                  change __eo_typeof (__eo_prog_ite_then_false a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_ite_then_false a1 a2) true
                    exact facts___eo_prog_ite_then_false_impl M hM a1 a2
                      hA1Trans hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_ite_then_false_impl a1 a2 hA1Trans hA2Trans
                        hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
