module

public import Cpc.Proofs.RuleSupport.BvIteEqualCond1Support
import all Cpc.Proofs.RuleSupport.BvIteEqualCond1Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem prog_bv_ite_equal_cond_3_eq_of_ne_stuck
    (c1 t1 e1 t2 e2 : Term) :
    c1 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    e1 ≠ Term.Stuck ->
    t2 ≠ Term.Stuck ->
    e2 ≠ Term.Stuck ->
    __eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (bvIte c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2)))
        (bvIte c1 t1 e2) := by
  intro hC1 hT1 hE1 hT2 hE2
  rw [__eo_prog_bv_ite_equal_cond_3.eq_6 c1 t1 e1 t2 e2 hC1 hT1 hE1 hT2 hE2]
  rfl

private theorem typeof_args_of_prog_bv_ite_equal_cond_3_bool
    (c1 t1 e1 t2 e2 : Term) :
    c1 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    e1 ≠ Term.Stuck ->
    t2 ≠ Term.Stuck ->
    e2 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) = Term.Bool ->
    __eo_typeof c1 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      __eo_typeof t1 = __eo_typeof e1 ∧
      __eo_typeof t1 = __eo_typeof e2 ∧
      __eo_typeof t2 = __eo_typeof e2 ∧
      __eo_typeof t1 ≠ Term.Stuck := by
  intro hC1 hT1 hE1 hT2 hE2 hTy
  rw [prog_bv_ite_equal_cond_3_eq_of_ne_stuck c1 t1 e1 t2 e2 hC1 hT1 hE1 hT2 hE2] at hTy
  change __eo_typeof_eq
      (__eo_typeof_bvite (__eo_typeof c1)
        (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1))
        (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t2) (__eo_typeof e2)))
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e2)) =
    Term.Bool at hTy
  have hOperandsNN :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof_bvite (__eo_typeof c1)
        (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1))
        (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t2) (__eo_typeof e2)))
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e2))
      hTy
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e2)
      hOperandsNN.2 with ⟨hCType, hT1E2, hT1NN⟩
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1)
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1))
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t2) (__eo_typeof e2))
      hOperandsNN.1 with ⟨_hCType2, hInnerEq, hInner1NN⟩
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1)
      hInner1NN with ⟨_hCType3, hT1E1, _hT1NN2⟩
  have hInner2NN :
      __eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t2) (__eo_typeof e2) ≠
        Term.Stuck := by
    intro h
    rw [← hInnerEq] at h
    exact hInner1NN h
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1) (__eo_typeof t2) (__eo_typeof e2)
      hInner2NN with ⟨_hCType4, hT2E2, _hT2NN⟩
  exact ⟨hCType, hT1E1, hT1E2, hT2E2, hT1NN⟩

private theorem smt_typeof_cond3_left_right
    (c1 t1 e1 t2 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2))) =
      __smtx_typeof (__eo_to_smt (bvIte c1 t1 e2)) := by
  intro hC1Trans hT1Trans hE1Trans hT2Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  rcases typeof_args_of_prog_bv_ite_equal_cond_3_bool c1 t1 e1 t2 e2
      hC1NotStuck hT1NotStuck hE1NotStuck hT2NotStuck hE2NotStuck
      hResultTy with
    ⟨hC1Type, hT1E1, hT1E2, hT2E2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hE1Same :
      __smtx_typeof (__eo_to_smt e1) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 e1 (__eo_typeof t1)
      hT1Trans hE1Trans rfl hT1E1.symm
  have hE2Same :
      __smtx_typeof (__eo_to_smt e2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 e2 (__eo_typeof t1)
      hT1Trans hE2Trans rfl hT1E2.symm
  have hT2Same :
      __smtx_typeof (__eo_to_smt t2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 t2 (__eo_typeof t1)
      hT1Trans hT2Trans rfl (hT2E2.trans hT1E2.symm)
  have hInner1Ty :
      __smtx_typeof (__eo_to_smt (bvIte c1 t1 e1)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t1 e1
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy rfl hE1Same
  have hInner2Ty :
      __smtx_typeof (__eo_to_smt (bvIte c1 t2 e2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t2 e2
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy hT2Same hE2Same
  have hLeftTy :
      __smtx_typeof
          (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2))) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2)
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy hInner1Ty hInner2Ty
  have hRightTy :
      __smtx_typeof (__eo_to_smt (bvIte c1 t1 e2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t1 e2
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy rfl hE2Same
  rw [hLeftTy, hRightTy]

private theorem smt_typeof_cond3_right_eq_t
    (c1 t1 e1 t2 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (bvIte c1 t1 e2)) =
      __smtx_typeof (__eo_to_smt t1) := by
  intro hC1Trans hT1Trans hE1Trans hT2Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  rcases typeof_args_of_prog_bv_ite_equal_cond_3_bool c1 t1 e1 t2 e2
      hC1NotStuck hT1NotStuck hE1NotStuck hT2NotStuck hE2NotStuck
      hResultTy with
    ⟨hC1Type, _hT1E1, hT1E2, _hT2E2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hE2Same :
      __smtx_typeof (__eo_to_smt e2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 e2 (__eo_typeof t1)
      hT1Trans hE2Trans rfl hT1E2.symm
  exact smt_typeof_bvite_of_smt_types c1 t1 e2
    (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy rfl hE2Same

private theorem typed___eo_prog_bv_ite_equal_cond_3_impl
    (c1 t1 e1 t2 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) := by
  intro hC1Trans hT1Trans hE1Trans hT2Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  rw [prog_bv_ite_equal_cond_3_eq_of_ne_stuck c1 t1 e1 t2 e2 hC1NotStuck
    hT1NotStuck hE1NotStuck hT2NotStuck hE2NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvIte c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2)) (bvIte c1 t1 e2)
    (smt_typeof_cond3_left_right c1 t1 e1 t2 e2 hC1Trans hT1Trans
      hE1Trans hT2Trans hE2Trans hResultTy)
    (by
      rw [smt_typeof_cond3_left_right c1 t1 e1 t2 e2 hC1Trans hT1Trans
        hE1Trans hT2Trans hE2Trans hResultTy]
      rw [smt_typeof_cond3_right_eq_t c1 t1 e1 t2 e2 hC1Trans hT1Trans
        hE1Trans hT2Trans hE2Trans hResultTy]
      exact hT1Trans)

private theorem smtx_model_eval_ite_equal_cond_3
    (c t1 e1 t2 e2 : SmtValue) :
    __smtx_model_eval_ite c (__smtx_model_eval_ite c t1 e1)
        (__smtx_model_eval_ite c t2 e2) =
      __smtx_model_eval_ite c t1 e2 := by
  cases c <;> try rfl
  case Boolean b =>
    cases b <;> rfl

private theorem eval_bvite_equal_cond_3
    (M : SmtModel) (c1 t1 e1 t2 e2 : Term) :
    __smtx_model_eval M
        (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2))) =
      __smtx_model_eval M (__eo_to_smt (bvIte c1 t1 e2)) := by
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
          (__eo_to_smt t1) (__eo_to_smt e1))
        (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
          (__eo_to_smt t2) (__eo_to_smt e2))) =
    __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt t1) (__eo_to_smt e2))
  simp only [smtx_eval_ite_term_eq]
  exact smtx_model_eval_ite_equal_cond_3
    (__smtx_model_eval M (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1)))
    (__smtx_model_eval M (__eo_to_smt t1))
    (__smtx_model_eval M (__eo_to_smt e1))
    (__smtx_model_eval M (__eo_to_smt t2))
    (__smtx_model_eval M (__eo_to_smt e2))

private theorem facts___eo_prog_bv_ite_equal_cond_3_impl
    (M : SmtModel) (hM : model_wf M) (c1 t1 e1 t2 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) true := by
  intro hC1Trans hT1Trans hE1Trans hT2Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  have hProgBool : RuleProofs.eo_has_bool_type
      (__eo_prog_bv_ite_equal_cond_3 c1 t1 e1 t2 e2) :=
    typed___eo_prog_bv_ite_equal_cond_3_impl c1 t1 e1 t2 e2 hC1Trans
      hT1Trans hE1Trans hT2Trans hE2Trans hResultTy
  rw [prog_bv_ite_equal_cond_3_eq_of_ne_stuck c1 t1 e1 t2 e2 hC1NotStuck
    hT1NotStuck hE1NotStuck hT2NotStuck hE2NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_ite_equal_cond_3_eq_of_ne_stuck c1 t1 e1 t2 e2 hC1NotStuck
      hT1NotStuck hE1NotStuck hT2NotStuck hE2NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) (bvIte c1 t2 e2))))
      (__smtx_model_eval M (__eo_to_smt (bvIte c1 t1 e2)))
    rw [eval_bvite_equal_cond_3 M c1 t1 e1 t2 e2]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_ite_equal_cond_3_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_cond_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_3 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_3 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ite_equal_cond_3 args premises ≠
      Term.Stuck :=
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons a5 args =>
                      cases args with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              have hATransPair :
                                  RuleProofs.eo_has_smt_translation a1 ∧
                                    RuleProofs.eo_has_smt_translation a2 ∧
                                    RuleProofs.eo_has_smt_translation a3 ∧
                                    RuleProofs.eo_has_smt_translation a4 ∧
                                    RuleProofs.eo_has_smt_translation a5 ∧ True := by
                                simpa [cmdTranslationOk, cArgListTranslationOk,
                                  eoHasSmtTranslation,
                                  RuleProofs.eo_has_smt_translation] using hCmdTrans
                              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                                hATransPair.1
                              have hA2Trans : RuleProofs.eo_has_smt_translation a2 :=
                                hATransPair.2.1
                              have hA3Trans : RuleProofs.eo_has_smt_translation a3 :=
                                hATransPair.2.2.1
                              have hA4Trans : RuleProofs.eo_has_smt_translation a4 :=
                                hATransPair.2.2.2.1
                              have hA5Trans : RuleProofs.eo_has_smt_translation a5 :=
                                hATransPair.2.2.2.2.1
                              change __eo_typeof
                                  (__eo_prog_bv_ite_equal_cond_3 a1 a2 a3 a4 a5) =
                                Term.Bool at hResultTy
                              refine ⟨?_, ?_⟩
                              · intro _hTrue
                                change eo_interprets M
                                  (__eo_prog_bv_ite_equal_cond_3 a1 a2 a3 a4 a5) true
                                exact facts___eo_prog_bv_ite_equal_cond_3_impl M hM
                                  a1 a2 a3 a4 a5 hA1Trans hA2Trans hA3Trans
                                  hA4Trans hA5Trans hResultTy
                              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  (typed___eo_prog_bv_ite_equal_cond_3_impl
                                    a1 a2 a3 a4 a5 hA1Trans hA2Trans hA3Trans
                                    hA4Trans hA5Trans hResultTy)
