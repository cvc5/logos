module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

def bvIte (c t e : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e

private theorem prog_bv_ite_equal_cond_1_eq_of_ne_stuck
    (c1 t1 e1 e2 : Term) :
    c1 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    e1 ≠ Term.Stuck ->
    e2 ≠ Term.Stuck ->
    __eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (bvIte c1 (bvIte c1 t1 e1) e2))
        (bvIte c1 t1 e2) := by
  intro hC1 hT1 hE1 hE2
  rw [__eo_prog_bv_ite_equal_cond_1.eq_5 c1 t1 e1 e2 hC1 hT1 hE1 hE2]
  rfl

theorem typeof_bvite_args_of_ne_stuck
    (C T E : Term) :
    __eo_typeof_bvite C T E ≠ Term.Stuck ->
      C = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
        T = E ∧ T ≠ Term.Stuck := by
  intro h
  by_cases hT : T = Term.Stuck
  · subst T
    exact False.elim (h (__eo_typeof_bvite.eq_1 C E))
  by_cases hE : E = Term.Stuck
  · subst E
    exact False.elim (h (__eo_typeof_bvite.eq_2 C T hT))
  by_cases hC : C = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  · subst C
    rw [__eo_typeof_bvite.eq_3 T E hT hE] at h
    have hCond := support_eo_requires_cond_eq_of_non_stuck h
    have hEq : E = T := support_eq_of_eo_eq_true T E hCond
    exact ⟨rfl, hEq.symm, hT⟩
  · exact False.elim (h (__eo_typeof_bvite.eq_4 C T E hC hT hE))

private theorem typeof_args_of_prog_bv_ite_equal_cond_1_bool
    (c1 t1 e1 e2 : Term) :
    c1 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    e1 ≠ Term.Stuck ->
    e2 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) = Term.Bool ->
    __eo_typeof c1 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      __eo_typeof t1 = __eo_typeof e1 ∧
      __eo_typeof t1 = __eo_typeof e2 ∧
      __eo_typeof t1 ≠ Term.Stuck := by
  intro hC1 hT1 hE1 hE2 hTy
  rw [prog_bv_ite_equal_cond_1_eq_of_ne_stuck c1 t1 e1 e2 hC1 hT1 hE1 hE2] at hTy
  change __eo_typeof_eq
      (__eo_typeof_bvite (__eo_typeof c1)
        (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1))
        (__eo_typeof e2))
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e2)) =
    Term.Bool at hTy
  have hOperandsNN :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof_bvite (__eo_typeof c1)
        (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1))
        (__eo_typeof e2))
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e2))
      hTy
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e2)
      hOperandsNN.2 with ⟨hCType, hT2, hTNN⟩
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1)
      (__eo_typeof_bvite (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1))
      (__eo_typeof e2) hOperandsNN.1 with
    ⟨_hCType2, hInnerE2, hInnerNN⟩
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1) (__eo_typeof t1) (__eo_typeof e1)
      hInnerNN with ⟨_hCType3, hT1, _hTNN2⟩
  exact ⟨hCType, hT1, hT2, hTNN⟩

theorem smt_typeof_binary_one_one :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    native_decide
  simpa [native_int_to_nat] using
    TranslationProofs.smtx_typeof_binary_of_non_none 1 1 hNN

theorem smt_typeof_c1_bitvec_one
    (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof c1 = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ->
    __smtx_typeof (__eo_to_smt c1) = SmtType.BitVec 1 := by
  intro hC1Trans hC1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt c1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) (__eo_to_smt c1) rfl
      hC1Trans hC1Type
  simpa [__eo_to_smt_type, SmtEval.native_zleq, native_int_to_nat, native_ite] using hSmtType

theorem smt_type_eq_of_same_eo_type
    (x y T : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof x = T ->
    __eo_typeof y = T ->
    __smtx_typeof (__eo_to_smt y) = __smtx_typeof (__eo_to_smt x) := by
  intro hXTrans hYTrans hXType hYType
  have hXSmtType :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type T := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x T (__eo_to_smt x) rfl hXTrans hXType
  have hYSmtType :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type T := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y T (__eo_to_smt y) rfl hYTrans hYType
  rw [hYSmtType, hXSmtType]

theorem smt_typeof_bvite_of_smt_types
    (c t e : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt t) = T ->
    __smtx_typeof (__eo_to_smt e) = T ->
    __smtx_typeof (__eo_to_smt (bvIte c t e)) = T := by
  intro hC hT hE
  have hCondTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt c) (SmtTerm.Binary 1 1)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hC,
      smt_typeof_binary_one_one, native_Teq, native_ite]
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c) (SmtTerm.Binary 1 1))
        (__eo_to_smt t) (__eo_to_smt e)) = T
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hCondTy, hT, hE, native_Teq, native_ite]

private theorem smt_typeof_cond1_left_right
    (c1 t1 e1 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) e2)) =
      __smtx_typeof (__eo_to_smt (bvIte c1 t1 e2)) := by
  intro hC1Trans hT1Trans hE1Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  rcases typeof_args_of_prog_bv_ite_equal_cond_1_bool c1 t1 e1 e2
      hC1NotStuck hT1NotStuck hE1NotStuck hE2NotStuck hResultTy with
    ⟨hC1Type, hT1E1, hT1E2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hE1Same :
      __smtx_typeof (__eo_to_smt e1) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 e1 (__eo_typeof t1)
      hT1Trans hE1Trans rfl hT1E1.symm
  have hE2Same :
      __smtx_typeof (__eo_to_smt e2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 e2 (__eo_typeof t1)
      hT1Trans hE2Trans rfl hT1E2.symm
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (bvIte c1 t1 e1)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t1 e1
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy rfl hE1Same
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) e2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 (bvIte c1 t1 e1) e2
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy hInnerTy hE2Same
  have hRightTy :
      __smtx_typeof (__eo_to_smt (bvIte c1 t1 e2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t1 e2
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy rfl hE2Same
  rw [hLeftTy, hRightTy]

private theorem smt_typeof_cond1_right_eq_t
    (c1 t1 e1 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (bvIte c1 t1 e2)) =
      __smtx_typeof (__eo_to_smt t1) := by
  intro hC1Trans hT1Trans hE1Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  rcases typeof_args_of_prog_bv_ite_equal_cond_1_bool c1 t1 e1 e2
      hC1NotStuck hT1NotStuck hE1NotStuck hE2NotStuck hResultTy with
    ⟨hC1Type, _hT1E1, hT1E2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hE2Same :
      __smtx_typeof (__eo_to_smt e2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 e2 (__eo_typeof t1)
      hT1Trans hE2Trans rfl hT1E2.symm
  exact smt_typeof_bvite_of_smt_types c1 t1 e2
    (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy rfl hE2Same

theorem typed___eo_prog_bv_ite_equal_cond_1_impl
    (c1 t1 e1 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) := by
  intro hC1Trans hT1Trans hE1Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  rw [prog_bv_ite_equal_cond_1_eq_of_ne_stuck c1 t1 e1 e2 hC1NotStuck
    hT1NotStuck hE1NotStuck hE2NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvIte c1 (bvIte c1 t1 e1) e2) (bvIte c1 t1 e2)
    (smt_typeof_cond1_left_right c1 t1 e1 e2 hC1Trans hT1Trans
      hE1Trans hE2Trans hResultTy)
    (by
      rw [smt_typeof_cond1_left_right c1 t1 e1 e2 hC1Trans hT1Trans
        hE1Trans hE2Trans hResultTy]
      rw [smt_typeof_cond1_right_eq_t c1 t1 e1 e2 hC1Trans hT1Trans
        hE1Trans hE2Trans hResultTy]
      exact hT1Trans)

private theorem smtx_model_eval_ite_equal_cond_1
    (c t e1 e2 : SmtValue) :
    __smtx_model_eval_ite c (__smtx_model_eval_ite c t e1) e2 =
      __smtx_model_eval_ite c t e2 := by
  cases c <;> try rfl
  case Boolean b =>
    cases b <;> rfl

private theorem eval_bvite_equal_cond_1
    (M : SmtModel) (c1 t1 e1 e2 : Term) :
    __smtx_model_eval M
        (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) e2)) =
      __smtx_model_eval M (__eo_to_smt (bvIte c1 t1 e2)) := by
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
          (__eo_to_smt t1) (__eo_to_smt e1))
        (__eo_to_smt e2)) =
    __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt t1) (__eo_to_smt e2))
  simp only [smtx_eval_ite_term_eq]
  exact smtx_model_eval_ite_equal_cond_1
    (__smtx_model_eval M (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1)))
    (__smtx_model_eval M (__eo_to_smt t1))
    (__smtx_model_eval M (__eo_to_smt e1))
    (__smtx_model_eval M (__eo_to_smt e2))

theorem facts___eo_prog_bv_ite_equal_cond_1_impl
    (M : SmtModel) (hM : model_wf M) (c1 t1 e1 e2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation e1 ->
    RuleProofs.eo_has_smt_translation e2 ->
    __eo_typeof (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) true := by
  intro hC1Trans hT1Trans hE1Trans hE2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hE2NotStuck : e2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e2 hE2Trans
  have hProgBool : RuleProofs.eo_has_bool_type
      (__eo_prog_bv_ite_equal_cond_1 c1 t1 e1 e2) :=
    typed___eo_prog_bv_ite_equal_cond_1_impl c1 t1 e1 e2 hC1Trans
      hT1Trans hE1Trans hE2Trans hResultTy
  rw [prog_bv_ite_equal_cond_1_eq_of_ne_stuck c1 t1 e1 e2 hC1NotStuck
    hT1NotStuck hE1NotStuck hE2NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_ite_equal_cond_1_eq_of_ne_stuck c1 t1 e1 e2 hC1NotStuck
      hT1NotStuck hE1NotStuck hE2NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvIte c1 (bvIte c1 t1 e1) e2)))
      (__smtx_model_eval M (__eo_to_smt (bvIte c1 t1 e2)))
    rw [eval_bvite_equal_cond_1 M c1 t1 e1 e2]
    exact RuleProofs.smt_value_rel_refl _
