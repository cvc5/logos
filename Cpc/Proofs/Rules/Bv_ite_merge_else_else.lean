module

public import Cpc.Proofs.RuleSupport.BvIteEqualCond1Support
import all Cpc.Proofs.RuleSupport.BvIteEqualCond1Support
public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def bvNot (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) x

private def bvAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y

private def bvOne : Term :=
  Term.Binary 1 1

private def mergeElseElseCond (c1 c2 : Term) : Term :=
  bvAnd (bvNot c1) (bvAnd c2 bvOne)

private def mergeElseElseLhs (c1 c2 t1 t2 : Term) : Term :=
  bvIte c1 t2 (bvIte c2 t1 t2)

private def mergeElseElseRhs (c1 c2 t1 t2 : Term) : Term :=
  bvIte (mergeElseElseCond c1 c2) t1 t2

private theorem prog_bv_ite_merge_else_else_eq_of_ne_stuck
    (c1 c2 t1 t2 : Term) :
    c1 ≠ Term.Stuck ->
    c2 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    t2 ≠ Term.Stuck ->
    __eo_prog_bv_ite_merge_else_else c1 c2 t1 t2 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (mergeElseElseLhs c1 c2 t1 t2))
        (mergeElseElseRhs c1 c2 t1 t2) := by
  intro hC1 hC2 hT1 hT2
  rw [__eo_prog_bv_ite_merge_else_else.eq_5 c1 c2 t1 t2 hC1 hC2 hT1 hT2]
  rfl

private theorem typeof_args_of_prog_bv_ite_merge_else_else_bool
    (c1 c2 t1 t2 : Term) :
    c1 ≠ Term.Stuck ->
    c2 ≠ Term.Stuck ->
    t1 ≠ Term.Stuck ->
    t2 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) = Term.Bool ->
    __eo_typeof c1 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      __eo_typeof c2 =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
      __eo_typeof t1 = __eo_typeof t2 ∧
      __eo_typeof t1 ≠ Term.Stuck := by
  intro hC1 hC2 hT1 hT2 hTy
  rw [prog_bv_ite_merge_else_else_eq_of_ne_stuck c1 c2 t1 t2 hC1 hC2
    hT1 hT2] at hTy
  change __eo_typeof_eq
      (__eo_typeof_bvite (__eo_typeof c1)
        (__eo_typeof t2)
        (__eo_typeof_bvite (__eo_typeof c2) (__eo_typeof t1)
          (__eo_typeof t2)))
      (__eo_typeof_bvite (__eo_typeof (mergeElseElseCond c1 c2))
        (__eo_typeof t1) (__eo_typeof t2)) = Term.Bool at hTy
  have hOperandsNN :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof_bvite (__eo_typeof c1)
        (__eo_typeof t2)
        (__eo_typeof_bvite (__eo_typeof c2) (__eo_typeof t1)
          (__eo_typeof t2)))
      (__eo_typeof_bvite (__eo_typeof (mergeElseElseCond c1 c2))
        (__eo_typeof t1) (__eo_typeof t2))
      hTy
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c1) (__eo_typeof t2)
      (__eo_typeof_bvite (__eo_typeof c2) (__eo_typeof t1)
        (__eo_typeof t2)) hOperandsNN.1 with
    ⟨hC1Type, hT2Inner, hT2NN⟩
  have hInnerNN :
      __eo_typeof_bvite (__eo_typeof c2) (__eo_typeof t1)
          (__eo_typeof t2) ≠ Term.Stuck := by
    intro h
    rw [← hT2Inner] at h
    exact hT2NN h
  rcases typeof_bvite_args_of_ne_stuck
      (__eo_typeof c2) (__eo_typeof t1) (__eo_typeof t2)
      hInnerNN with
    ⟨hC2Type, hT1T2, hT1NN⟩
  exact ⟨hC1Type, hC2Type, hT1T2, hT1NN⟩

private theorem smt_typeof_bvnot_bitvec_one
    (x : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt (bvNot x)) = SmtType.BitVec 1 := by
  intro hXTy
  change __smtx_typeof (SmtTerm.bvnot (__eo_to_smt x)) = SmtType.BitVec 1
  rw [smtx_typeof_bvnot_term_eq]
  simp [__smtx_typeof_bv_op_1, hXTy]

private theorem smt_typeof_bvand_bitvec_one
    (x y : Term) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt (bvAnd x y)) = SmtType.BitVec 1 := by
  intro hXTy hYTy
  change __smtx_typeof (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.BitVec 1
  rw [__smtx_typeof.eq_def] <;> simp [__smtx_typeof_bv_op_2, hXTy, hYTy,
    native_nateq, native_ite]

private theorem smt_typeof_bvone :
    __smtx_typeof (__eo_to_smt bvOne) = SmtType.BitVec 1 := by
  change __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1
  exact smt_typeof_binary_one_one

private theorem smt_typeof_merge_else_else_cond
    (c1 c2 : Term) :
    __smtx_typeof (__eo_to_smt c1) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt c2) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt (mergeElseElseCond c1 c2)) =
      SmtType.BitVec 1 := by
  intro hC1Ty hC2Ty
  have hNotC1 : __smtx_typeof (__eo_to_smt (bvNot c1)) = SmtType.BitVec 1 :=
    smt_typeof_bvnot_bitvec_one c1 hC1Ty
  have hInner :
      __smtx_typeof (__eo_to_smt (bvAnd c2 bvOne)) =
        SmtType.BitVec 1 :=
    smt_typeof_bvand_bitvec_one c2 bvOne hC2Ty smt_typeof_bvone
  exact smt_typeof_bvand_bitvec_one (bvNot c1) (bvAnd c2 bvOne)
    hNotC1 hInner

private theorem smt_typeof_else_else_left_right
    (c1 c2 t1 t2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation c2 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    __eo_typeof (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (mergeElseElseLhs c1 c2 t1 t2)) =
      __smtx_typeof (__eo_to_smt (mergeElseElseRhs c1 c2 t1 t2)) := by
  intro hC1Trans hC2Trans hT1Trans hT2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hC2NotStuck : c2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c2 hC2Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  rcases typeof_args_of_prog_bv_ite_merge_else_else_bool c1 c2 t1 t2
      hC1NotStuck hC2NotStuck hT1NotStuck hT2NotStuck hResultTy with
    ⟨hC1Type, hC2Type, hT1T2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hC2SmtTy := smt_typeof_c1_bitvec_one c2 hC2Trans hC2Type
  have hT2Same :
      __smtx_typeof (__eo_to_smt t2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 t2 (__eo_typeof t1)
      hT1Trans hT2Trans rfl hT1T2.symm
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (bvIte c2 t1 t2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c2 t1 t2
      (__smtx_typeof (__eo_to_smt t1)) hC2SmtTy rfl hT2Same
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mergeElseElseLhs c1 c2 t1 t2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t2 (bvIte c2 t1 t2)
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy hT2Same hInnerTy
  have hCondTy :
      __smtx_typeof (__eo_to_smt (mergeElseElseCond c1 c2)) =
        SmtType.BitVec 1 :=
    smt_typeof_merge_else_else_cond c1 c2 hC1SmtTy hC2SmtTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mergeElseElseRhs c1 c2 t1 t2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types (mergeElseElseCond c1 c2) t1 t2
      (__smtx_typeof (__eo_to_smt t1)) hCondTy rfl hT2Same
  rw [hLeftTy, hRightTy]

private theorem smt_typeof_else_else_left_non_none
    (c1 c2 t1 t2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation c2 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    __eo_typeof (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) = Term.Bool ->
    __smtx_typeof (__eo_to_smt (mergeElseElseLhs c1 c2 t1 t2)) ≠
      SmtType.None := by
  intro hC1Trans hC2Trans hT1Trans hT2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hC2NotStuck : c2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c2 hC2Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  rcases typeof_args_of_prog_bv_ite_merge_else_else_bool c1 c2 t1 t2
      hC1NotStuck hC2NotStuck hT1NotStuck hT2NotStuck hResultTy with
    ⟨hC1Type, hC2Type, hT1T2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hC2SmtTy := smt_typeof_c1_bitvec_one c2 hC2Trans hC2Type
  have hT2Same :
      __smtx_typeof (__eo_to_smt t2) = __smtx_typeof (__eo_to_smt t1) :=
    smt_type_eq_of_same_eo_type t1 t2 (__eo_typeof t1)
      hT1Trans hT2Trans rfl hT1T2.symm
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (bvIte c2 t1 t2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c2 t1 t2
      (__smtx_typeof (__eo_to_smt t1)) hC2SmtTy rfl hT2Same
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mergeElseElseLhs c1 c2 t1 t2)) =
        __smtx_typeof (__eo_to_smt t1) :=
    smt_typeof_bvite_of_smt_types c1 t2 (bvIte c2 t1 t2)
      (__smtx_typeof (__eo_to_smt t1)) hC1SmtTy hT2Same hInnerTy
  rw [hLeftTy]
  exact hT1Trans

private theorem typed___eo_prog_bv_ite_merge_else_else_impl
    (c1 c2 t1 t2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation c2 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    __eo_typeof (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) := by
  intro hC1Trans hC2Trans hT1Trans hT2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hC2NotStuck : c2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c2 hC2Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  rw [prog_bv_ite_merge_else_else_eq_of_ne_stuck c1 c2 t1 t2 hC1NotStuck
    hC2NotStuck hT1NotStuck hT2NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (mergeElseElseLhs c1 c2 t1 t2) (mergeElseElseRhs c1 c2 t1 t2)
    (smt_typeof_else_else_left_right c1 c2 t1 t2 hC1Trans hC2Trans
      hT1Trans hT2Trans hResultTy)
    (smt_typeof_else_else_left_non_none c1 c2 t1 t2 hC1Trans hC2Trans
      hT1Trans hT2Trans hResultTy)

private theorem bv1_not (b : Bool) :
    __smtx_model_eval_bvnot (bv1 b) = bv1 (!b) := by
  cases b <;> native_decide

private theorem eval_bvnot_bv1_term
    (M : SmtModel) (x : Term) (b : Bool)
    (hx : __smtx_model_eval M (__eo_to_smt x) = bv1 b) :
    __smtx_model_eval M (__eo_to_smt (bvNot x)) = bv1 (!b) := by
  change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = bv1 (!b)
  rw [smtx_eval_bvnot_term_eq, hx]
  exact bv1_not b

private theorem eval_bvone (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt bvOne) = bv1 true := by
  simpa [bvOne, bv1] using eval_binary M 1 1

private theorem eval_bv1_of_smt_type_bitvec_one
    (M : SmtModel) (hM : model_wf M) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec 1 ->
    ∃ b, __smtx_model_eval M (__eo_to_smt t) = bv1 b := by
  intro hTrans hSmtTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec 1 := by
    simpa [hSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
          using hTrans)
  rcases bitvec_value_canonical hEvalTy with ⟨payload, hEvalT⟩
  have hPayloadCanon :
      native_zeq payload (native_mod_total payload (native_int_pow2 1)) =
        true := by
    exact bitvec_payload_canonical
      (by simpa [hEvalT, native_nat_to_int, native_int_to_nat] using hEvalTy)
  have hWidth : native_zleq 0 1 = true := by
    native_decide
  have hRange := bitvec_payload_range_of_canonical hWidth hPayloadCanon
  have hPayloadCases : payload = 0 ∨ payload = 1 := by
    have hLtTwo : payload < 2 := by
      simpa [native_int_pow2, native_zexp_total] using hRange.2
    have hLeOne : payload ≤ 1 := Int.le_of_lt_add_one hLtTwo
    rcases Int.lt_or_eq_of_le hRange.1 with hPos | hZero
    · have hGeOne : 1 ≤ payload := (Int.add_one_le_iff).mpr hPos
      exact Or.inr (Int.le_antisymm hLeOne hGeOne)
    · exact Or.inl hZero.symm
  rcases hPayloadCases with hPayload | hPayload
  · refine ⟨false, ?_⟩
    subst payload
    simpa [bv1, native_nat_to_int] using hEvalT
  · refine ⟨true, ?_⟩
    subst payload
    simpa [bv1, native_nat_to_int] using hEvalT

private theorem eval_merge_else_else_cond
    (M : SmtModel) (c1 c2 : Term) (b1 b2 : Bool) :
    __smtx_model_eval M (__eo_to_smt c1) = bv1 b1 ->
    __smtx_model_eval M (__eo_to_smt c2) = bv1 b2 ->
    __smtx_model_eval M (__eo_to_smt (mergeElseElseCond c1 c2)) =
      bv1 (!b1 && b2) := by
  intro hC1Eval hC2Eval
  have hNotC1Eval :
      __smtx_model_eval M (__eo_to_smt (bvNot c1)) = bv1 (!b1) :=
    eval_bvnot_bv1_term M c1 b1 hC1Eval
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt (bvAnd c2 bvOne)) =
        bv1 (b2 && true) :=
    eval_bvand_term M c2 bvOne b2 true hC2Eval (eval_bvone M)
  have hOuterEval :
      __smtx_model_eval M (__eo_to_smt (mergeElseElseCond c1 c2)) =
        bv1 ((!b1) && (b2 && true)) :=
    eval_bvand_term M (bvNot c1) (bvAnd c2 bvOne) (!b1)
      (b2 && true) hNotC1Eval hInnerEval
  rw [hOuterEval]
  cases b1 <;> cases b2 <;> rfl

private theorem eval_eq_bv1_one
    (M : SmtModel) (x : Term) (b : Bool) :
    __smtx_model_eval M (__eo_to_smt x) = bv1 b ->
    __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Binary 1 1)) =
      SmtValue.Boolean b := by
  intro hx
  exact eval_eq_bv1_one_term M x b hx

private theorem eval_bvite_merge_else_else
    (M : SmtModel) (hM : model_wf M) (c1 c2 t1 t2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation c2 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    __eo_typeof (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) = Term.Bool ->
    __smtx_model_eval M (__eo_to_smt (mergeElseElseLhs c1 c2 t1 t2)) =
      __smtx_model_eval M (__eo_to_smt (mergeElseElseRhs c1 c2 t1 t2)) := by
  intro hC1Trans hC2Trans hT1Trans hT2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hC2NotStuck : c2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c2 hC2Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  rcases typeof_args_of_prog_bv_ite_merge_else_else_bool c1 c2 t1 t2
      hC1NotStuck hC2NotStuck hT1NotStuck hT2NotStuck hResultTy with
    ⟨hC1Type, hC2Type, _hT1T2, _hT1NN⟩
  have hC1SmtTy := smt_typeof_c1_bitvec_one c1 hC1Trans hC1Type
  have hC2SmtTy := smt_typeof_c1_bitvec_one c2 hC2Trans hC2Type
  rcases eval_bv1_of_smt_type_bitvec_one M hM c1 hC1Trans hC1SmtTy with
    ⟨b1, hC1Eval⟩
  rcases eval_bv1_of_smt_type_bitvec_one M hM c2 hC2Trans hC2SmtTy with
    ⟨b2, hC2Eval⟩
  have hC1Eq := eval_eq_bv1_one M c1 b1 hC1Eval
  have hC2Eq := eval_eq_bv1_one M c2 b2 hC2Eval
  have hCondEval :
      __smtx_model_eval M (__eo_to_smt (mergeElseElseCond c1 c2)) =
        bv1 (!b1 && b2) :=
    eval_merge_else_else_cond M c1 c2 b1 b2 hC1Eval hC2Eval
  have hCondEq :=
    eval_eq_bv1_one M (mergeElseElseCond c1 c2) (!b1 && b2) hCondEval
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c1) (SmtTerm.Binary 1 1))
        (__eo_to_smt t2)
        (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c2) (SmtTerm.Binary 1 1))
          (__eo_to_smt t1) (__eo_to_smt t2))) =
    __smtx_model_eval M
      (SmtTerm.ite
        (SmtTerm.eq (__eo_to_smt (mergeElseElseCond c1 c2))
          (SmtTerm.Binary 1 1))
        (__eo_to_smt t1) (__eo_to_smt t2))
  rw [smtx_eval_ite_term_eq, hC1Eq]
  rw [smtx_eval_ite_term_eq, hC2Eq]
  rw [smtx_eval_ite_term_eq, hCondEq]
  cases b1 <;> cases b2 <;> rfl

private theorem facts___eo_prog_bv_ite_merge_else_else_impl
    (M : SmtModel) (hM : model_wf M) (c1 c2 t1 t2 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    RuleProofs.eo_has_smt_translation c2 ->
    RuleProofs.eo_has_smt_translation t1 ->
    RuleProofs.eo_has_smt_translation t2 ->
    __eo_typeof (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) = Term.Bool ->
    eo_interprets M (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) true := by
  intro hC1Trans hC2Trans hT1Trans hT2Trans hResultTy
  have hC1NotStuck : c1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c1 hC1Trans
  have hC2NotStuck : c2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation c2 hC2Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hT2NotStuck : t2 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t2 hT2Trans
  have hProgBool : RuleProofs.eo_has_bool_type
      (__eo_prog_bv_ite_merge_else_else c1 c2 t1 t2) :=
    typed___eo_prog_bv_ite_merge_else_else_impl c1 c2 t1 t2 hC1Trans
      hC2Trans hT1Trans hT2Trans hResultTy
  rw [prog_bv_ite_merge_else_else_eq_of_ne_stuck c1 c2 t1 t2 hC1NotStuck
    hC2NotStuck hT1NotStuck hT2NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bv_ite_merge_else_else_eq_of_ne_stuck c1 c2 t1 t2
      hC1NotStuck hC2NotStuck hT1NotStuck hT2NotStuck] using hProgBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mergeElseElseLhs c1 c2 t1 t2)))
      (__smtx_model_eval M (__eo_to_smt (mergeElseElseRhs c1 c2 t1 t2)))
    rw [eval_bvite_merge_else_else M hM c1 c2 t1 t2 hC1Trans hC2Trans
      hT1Trans hT2Trans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

public theorem cmd_step_bv_ite_merge_else_else_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_merge_else_else args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ite_merge_else_else args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_merge_else_else args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bv_ite_merge_else_else args premises ≠
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
                                RuleProofs.eo_has_smt_translation a4 ∧ True := by
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
                          change __eo_typeof
                              (__eo_prog_bv_ite_merge_else_else a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            change eo_interprets M
                              (__eo_prog_bv_ite_merge_else_else a1 a2 a3 a4) true
                            exact facts___eo_prog_bv_ite_merge_else_else_impl M hM
                              a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans
                              hA4Trans hResultTy
                          · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                              (typed___eo_prog_bv_ite_merge_else_else_impl
                                a1 a2 a3 a4 hA1Trans hA2Trans hA3Trans
                                hA4Trans hResultTy)
