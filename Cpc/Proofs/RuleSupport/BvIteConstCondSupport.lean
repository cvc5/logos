module

public import Cpc.Proofs.RuleSupport.BvIteEqualCond1Support
import all Cpc.Proofs.RuleSupport.BvIteEqualCond1Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- The width-one bit-vector constant `(int_to_bv 1 n)`. -/
def bvConst1 (n : native_Int) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral n)

theorem prog_bv_ite_const_cond_1_eq_of_ne_stuck (t1 e1 : Term) :
    t1 ≠ Term.Stuck ->
    e1 ≠ Term.Stuck ->
    __eo_prog_bv_ite_const_cond_1 t1 e1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvIte (bvConst1 1) t1 e1)) t1 := by
  intro hT1 hE1
  rw [__eo_prog_bv_ite_const_cond_1.eq_3 t1 e1 hT1 hE1]
  rfl

theorem prog_bv_ite_const_cond_2_eq_of_ne_stuck (t1 e1 : Term) :
    t1 ≠ Term.Stuck ->
    e1 ≠ Term.Stuck ->
    __eo_prog_bv_ite_const_cond_2 t1 e1 =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvIte (bvConst1 0) t1 e1)) e1 := by
  intro hT1 hE1
  rw [__eo_prog_bv_ite_const_cond_2.eq_3 t1 e1 hT1 hE1]
  rfl

/-- Well-typedness of `(= (bvite c t e) r)` gives equal branch types. -/
theorem typeof_branches_of_bvite_eq_bool (c t e r : Term) :
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvIte c t e)) r) = Term.Bool ->
    __eo_typeof t = __eo_typeof e := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof_bvite (__eo_typeof c) (__eo_typeof t) (__eo_typeof e))
      (__eo_typeof r) = Term.Bool at hTy
  have hNN :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof_bvite (__eo_typeof c) (__eo_typeof t) (__eo_typeof e))
      (__eo_typeof r) hTy).1
  exact (typeof_bvite_args_of_ne_stuck
    (__eo_typeof c) (__eo_typeof t) (__eo_typeof e) hNN).2.1

theorem smt_typeof_bv_const1 (n : native_Int) (hn : n = 0 ∨ n = 1) :
    __smtx_typeof (__eo_to_smt (bvConst1 n)) = SmtType.BitVec 1 := by
  rcases hn with rfl | rfl <;> decide +kernel

theorem smt_eval_bv_const1 (M : SmtModel) (n : native_Int) (hn : n = 0 ∨ n = 1) :
    __smtx_model_eval M (__eo_to_smt (bvConst1 n)) = SmtValue.Binary 1 n := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral n)) =
    SmtValue.Binary 1 n
  rcases hn with rfl | rfl
  · simp [native_ite, SmtEval.native_zleq]
    decide +kernel
  · simp [native_ite, SmtEval.native_zleq]
    decide +kernel

private theorem smt_eval_binary_one_one (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.Binary 1 1) = SmtValue.Binary 1 1 := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- `(= (bvite c t e) r)` is Boolean when `r` is one of the branches. -/
theorem has_bool_type_bvite_const_eq (n : native_Int) (hn : n = 0 ∨ n = 1)
    (t e r : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.eo_has_smt_translation e ->
    (r = t ∨ r = e) ->
    __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvIte (bvConst1 n) t e)) r) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvIte (bvConst1 n) t e)) r) := by
  intro hTTrans hETrans hR hTy
  have hTE := typeof_branches_of_bvite_eq_bool (bvConst1 n) t e r hTy
  have hESame :
      __smtx_typeof (__eo_to_smt e) = __smtx_typeof (__eo_to_smt t) :=
    smt_type_eq_of_same_eo_type t e (__eo_typeof t) hTTrans hETrans rfl hTE.symm
  have hIteTy :
      __smtx_typeof (__eo_to_smt (bvIte (bvConst1 n) t e)) =
        __smtx_typeof (__eo_to_smt t) :=
    smt_typeof_bvite_of_smt_types (bvConst1 n) t e (__smtx_typeof (__eo_to_smt t))
      (smt_typeof_bv_const1 n hn) rfl hESame
  have hRTy : __smtx_typeof (__eo_to_smt r) = __smtx_typeof (__eo_to_smt t) := by
    rcases hR with rfl | rfl
    · rfl
    · exact hESame
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvIte (bvConst1 n) t e) r (by rw [hIteTy, hRTy])
    (by rw [hIteTy]; exact hTTrans)

theorem eval_bvite_const1_one (M : SmtModel) (t e : Term) :
    __smtx_model_eval M (__eo_to_smt (bvIte (bvConst1 1) t e)) =
      __smtx_model_eval M (__eo_to_smt t) := by
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt (bvConst1 1)) (SmtTerm.Binary 1 1))
        (__eo_to_smt t) (__eo_to_smt e)) =
    __smtx_model_eval M (__eo_to_smt t)
  rw [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq,
    smt_eval_bv_const1 M 1 (Or.inr rfl), smt_eval_binary_one_one M]
  simp [__smtx_model_eval_eq, __smtx_model_eval_ite, native_veq]

theorem eval_bvite_const1_zero (M : SmtModel) (t e : Term) :
    __smtx_model_eval M (__eo_to_smt (bvIte (bvConst1 0) t e)) =
      __smtx_model_eval M (__eo_to_smt e) := by
  change __smtx_model_eval M
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt (bvConst1 0)) (SmtTerm.Binary 1 1))
        (__eo_to_smt t) (__eo_to_smt e)) =
    __smtx_model_eval M (__eo_to_smt e)
  rw [smtx_eval_ite_term_eq, smtx_eval_eq_term_eq,
    smt_eval_bv_const1 M 0 (Or.inl rfl), smt_eval_binary_one_one M]
  simp [__smtx_model_eval_eq, __smtx_model_eval_ite, native_veq]
