module

public import Cpc.Proofs.RuleSupport.ArithSimpleSupport
import all Cpc.Proofs.RuleSupport.ArithSimpleSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace ArithAbsRealGt

private abbrev negTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.__eoo_neg_2) t

private abbrev absTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.abs) t

private abbrev gtTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s

private abbrev geqTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s

private abbrev iteTerm (c t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) s

private abbrev eqTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s

private abbrev zeroTerm : Term := Term.Rational (native_mk_rational 0 1)

/-- The right-hand-side of the abs-real-gt equation, as nested ites by sign. -/
private abbrev rhsTerm (x1 y1 : Term) : Term :=
  iteTerm (geqTerm x1 zeroTerm)
    (iteTerm (geqTerm y1 zeroTerm) (gtTerm x1 y1) (gtTerm x1 (negTerm y1)))
    (iteTerm (geqTerm y1 zeroTerm) (gtTerm (negTerm x1) y1)
      (gtTerm (negTerm x1) (negTerm y1)))

private abbrev resultTerm (x1 y1 : Term) : Term :=
  eqTerm (gtTerm (absTerm x1) (absTerm y1)) (rhsTerm x1 y1)

/-- Stable model-eval rewrites. -/
private theorem eval_gt (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.gt a b) =
      __smtx_model_eval_gt (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_geq (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.geq a b) =
      __smtx_model_eval_geq (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_abs (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.abs a) =
      __smtx_model_eval_abs (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_uneg (M : SmtModel) (a : SmtTerm) :
    __smtx_model_eval M (SmtTerm.uneg a) =
      __smtx_model_eval_uneg (__smtx_model_eval M a) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- abs eval on an integer value. -/
private theorem eval_abs_real (M : SmtModel) (x : Term) (n : native_Rat)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Rational n) :
    __smtx_model_eval M (__eo_to_smt (absTerm x)) =
      SmtValue.Rational (if n < 0 then -n else n) := by
  rw [show __eo_to_smt (absTerm x) = SmtTerm.abs (__eo_to_smt x) by rfl]
  rw [eval_abs, hx]
  by_cases hneg : n < 0
  · simp [__smtx_model_eval_abs, native_qabs, hneg]
  · simp [__smtx_model_eval_abs, native_qabs, hneg]

/-- uneg eval on an integer value. -/
private theorem eval_neg_real (M : SmtModel) (x : Term) (n : native_Rat)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Rational n) :
    __smtx_model_eval M (__eo_to_smt (negTerm x)) = SmtValue.Rational (-n) := by
  rw [show __eo_to_smt (negTerm x) = SmtTerm.uneg (__eo_to_smt x) by rfl]
  rw [eval_uneg, hx]
  simp [__smtx_model_eval_uneg, native_qneg]

/-- Rewrite the program to the explicit equation when args are non-stuck. -/
private theorem prog_eq_of_nonstuck (x1 y1 : Term)
    (hx : x1 ≠ Term.Stuck) (hy : y1 ≠ Term.Stuck) :
    __eo_prog_arith_abs_real_gt x1 y1 = resultTerm x1 y1 := by
  by_cases hxSt : x1 = Term.Stuck
  · exact False.elim (hx hxSt)
  by_cases hySt : y1 = Term.Stuck
  · exact False.elim (hy hySt)
  cases x1 <;> cases y1 <;>
    first
      | exact False.elim (hx rfl)
      | exact False.elim (hy rfl)
      | rfl

/-- `geq t 0` (integer zero) has eo-typeof Bool only when `t` has eo-typeof Int. -/
private theorem real_of_geq_zero_bool (t : Term)
    (h : __eo_typeof (geqTerm t zeroTerm) = Term.Bool) :
    __eo_typeof t = Term.Real := by
  change __eo_typeof_lt (__eo_typeof t) Term.Real = Term.Bool at h
  cases hT : __eo_typeof t with
  | UOp op =>
    cases op <;>
      simp_all [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not]
  | _ =>
    simp_all [__eo_typeof_lt, __eo_requires, __eo_eq,
      native_ite, native_teq]

/-- `__eo_typeof_ite` is non-stuck only when its first argument (condition type)
    is `Bool`. -/
private theorem ite_cond_bool_of_not_stuck (C T E : Term)
    (h : __eo_typeof_ite C T E ≠ Term.Stuck) : C = Term.Bool := by
  cases C <;>
    first
      | rfl
      | (exfalso; apply h; cases T <;> cases E <;> rfl)

/-- The outer condition of the RHS is `geq x1 0`; the inner condition is `geq y1 0`.
    Non-stuck RHS forces both conditions to be Bool. -/
private theorem rhs_conds_bool (x1 y1 : Term)
    (h : __eo_typeof (rhsTerm x1 y1) ≠ Term.Stuck) :
    __eo_typeof (geqTerm x1 zeroTerm) = Term.Bool ∧
      __eo_typeof (geqTerm y1 zeroTerm) = Term.Bool := by
  change __eo_typeof_ite (__eo_typeof (geqTerm x1 zeroTerm))
    (__eo_typeof
      (iteTerm (geqTerm y1 zeroTerm) (gtTerm x1 y1) (gtTerm x1 (negTerm y1))))
    (__eo_typeof
      (iteTerm (geqTerm y1 zeroTerm) (gtTerm (negTerm x1) y1)
        (gtTerm (negTerm x1) (negTerm y1)))) ≠ Term.Stuck at h
  have hCondX : __eo_typeof (geqTerm x1 zeroTerm) = Term.Bool :=
    ite_cond_bool_of_not_stuck _ _ _ h
  -- then branch typeof not stuck => its condition Bool
  have hThenNotStuck :
      __eo_typeof
        (iteTerm (geqTerm y1 zeroTerm) (gtTerm x1 y1) (gtTerm x1 (negTerm y1)))
        ≠ Term.Stuck := by
    intro hStuck
    apply h
    rw [hCondX, hStuck, __eo_typeof_ite]
  have hCondY : __eo_typeof (geqTerm y1 zeroTerm) = Term.Bool := by
    have heq : __eo_typeof
        (iteTerm (geqTerm y1 zeroTerm) (gtTerm x1 y1) (gtTerm x1 (negTerm y1))) =
        __eo_typeof_ite (__eo_typeof (geqTerm y1 zeroTerm))
          (__eo_typeof (gtTerm x1 y1)) (__eo_typeof (gtTerm x1 (negTerm y1))) := rfl
    rw [heq] at hThenNotStuck
    exact ite_cond_bool_of_not_stuck _ _ _ hThenNotStuck
  exact ⟨hCondX, hCondY⟩

/-- From result being Bool, both args are eo-Int. -/
private theorem arg_types_real (x1 y1 : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x1)
    (hyTrans : RuleProofs.eo_has_smt_translation y1)
    (hResultTy : __eo_typeof (__eo_prog_arith_abs_real_gt x1 y1) = Term.Bool) :
    __eo_typeof x1 = Term.Real ∧ __eo_typeof y1 = Term.Real := by
  have hx : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x1 hxTrans
  have hy : y1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation y1 hyTrans
  rw [prog_eq_of_nonstuck x1 y1 hx hy] at hResultTy
  change __eo_typeof_eq (__eo_typeof (gtTerm (absTerm x1) (absTerm y1)))
      (__eo_typeof (rhsTerm x1 y1)) = Term.Bool at hResultTy
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hConds := rhs_conds_bool x1 y1 hRightNotStuck
  exact ⟨real_of_geq_zero_bool x1 hConds.1, real_of_geq_zero_bool y1 hConds.2⟩

/-- SMT type of each arg is Int. -/
private theorem smt_real_of_eo_real (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof t = Term.Real) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
  RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Real (__eo_to_smt t) rfl hTrans hTy

/-- SMT type of abs of an int-typed term is Int. -/
private theorem smt_abs_real (t : Term)
    (hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (absTerm t)) = SmtType.Real := by
  rw [show __eo_to_smt (absTerm t) = SmtTerm.abs (__eo_to_smt t) by rfl]
  rw [typeof_abs_eq, hSmt]
  simp [__smtx_typeof_arith_overload_op_1]

/-- SMT type of uneg of an int-typed term is Int. -/
private theorem smt_neg_real (t : Term)
    (hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (negTerm t)) = SmtType.Real := by
  rw [show __eo_to_smt (negTerm t) = SmtTerm.uneg (__eo_to_smt t) by rfl]
  rw [typeof_uneg_eq, hSmt]
  simp [__smtx_typeof_arith_overload_op_1]

private theorem smt_gt_bool (a b : Term)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (gtTerm a b)) = SmtType.Bool := by
  rw [show __eo_to_smt (gtTerm a b) = SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) by rfl]
  rw [typeof_gt_eq, ha, hb]
  simp [__smtx_typeof_arith_overload_op_2_ret]

private theorem smt_geq_bool (a b : Term)
    (ha : __smtx_typeof (__eo_to_smt a) = SmtType.Real)
    (hb : __smtx_typeof (__eo_to_smt b) = SmtType.Real) :
    __smtx_typeof (__eo_to_smt (geqTerm a b)) = SmtType.Bool := by
  rw [show __eo_to_smt (geqTerm a b) = SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) by rfl]
  rw [typeof_geq_eq, ha, hb]
  simp [__smtx_typeof_arith_overload_op_2_ret]

private theorem smt_ite_bool (c t e : Term)
    (hc : __smtx_typeof (__eo_to_smt c) = SmtType.Bool)
    (ht : __smtx_typeof (__eo_to_smt t) = SmtType.Bool)
    (he : __smtx_typeof (__eo_to_smt e) = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt (iteTerm c t e)) = SmtType.Bool := by
  rw [show __eo_to_smt (iteTerm c t e) =
      SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e) by rfl]
  rw [typeof_ite_eq, hc, ht, he]
  simp [__smtx_typeof_ite, native_Teq, native_ite]

private theorem zero_smt_real :
    __smtx_typeof (__eo_to_smt zeroTerm) = SmtType.Real := by
  change __smtx_typeof (SmtTerm.Rational (native_mk_rational 0 1)) = SmtType.Real
  rw [__smtx_typeof.eq_3]

/-- Type-preservation: the result has SMT Bool type. -/
private theorem typed_result (x1 y1 : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x1)
    (hyTrans : RuleProofs.eo_has_smt_translation y1)
    (hxTy : __eo_typeof x1 = Term.Real)
    (hyTy : __eo_typeof y1 = Term.Real) :
    RuleProofs.eo_has_bool_type (resultTerm x1 y1) := by
  have hxSmt := smt_real_of_eo_real x1 hxTrans hxTy
  have hySmt := smt_real_of_eo_real y1 hyTrans hyTy
  have hNegX := smt_neg_real x1 hxSmt
  have hNegY := smt_neg_real y1 hySmt
  have hAbsX := smt_abs_real x1 hxSmt
  have hAbsY := smt_abs_real y1 hySmt
  have hZero := zero_smt_real
  have hLhs : __smtx_typeof (__eo_to_smt (gtTerm (absTerm x1) (absTerm y1))) = SmtType.Bool :=
    smt_gt_bool (absTerm x1) (absTerm y1) hAbsX hAbsY
  have hCondX : __smtx_typeof (__eo_to_smt (geqTerm x1 zeroTerm)) = SmtType.Bool :=
    smt_geq_bool x1 zeroTerm hxSmt hZero
  have hCondY : __smtx_typeof (__eo_to_smt (geqTerm y1 zeroTerm)) = SmtType.Bool :=
    smt_geq_bool y1 zeroTerm hySmt hZero
  have hG_xy := smt_gt_bool x1 y1 hxSmt hySmt
  have hG_xny := smt_gt_bool x1 (negTerm y1) hxSmt hNegY
  have hG_nxy := smt_gt_bool (negTerm x1) y1 hNegX hySmt
  have hG_nxny := smt_gt_bool (negTerm x1) (negTerm y1) hNegX hNegY
  have hThen := smt_ite_bool (geqTerm y1 zeroTerm) (gtTerm x1 y1) (gtTerm x1 (negTerm y1))
    hCondY hG_xy hG_xny
  have hElse := smt_ite_bool (geqTerm y1 zeroTerm) (gtTerm (negTerm x1) y1)
    (gtTerm (negTerm x1) (negTerm y1)) hCondY hG_nxy hG_nxny
  have hRhs : __smtx_typeof (__eo_to_smt (rhsTerm x1 y1)) = SmtType.Bool :=
    smt_ite_bool (geqTerm x1 zeroTerm) _ _ hCondX hThen hElse
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (gtTerm (absTerm x1) (absTerm y1)) (rhsTerm x1 y1)
    (by rw [hLhs, hRhs]) (by rw [hLhs]; simp)

/-- The core integer arithmetic identity expressed at the value level. -/
private theorem eval_rel (M : SmtModel) (hM : model_wf M) (x1 y1 : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x1)
    (hyTrans : RuleProofs.eo_has_smt_translation y1)
    (hxTy : __eo_typeof x1 = Term.Real)
    (hyTy : __eo_typeof y1 = Term.Real) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (gtTerm (absTerm x1) (absTerm y1))))
      (__smtx_model_eval M (__eo_to_smt (rhsTerm x1 y1))) := by
  have hxSmt := smt_real_of_eo_real x1 hxTrans hxTy
  have hySmt := smt_real_of_eo_real y1 hyTrans hyTy
  rcases smt_eval_real_of_type M hM x1 hxSmt with ⟨a, hEvalX⟩
  rcases smt_eval_real_of_type M hM y1 hySmt with ⟨b, hEvalY⟩
  have hAbsX := eval_abs_real M x1 a hEvalX
  have hAbsY := eval_abs_real M y1 b hEvalY
  have hNegX := eval_neg_real M x1 a hEvalX
  have hNegY := eval_neg_real M y1 b hEvalY
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (gtTerm (absTerm x1) (absTerm y1))) =
        SmtValue.Boolean (native_qlt (if b < 0 then -b else b) (if a < 0 then -a else a)) := by
    rw [show __eo_to_smt (gtTerm (absTerm x1) (absTerm y1)) =
        SmtTerm.gt (__eo_to_smt (absTerm x1)) (__eo_to_smt (absTerm y1)) by rfl]
    rw [eval_gt, hAbsX, hAbsY]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt (rhsTerm x1 y1)) =
        SmtValue.Boolean
          (if 0 ≤ a then
            (if 0 ≤ b then native_qlt b a else native_qlt (-b) a)
          else
            (if 0 ≤ b then native_qlt b (-a) else native_qlt (-b) (-a))) := by
    rw [show __eo_to_smt (rhsTerm x1 y1) =
        SmtTerm.ite (__eo_to_smt (geqTerm x1 zeroTerm))
          (SmtTerm.ite (__eo_to_smt (geqTerm y1 zeroTerm))
            (__eo_to_smt (gtTerm x1 y1)) (__eo_to_smt (gtTerm x1 (negTerm y1))))
          (SmtTerm.ite (__eo_to_smt (geqTerm y1 zeroTerm))
            (__eo_to_smt (gtTerm (negTerm x1) y1))
            (__eo_to_smt (gtTerm (negTerm x1) (negTerm y1)))) by rfl]
    have hEvalZero : __smtx_model_eval M (__eo_to_smt zeroTerm) = SmtValue.Rational (native_mk_rational 0 1) := by
      change __smtx_model_eval M (SmtTerm.Rational (native_mk_rational 0 1)) = SmtValue.Rational (native_mk_rational 0 1)
      rw [__smtx_model_eval.eq_3]
    have hGeqX :
        __smtx_model_eval M (__eo_to_smt (geqTerm x1 zeroTerm)) =
          SmtValue.Boolean (native_qleq 0 a) := by
      rw [show __eo_to_smt (geqTerm x1 zeroTerm) =
          SmtTerm.geq (__eo_to_smt x1) (__eo_to_smt zeroTerm) by rfl]
      rw [eval_geq, hEvalX, hEvalZero]
      simp [__smtx_model_eval_geq, __smtx_model_eval_leq]
      have hZeroRat : native_mk_rational 0 1 = (0 : native_Rat) := by native_decide
      rw [hZeroRat]
    have hGeqY :
        __smtx_model_eval M (__eo_to_smt (geqTerm y1 zeroTerm)) =
          SmtValue.Boolean (native_qleq 0 b) := by
      rw [show __eo_to_smt (geqTerm y1 zeroTerm) =
          SmtTerm.geq (__eo_to_smt y1) (__eo_to_smt zeroTerm) by rfl]
      rw [eval_geq, hEvalY, hEvalZero]
      simp [__smtx_model_eval_geq, __smtx_model_eval_leq]
      have hZeroRat : native_mk_rational 0 1 = (0 : native_Rat) := by native_decide
      rw [hZeroRat]
    have hGT_xy :
        __smtx_model_eval M (__eo_to_smt (gtTerm x1 y1)) =
          SmtValue.Boolean (native_qlt b a) := by
      rw [show __eo_to_smt (gtTerm x1 y1) =
          SmtTerm.gt (__eo_to_smt x1) (__eo_to_smt y1) by rfl]
      rw [eval_gt, hEvalX, hEvalY]; simp [__smtx_model_eval_gt, __smtx_model_eval_lt]
    have hGT_xny :
        __smtx_model_eval M (__eo_to_smt (gtTerm x1 (negTerm y1))) =
          SmtValue.Boolean (native_qlt (-b) a) := by
      rw [show __eo_to_smt (gtTerm x1 (negTerm y1)) =
          SmtTerm.gt (__eo_to_smt x1) (__eo_to_smt (negTerm y1)) by rfl]
      rw [eval_gt, hEvalX, hNegY]; simp [__smtx_model_eval_gt, __smtx_model_eval_lt]
    have hGT_nxy :
        __smtx_model_eval M (__eo_to_smt (gtTerm (negTerm x1) y1)) =
          SmtValue.Boolean (native_qlt b (-a)) := by
      rw [show __eo_to_smt (gtTerm (negTerm x1) y1) =
          SmtTerm.gt (__eo_to_smt (negTerm x1)) (__eo_to_smt y1) by rfl]
      rw [eval_gt, hNegX, hEvalY]; simp [__smtx_model_eval_gt, __smtx_model_eval_lt]
    have hGT_nxny :
        __smtx_model_eval M (__eo_to_smt (gtTerm (negTerm x1) (negTerm y1))) =
          SmtValue.Boolean (native_qlt (-b) (-a)) := by
      rw [show __eo_to_smt (gtTerm (negTerm x1) (negTerm y1)) =
          SmtTerm.gt (__eo_to_smt (negTerm x1)) (__eo_to_smt (negTerm y1)) by rfl]
      rw [eval_gt, hNegX, hNegY]; simp [__smtx_model_eval_gt, __smtx_model_eval_lt]
    rw [smtx_eval_ite_term_eq, smtx_eval_ite_term_eq, smtx_eval_ite_term_eq,
      hGeqX, hGeqY, hGT_xy, hGT_xny, hGT_nxy, hGT_nxny]
    by_cases hA : 0 ≤ a
    · by_cases hB : 0 ≤ b
      · simp [native_qleq, __smtx_model_eval_ite, hA, hB]
      · simp [native_qleq, __smtx_model_eval_ite, hA, hB]
    · by_cases hB : 0 ≤ b
      · simp [native_qleq, __smtx_model_eval_ite, hA, hB]
      · simp [native_qleq, __smtx_model_eval_ite, hA, hB]
  unfold RuleProofs.smt_value_rel
  rw [hLhsEval, hRhsEval]
  have hEq :
      (native_qlt (if b < 0 then -b else b) (if a < 0 then -a else a)) =
        (if 0 ≤ a then
          (if 0 ≤ b then native_qlt b a else native_qlt (-b) a)
        else
          (if 0 ≤ b then native_qlt b (-a) else native_qlt (-b) (-a))) := by
    by_cases hA : 0 ≤ a
    · by_cases hB : 0 ≤ b
      · simp [hA, hB, native_qlt]
        grind
      · simp [hA, hB, native_qlt]
        grind
    · by_cases hB : 0 ≤ b
      · simp [hA, hB, native_qlt]
        grind
      · simp [hA, hB, native_qlt]
        grind
  rw [hEq]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem facts_result (M : SmtModel) (hM : model_wf M) (x1 y1 : Term)
    (hxTrans : RuleProofs.eo_has_smt_translation x1)
    (hyTrans : RuleProofs.eo_has_smt_translation y1)
    (hxTy : __eo_typeof x1 = Term.Real)
    (hyTy : __eo_typeof y1 = Term.Real) :
    eo_interprets M (resultTerm x1 y1) true := by
  have hBool := typed_result x1 y1 hxTrans hyTrans hxTy hyTy
  exact RuleProofs.eo_interprets_eq_of_rel M
    (gtTerm (absTerm x1) (absTerm y1)) (rhsTerm x1 y1)
    hBool
    (eval_rel M hM x1 y1 hxTrans hyTrans hxTy hyTy)

end ArithAbsRealGt

open ArithAbsRealGt in
public theorem cmd_step_arith_abs_real_gt_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_abs_real_gt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_abs_real_gt args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_abs_real_gt args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_abs_real_gt args premises ≠ Term.Stuck :=
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cArgListTranslationOk] using hArgsTrans.2.1
                  change __eo_typeof (__eo_prog_arith_abs_real_gt a1 a2) = Term.Bool
                    at hResultTy
                  have hArgTy := arg_types_real a1 a2 hA1Trans hA2Trans hResultTy
                  have hx : a1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a1 hA1Trans
                  have hy : a2 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_smt_translation a2 hA2Trans
                  have hProgEq := prog_eq_of_nonstuck a1 a2 hx hy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_arith_abs_real_gt a1 a2) true
                    rw [hProgEq]
                    exact facts_result M hM a1 a2 hA1Trans hA2Trans hArgTy.1 hArgTy.2
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_abs_real_gt a1 a2)
                    rw [hProgEq]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed_result a1 a2 hA1Trans hA2Trans hArgTy.1 hArgTy.2)
