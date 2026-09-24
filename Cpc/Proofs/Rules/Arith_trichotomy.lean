module

public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem term_ne_stuck_of_int_or_real_smt_type (t : Term) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rcases hTy with hTy | hTy <;>
    change __smtx_typeof SmtTerm.None = _ at hTy <;>
    rw [TranslationProofs.smtx_typeof_none] at hTy <;>
    cases hTy

private theorem arith_rel_neg_leq_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_neg (Term.UOp UserOp.leq) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_neg] at ha hb ⊢

private theorem arith_rel_neg_lt_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_neg (Term.UOp UserOp.lt) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_neg] at ha hb ⊢

private theorem arith_rel_neg_gt_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_neg (Term.UOp UserOp.gt) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_neg] at ha hb ⊢

private theorem arith_rel_neg_geq_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_neg (Term.UOp UserOp.geq) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_neg] at ha hb ⊢

private theorem arith_rel_trichotomy_eq_lt_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_trichotomy (Term.UOp UserOp.eq) (Term.UOp UserOp.lt) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_trichotomy] at ha hb ⊢

private theorem arith_rel_trichotomy_eq_gt_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_trichotomy (Term.UOp UserOp.eq) (Term.UOp UserOp.gt) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_trichotomy] at ha hb ⊢

private theorem arith_rel_trichotomy_gt_eq_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_trichotomy (Term.UOp UserOp.gt) (Term.UOp UserOp.eq) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_trichotomy] at ha hb ⊢

private theorem arith_rel_trichotomy_lt_eq_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_trichotomy (Term.UOp UserOp.lt) (Term.UOp UserOp.eq) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_trichotomy] at ha hb ⊢

private theorem arith_rel_trichotomy_gt_lt_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_trichotomy (Term.UOp UserOp.gt) (Term.UOp UserOp.lt) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_trichotomy] at ha hb ⊢

private theorem arith_rel_trichotomy_lt_gt_eq
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __arith_rel_trichotomy (Term.UOp UserOp.lt) (Term.UOp UserOp.gt) a b =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
  intro ha hb
  cases a <;> cases b <;> simp [__arith_rel_trichotomy] at ha hb ⊢

private theorem arith_rel_trichotomy_ne_stuck_cases
    (r1 r2 a b : Term) :
    __arith_rel_trichotomy r1 r2 a b ≠ Term.Stuck ->
    (r1 = Term.UOp UserOp.eq ∧ r2 = Term.UOp UserOp.lt) ∨
    (r1 = Term.UOp UserOp.eq ∧ r2 = Term.UOp UserOp.gt) ∨
    (r1 = Term.UOp UserOp.gt ∧ r2 = Term.UOp UserOp.eq) ∨
    (r1 = Term.UOp UserOp.lt ∧ r2 = Term.UOp UserOp.eq) ∨
    (r1 = Term.UOp UserOp.gt ∧ r2 = Term.UOp UserOp.lt) ∨
    (r1 = Term.UOp UserOp.lt ∧ r2 = Term.UOp UserOp.gt) := by
  intro hBodyNe
  by_cases hEqLt : r1 = Term.UOp UserOp.eq ∧ r2 = Term.UOp UserOp.lt
  · exact Or.inl hEqLt
  by_cases hEqGt : r1 = Term.UOp UserOp.eq ∧ r2 = Term.UOp UserOp.gt
  · exact Or.inr (Or.inl hEqGt)
  by_cases hGtEq : r1 = Term.UOp UserOp.gt ∧ r2 = Term.UOp UserOp.eq
  · exact Or.inr (Or.inr (Or.inl hGtEq))
  by_cases hLtEq : r1 = Term.UOp UserOp.lt ∧ r2 = Term.UOp UserOp.eq
  · exact Or.inr (Or.inr (Or.inr (Or.inl hLtEq)))
  by_cases hGtLt : r1 = Term.UOp UserOp.gt ∧ r2 = Term.UOp UserOp.lt
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hGtLt))))
  by_cases hLtGt : r1 = Term.UOp UserOp.lt ∧ r2 = Term.UOp UserOp.gt
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hLtGt))))
  exfalso
  simp [__arith_rel_trichotomy] at hBodyNe
  split at hBodyNe <;> simp at hBodyNe
  all_goals
    first
    | contradiction
    | rename_i hr1 hr2
      first
      | exact hEqLt ⟨hr1, hr2⟩
      | exact hEqGt ⟨hr1, hr2⟩
      | exact hGtEq ⟨hr1, hr2⟩
      | exact hLtEq ⟨hr1, hr2⟩
      | exact hGtLt ⟨hr1, hr2⟩
      | exact hLtGt ⟨hr1, hr2⟩

private theorem eo_requires_true_eq
    (body : Term) :
    __eo_requires (Term.Boolean true) (Term.Boolean true) body = body := by
  simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]

private theorem eo_and_eq_refl_true
    (a b : Term) :
    a ≠ Term.Stuck ->
    b ≠ Term.Stuck ->
    __eo_and (__eo_eq a a) (__eo_eq b b) = Term.Boolean true := by
  intro ha hb
  cases a <;> cases b <;>
    simp [__eo_and, __eo_eq, native_teq, SmtEval.native_and] at ha hb ⊢

private theorem left_ne_stuck_of_arith_types
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    a ≠ Term.Stuck := by
  rcases hTy with hInt | hReal
  · exact term_ne_stuck_of_int_or_real_smt_type a (Or.inl hInt.1)
  · exact term_ne_stuck_of_int_or_real_smt_type a (Or.inr hReal.1)

private theorem right_ne_stuck_of_arith_types
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    b ≠ Term.Stuck := by
  rcases hTy with hInt | hReal
  · exact term_ne_stuck_of_int_or_real_smt_type b (Or.inl hInt.2)
  · exact term_ne_stuck_of_int_or_real_smt_type b (Or.inr hReal.2)

private theorem eo_has_bool_type_lt_of_arith
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) := by
  rcases hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem eo_has_bool_type_gt_of_arith
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) := by
  rcases hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem eo_has_bool_type_eq_of_arith
    (a b : Term)
    (hTy :
      (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int) ∨
      (__smtx_typeof (__eo_to_smt a) = SmtType.Real ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  rcases hTy with hInt | hReal
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
      (by rw [hInt.1, hInt.2]) (by rw [hInt.1]; simp)
  · exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a b
      (by rw [hReal.1, hReal.2]) (by rw [hReal.1]; simp)

private theorem native_zlt_of_not_eq_not_gt {a b : native_Int} :
    native_zeq a b = false ->
    native_zlt b a = false ->
    native_zlt a b = true := by
  intro hEq hGt
  have hNe : a ≠ b := by
    simpa [native_zeq, SmtEval.native_zeq] using hEq
  have hNotGt : ¬ b < a := by
    simpa [native_zlt, SmtEval.native_zlt] using hGt
  have hLe : a ≤ b := Int.not_lt.mp hNotGt
  have hLt : a < b := by
    by_cases hlt : a < b
    · exact hlt
    · have hBA : b ≤ a := Int.not_lt.mp hlt
      have hEq : a = b := Int.le_antisymm hLe hBA
      exact False.elim (hNe hEq)
  simpa [native_zlt, SmtEval.native_zlt] using hLt

private theorem native_zgt_of_not_eq_not_lt {a b : native_Int} :
    native_zeq a b = false ->
    native_zlt a b = false ->
    native_zlt b a = true := by
  intro hEq hLt
  have hNe : a ≠ b := by
    simpa [native_zeq, SmtEval.native_zeq] using hEq
  have hNotLt : ¬ a < b := by
    simpa [native_zlt, SmtEval.native_zlt] using hLt
  have hLe : b ≤ a := Int.not_lt.mp hNotLt
  have hGt : b < a := by
    by_cases hgt : b < a
    · exact hgt
    · have hAB : a ≤ b := Int.not_lt.mp hgt
      have hEq : a = b := Int.le_antisymm hAB hLe
      exact False.elim (hNe hEq)
  simpa [native_zlt, SmtEval.native_zlt] using hGt

private theorem native_zeq_of_not_lt_not_gt {a b : native_Int} :
    native_zlt a b = false ->
    native_zlt b a = false ->
    native_zeq a b = true := by
  intro hLt hGt
  have hNotLt : ¬ a < b := by
    simpa [native_zlt, SmtEval.native_zlt] using hLt
  have hNotGt : ¬ b < a := by
    simpa [native_zlt, SmtEval.native_zlt] using hGt
  have hAB : a ≤ b := Int.not_lt.mp hNotGt
  have hBA : b ≤ a := Int.not_lt.mp hNotLt
  have hEq : a = b := Int.le_antisymm hAB hBA
  simpa [native_zeq, SmtEval.native_zeq] using hEq

private theorem native_qlt_of_not_eq_not_gt {a b : native_Rat} :
    native_qeq a b = false ->
    native_qlt b a = false ->
    native_qlt a b = true := by
  intro hEq hGt
  have hNe : a ≠ b := by
    simpa [native_qeq, Eo.native_qeq] using hEq
  have hNotGt : ¬ b < a := by
    simpa [native_qlt, SmtEval.native_qlt] using hGt
  have hLe : a ≤ b := Rat.not_lt.mp hNotGt
  have hLt : a < b := by
    by_cases hlt : a < b
    · exact hlt
    · have hBA : b ≤ a := Rat.not_lt.mp hlt
      have hEq : a = b := Rat.le_antisymm hLe hBA
      exact False.elim (hNe hEq)
  simpa [native_qlt, SmtEval.native_qlt] using hLt

private theorem native_qgt_of_not_eq_not_lt {a b : native_Rat} :
    native_qeq a b = false ->
    native_qlt a b = false ->
    native_qlt b a = true := by
  intro hEq hLt
  have hNe : a ≠ b := by
    simpa [native_qeq, Eo.native_qeq] using hEq
  have hNotLt : ¬ a < b := by
    simpa [native_qlt, SmtEval.native_qlt] using hLt
  have hLe : b ≤ a := Rat.not_lt.mp hNotLt
  have hLt' : b < a := by
    by_cases hgt : b < a
    · exact hgt
    · have hAB : a ≤ b := Rat.not_lt.mp hgt
      have hEq : a = b := Rat.le_antisymm hAB hLe
      exact False.elim (hNe hEq)
  simpa [native_qlt, SmtEval.native_qlt] using hLt'

private theorem native_qeq_of_not_lt_not_gt {a b : native_Rat} :
    native_qlt a b = false ->
    native_qlt b a = false ->
    native_qeq a b = true := by
  intro hLt hGt
  have hNotLt : ¬ a < b := by
    simpa [native_qlt, SmtEval.native_qlt] using hLt
  have hNotGt : ¬ b < a := by
    simpa [native_qlt, SmtEval.native_qlt] using hGt
  have hAB : a ≤ b := Rat.not_lt.mp hNotGt
  have hBA : b ≤ a := Rat.not_lt.mp hNotLt
  have hEq : a = b := Rat.le_antisymm hAB hBA
  simpa [native_qeq, Eo.native_qeq] using hEq

private theorem native_zlt_false_of_zleq_true {a b : native_Int} :
    native_zleq b a = true ->
    native_zlt a b = false := by
  intro hLe
  have hLe' : b ≤ a := by
    simpa [native_zleq, SmtEval.native_zleq] using hLe
  have hNotLt : ¬ a < b := Int.not_lt.mpr hLe'
  simpa [native_zlt, SmtEval.native_zlt] using hNotLt

private theorem native_zgt_false_of_zleq_true {a b : native_Int} :
    native_zleq a b = true ->
    native_zlt b a = false := by
  intro hLe
  have hLe' : a ≤ b := by
    simpa [native_zleq, SmtEval.native_zleq] using hLe
  have hNotGt : ¬ b < a := Int.not_lt.mpr hLe'
  simpa [native_zlt, SmtEval.native_zlt] using hNotGt

private theorem native_qlt_false_of_qleq_true {a b : native_Rat} :
    native_qleq b a = true ->
    native_qlt a b = false := by
  intro hLe
  have hLe' : b ≤ a := by
    simpa [native_qleq, Smtm.native_qleq] using hLe
  have hNotLt : ¬ a < b := Rat.not_lt.mpr hLe'
  simpa [native_qlt, SmtEval.native_qlt] using hNotLt

private theorem native_qgt_false_of_qleq_true {a b : native_Rat} :
    native_qleq a b = true ->
    native_qlt b a = false := by
  intro hLe
  have hLe' : a ≤ b := by
    simpa [native_qleq, Smtm.native_qleq] using hLe
  have hNotGt : ¬ b < a := Rat.not_lt.mpr hLe'
  simpa [native_qlt, SmtEval.native_qlt] using hNotGt

private theorem int_eq_false_of_eval
    (M : SmtModel) (a b : Term) {n m : native_Int}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Numeral n)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral m) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false ->
    native_zeq n m = false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [smtx_eval_eq_term_eq, ha, hb] at hEval
      simp [__smtx_model_eval_eq, native_veq] at hEval
      simp [native_zeq, SmtEval.native_zeq, hEval]

private theorem int_lt_false_of_eval
    (M : SmtModel) (a b : Term) {n m : native_Int}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Numeral n)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral m) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) false ->
    native_zlt n m = false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [__smtx_model_eval.eq_17, ha, hb] at hEval
      simpa [__smtx_model_eval_lt] using hEval

private theorem int_gt_false_of_eval
    (M : SmtModel) (a b : Term) {n m : native_Int}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Numeral n)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Numeral m) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) false ->
    native_zlt m n = false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_gt_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [__smtx_model_eval.eq_19, ha, hb] at hEval
      simpa [__smtx_model_eval_gt, __smtx_model_eval_lt] using hEval

private theorem real_eq_false_of_eval
    (M : SmtModel) (a b : Term) {q r : native_Rat}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Rational q)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Rational r) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false ->
    native_qeq q r = false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [smtx_eval_eq_term_eq, ha, hb] at hEval
      simp [__smtx_model_eval_eq, native_veq] at hEval
      simp [native_qeq, Eo.native_qeq, hEval]

private theorem real_lt_false_of_eval
    (M : SmtModel) (a b : Term) {q r : native_Rat}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Rational q)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Rational r) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) false ->
    native_qlt q r = false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_lt_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [__smtx_model_eval.eq_17, ha, hb] at hEval
      simpa [__smtx_model_eval_lt] using hEval

private theorem real_gt_false_of_eval
    (M : SmtModel) (a b : Term) {q r : native_Rat}
    (ha : __smtx_model_eval M (__eo_to_smt a) = SmtValue.Rational q)
    (hb : __smtx_model_eval M (__eo_to_smt b) = SmtValue.Rational r) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) false ->
    native_qlt r q = false := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_gt_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [__smtx_model_eval.eq_19, ha, hb] at hEval
      simpa [__smtx_model_eval_gt, __smtx_model_eval_lt] using hEval

private theorem lt_false_of_geq_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hGeqTrue :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) true)
    (hLtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b)) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) false := by
  rcases rel_operands_arith_type_of_lt_has_bool_type a b hLtBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM a hInt.1 with ⟨n, ha⟩
    rcases smt_eval_int_of_type M hM b hInt.2 with ⟨m, hb⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_geq_eq] at hGeqTrue
    cases hGeqTrue with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_20, ha, hb] at hEval
        simp [__smtx_model_eval_geq, __smtx_model_eval_leq] at hEval
        apply RuleProofs.eo_interprets_of_bool_eval M
        · exact hLtBool
        · rw [eo_to_smt_lt_eq, __smtx_model_eval.eq_17, ha, hb]
          simp [__smtx_model_eval_lt, native_zlt_false_of_zleq_true hEval]
  · rcases smt_eval_real_of_type M hM a hReal.1 with ⟨q, ha⟩
    rcases smt_eval_real_of_type M hM b hReal.2 with ⟨r, hb⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_geq_eq] at hGeqTrue
    cases hGeqTrue with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_20, ha, hb] at hEval
        simp [__smtx_model_eval_geq, __smtx_model_eval_leq] at hEval
        apply RuleProofs.eo_interprets_of_bool_eval M
        · exact hLtBool
        · rw [eo_to_smt_lt_eq, __smtx_model_eval.eq_17, ha, hb]
          simp [__smtx_model_eval_lt, native_qlt_false_of_qleq_true hEval]

private theorem gt_false_of_leq_true
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hLeqTrue :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) true)
    (hGtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b)) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) false := by
  rcases rel_operands_arith_type_of_gt_has_bool_type a b hGtBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM a hInt.1 with ⟨n, ha⟩
    rcases smt_eval_int_of_type M hM b hInt.2 with ⟨m, hb⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_leq_eq] at hLeqTrue
    cases hLeqTrue with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_18, ha, hb] at hEval
        simp [__smtx_model_eval_leq] at hEval
        apply RuleProofs.eo_interprets_of_bool_eval M
        · exact hGtBool
        · rw [eo_to_smt_gt_eq, __smtx_model_eval.eq_19, ha, hb]
          simp [__smtx_model_eval_gt, __smtx_model_eval_lt,
            native_zgt_false_of_zleq_true hEval]
  · rcases smt_eval_real_of_type M hM a hReal.1 with ⟨q, ha⟩
    rcases smt_eval_real_of_type M hM b hReal.2 with ⟨r, hb⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets, eo_to_smt_leq_eq] at hLeqTrue
    cases hLeqTrue with
    | intro_true _ hEval =>
        rw [__smtx_model_eval.eq_18, ha, hb] at hEval
        simp [__smtx_model_eval_leq] at hEval
        apply RuleProofs.eo_interprets_of_bool_eval M
        · exact hGtBool
        · rw [eo_to_smt_gt_eq, __smtx_model_eval.eq_19, ha, hb]
          simp [__smtx_model_eval_gt, __smtx_model_eval_lt,
            native_qgt_false_of_qleq_true hEval]

private theorem gt_true_of_eq_false_lt_false
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hEqFalse :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false)
    (hLtFalse :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) false)
    (hGtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b)) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) true := by
  rcases rel_operands_arith_type_of_gt_has_bool_type a b hGtBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM a hInt.1 with ⟨n, ha⟩
    rcases smt_eval_int_of_type M hM b hInt.2 with ⟨m, hb⟩
    have hEqB := int_eq_false_of_eval M a b ha hb hEqFalse
    have hLtB := int_lt_false_of_eval M a b ha hb hLtFalse
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hGtBool
    · rw [eo_to_smt_gt_eq, __smtx_model_eval.eq_19, ha, hb]
      simpa [__smtx_model_eval_gt, __smtx_model_eval_lt] using
        native_zgt_of_not_eq_not_lt hEqB hLtB
  · rcases smt_eval_real_of_type M hM a hReal.1 with ⟨q, ha⟩
    rcases smt_eval_real_of_type M hM b hReal.2 with ⟨r, hb⟩
    have hEqB := real_eq_false_of_eval M a b ha hb hEqFalse
    have hLtB := real_lt_false_of_eval M a b ha hb hLtFalse
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hGtBool
    · rw [eo_to_smt_gt_eq, __smtx_model_eval.eq_19, ha, hb]
      simpa [__smtx_model_eval_gt, __smtx_model_eval_lt] using
        native_qgt_of_not_eq_not_lt hEqB hLtB

private theorem lt_true_of_eq_false_gt_false
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hEqFalse :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false)
    (hGtFalse :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) false)
    (hLtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b)) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) true := by
  rcases rel_operands_arith_type_of_lt_has_bool_type a b hLtBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM a hInt.1 with ⟨n, ha⟩
    rcases smt_eval_int_of_type M hM b hInt.2 with ⟨m, hb⟩
    have hEqB := int_eq_false_of_eval M a b ha hb hEqFalse
    have hGtB := int_gt_false_of_eval M a b ha hb hGtFalse
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hLtBool
    · rw [eo_to_smt_lt_eq, __smtx_model_eval.eq_17, ha, hb]
      simpa [__smtx_model_eval_lt] using
        native_zlt_of_not_eq_not_gt hEqB hGtB
  · rcases smt_eval_real_of_type M hM a hReal.1 with ⟨q, ha⟩
    rcases smt_eval_real_of_type M hM b hReal.2 with ⟨r, hb⟩
    have hEqB := real_eq_false_of_eval M a b ha hb hEqFalse
    have hGtB := real_gt_false_of_eval M a b ha hb hGtFalse
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hLtBool
    · rw [eo_to_smt_lt_eq, __smtx_model_eval.eq_17, ha, hb]
      simpa [__smtx_model_eval_lt] using
        native_qlt_of_not_eq_not_gt hEqB hGtB

private theorem eq_true_of_lt_false_gt_false
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hLtFalse :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) false)
    (hGtFalse :
      eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) false)
    (hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true := by
  have hLtBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hLtFalse
  rcases rel_operands_arith_type_of_lt_has_bool_type a b hLtBool with hInt | hReal
  · rcases smt_eval_int_of_type M hM a hInt.1 with ⟨n, ha⟩
    rcases smt_eval_int_of_type M hM b hInt.2 with ⟨m, hb⟩
    have hLtB := int_lt_false_of_eval M a b ha hb hLtFalse
    have hGtB := int_gt_false_of_eval M a b ha hb hGtFalse
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hEqBool
    · rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq, ha, hb]
      have hEqVal : n = m := by
        simpa [native_zeq, SmtEval.native_zeq] using
          native_zeq_of_not_lt_not_gt hLtB hGtB
      simp [__smtx_model_eval_eq, native_veq, hEqVal]
  · rcases smt_eval_real_of_type M hM a hReal.1 with ⟨q, ha⟩
    rcases smt_eval_real_of_type M hM b hReal.2 with ⟨r, hb⟩
    have hLtB := real_lt_false_of_eval M a b ha hb hLtFalse
    have hGtB := real_gt_false_of_eval M a b ha hb hGtFalse
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hEqBool
    · rw [eo_to_smt_eq_eq, smtx_eval_eq_term_eq, ha, hb]
      have hEqVal : q = r := by
        simpa [native_qeq, Eo.native_qeq] using
          native_qeq_of_not_lt_not_gt hLtB hGtB
      simp [__smtx_model_eval_eq, native_veq, hEqVal]

private theorem arith_normalize_lit_not_lt_has_bool_type
    (F a b : Term) :
    RuleProofs.eo_has_bool_type F ->
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F) =
      Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) := by
  intro hF hNorm
  cases F with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x <;> simp [__arith_normalize_lit] at hNorm
              case Apply g y =>
                cases g <;> simp at hNorm
                case Apply r x =>
                  have hXBool :
                      RuleProofs.eo_has_bool_type
                        (Term.Apply (Term.Apply r x) y) :=
                    RuleProofs.eo_has_bool_type_not_arg _ hF
                  simpa [hNorm] using hXBool
          | _ =>
              simp [__arith_normalize_lit] at hNorm
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | lt =>
                  have hArith := rel_operands_arith_type_of_lt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.lt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_lt_eq y x hy hx] at hNorm
                  cases hNorm
              | leq =>
                  have hArith := rel_operands_arith_type_of_leq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.leq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_leq_eq y x hy hx] at hNorm
                  cases hNorm
              | gt =>
                  have hArith := rel_operands_arith_type_of_gt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.gt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_gt_eq y x hy hx] at hNorm
                  cases hNorm
              | geq =>
                  have hArith := rel_operands_arith_type_of_geq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.geq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_geq_eq y x hy hx] at hNorm
                  have hLtBool := eo_has_bool_type_lt_of_arith y x hArith
                  simpa [hNorm] using hLtBool
              | _ =>
                  simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
                  split at hNorm <;> simp at hNorm
                  all_goals simp at *
          | _ =>
              simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
              split at hNorm <;> simp at hNorm
              all_goals
                first
                | contradiction
                | rename_i hEq
                  cases hEq
      | _ =>
          simp [__arith_normalize_lit] at hNorm
  | _ =>
      simp [__arith_normalize_lit] at hNorm

private theorem arith_normalize_lit_not_gt_has_bool_type
    (F a b : Term) :
    RuleProofs.eo_has_bool_type F ->
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F) =
      Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) := by
  intro hF hNorm
  cases F with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x <;> simp [__arith_normalize_lit] at hNorm
              case Apply g y =>
                cases g <;> simp at hNorm
                case Apply r x =>
                  have hXBool :
                      RuleProofs.eo_has_bool_type
                        (Term.Apply (Term.Apply r x) y) :=
                    RuleProofs.eo_has_bool_type_not_arg _ hF
                  simpa [hNorm] using hXBool
          | _ =>
              simp [__arith_normalize_lit] at hNorm
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | lt =>
                  have hArith := rel_operands_arith_type_of_lt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.lt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_lt_eq y x hy hx] at hNorm
                  cases hNorm
              | leq =>
                  have hArith := rel_operands_arith_type_of_leq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.leq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_leq_eq y x hy hx] at hNorm
                  have hGtBool := eo_has_bool_type_gt_of_arith y x hArith
                  simpa [hNorm] using hGtBool
              | gt =>
                  have hArith := rel_operands_arith_type_of_gt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.gt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_gt_eq y x hy hx] at hNorm
                  cases hNorm
              | geq =>
                  have hArith := rel_operands_arith_type_of_geq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.geq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_geq_eq y x hy hx] at hNorm
                  cases hNorm
              | _ =>
                  simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
                  split at hNorm <;> simp at hNorm
                  all_goals simp at *
          | _ =>
              simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
              split at hNorm <;> simp at hNorm
              all_goals
                first
                | contradiction
                | rename_i hEq
                  cases hEq
      | _ =>
          simp [__arith_normalize_lit] at hNorm
  | _ =>
      simp [__arith_normalize_lit] at hNorm

private theorem arith_normalize_lit_not_eq_false
    (M : SmtModel) (F a b : Term) :
    eo_interprets M F true ->
    RuleProofs.eo_has_bool_type F ->
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false := by
  intro hFTrue _hF hNorm
  cases F with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x <;> simp [__arith_normalize_lit] at hNorm
              case Apply g y =>
                cases g <;> simp at hNorm
                case Apply r x =>
                  have hXFalse :
                      eo_interprets M (Term.Apply (Term.Apply r x) y) false :=
                    RuleProofs.eo_interprets_not_true_implies_false M
                      (Term.Apply (Term.Apply r x) y) hFTrue
                  simpa [hNorm] using hXFalse
          | _ =>
              cases x <;> simp [__arith_normalize_lit] at hNorm
      | Apply g y =>
          simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
          split at hNorm <;> simp at hNorm
      | _ =>
          simp [__arith_normalize_lit] at hNorm
  | _ =>
      simp [__arith_normalize_lit] at hNorm

private theorem arith_normalize_lit_not_lt_false
    (M : SmtModel) (hM : model_wf M) (F a b : Term) :
    eo_interprets M F true ->
    RuleProofs.eo_has_bool_type F ->
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F) =
      Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) false := by
  intro hFTrue hF hNorm
  cases F with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x <;> simp [__arith_normalize_lit] at hNorm
              case Apply g y =>
                cases g <;> simp at hNorm
                case Apply r x =>
                  have hXFalse :
                      eo_interprets M (Term.Apply (Term.Apply r x) y) false :=
                    RuleProofs.eo_interprets_not_true_implies_false M
                      (Term.Apply (Term.Apply r x) y) hFTrue
                  simpa [hNorm] using hXFalse
          | _ =>
              simp [__arith_normalize_lit] at hNorm
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | lt =>
                  have hArith := rel_operands_arith_type_of_lt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.lt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_lt_eq y x hy hx] at hNorm
                  cases hNorm
              | leq =>
                  have hArith := rel_operands_arith_type_of_leq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.leq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_leq_eq y x hy hx] at hNorm
                  cases hNorm
              | gt =>
                  have hArith := rel_operands_arith_type_of_gt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.gt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_gt_eq y x hy hx] at hNorm
                  cases hNorm
              | geq =>
                  have hArith := rel_operands_arith_type_of_geq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.geq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b at hNorm
                  rw [arith_rel_neg_geq_eq y x hy hx] at hNorm
                  have hLtBool := eo_has_bool_type_lt_of_arith y x hArith
                  have hGeqTrue :
                      eo_interprets M
                        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) y) x) true := by
                    simpa using hFTrue
                  have hLtFalse := lt_false_of_geq_true M hM y x hGeqTrue hLtBool
                  rw [hNorm] at hLtFalse
                  exact hLtFalse
              | _ =>
                  simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
                  split at hNorm <;> simp at hNorm
                  all_goals simp at *
          | _ =>
              simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
              split at hNorm <;> simp at hNorm
              all_goals
                first
                | contradiction
                | rename_i hEq
                  cases hEq
      | _ =>
          simp [__arith_normalize_lit] at hNorm
  | _ =>
      simp [__arith_normalize_lit] at hNorm

private theorem arith_normalize_lit_not_gt_false
    (M : SmtModel) (hM : model_wf M) (F a b : Term) :
    eo_interprets M F true ->
    RuleProofs.eo_has_bool_type F ->
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F) =
      Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) false := by
  intro hFTrue hF hNorm
  cases F with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases x <;> simp [__arith_normalize_lit] at hNorm
              case Apply g y =>
                cases g <;> simp at hNorm
                case Apply r x =>
                  have hXFalse :
                      eo_interprets M (Term.Apply (Term.Apply r x) y) false :=
                    RuleProofs.eo_interprets_not_true_implies_false M
                      (Term.Apply (Term.Apply r x) y) hFTrue
                  simpa [hNorm] using hXFalse
          | _ =>
              simp [__arith_normalize_lit] at hNorm
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op with
              | lt =>
                  have hArith := rel_operands_arith_type_of_lt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.lt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_lt_eq y x hy hx] at hNorm
                  cases hNorm
              | leq =>
                  have hArith := rel_operands_arith_type_of_leq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.leq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_leq_eq y x hy hx] at hNorm
                  have hGtBool := eo_has_bool_type_gt_of_arith y x hArith
                  have hLeqTrue :
                      eo_interprets M
                        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) y) x) true := by
                    simpa using hFTrue
                  have hGtFalse := gt_false_of_leq_true M hM y x hLeqTrue hGtBool
                  rw [hNorm] at hGtFalse
                  exact hGtFalse
              | gt =>
                  have hArith := rel_operands_arith_type_of_gt_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.gt) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_gt_eq y x hy hx] at hNorm
                  cases hNorm
              | geq =>
                  have hArith := rel_operands_arith_type_of_geq_has_bool_type y x hF
                  have hy := left_ne_stuck_of_arith_types y x hArith
                  have hx := right_ne_stuck_of_arith_types y x hArith
                  change __arith_rel_neg (Term.UOp UserOp.geq) y x =
                    Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b at hNorm
                  rw [arith_rel_neg_geq_eq y x hy hx] at hNorm
                  cases hNorm
              | _ =>
                  simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
                  split at hNorm <;> simp at hNorm
                  all_goals simp at *
          | _ =>
              simp [__arith_normalize_lit, __arith_rel_neg] at hNorm
              split at hNorm <;> simp at hNorm
              all_goals
                first
                | contradiction
                | rename_i hEq
                  cases hEq
      | _ =>
          simp [__arith_normalize_lit] at hNorm
  | _ =>
      simp [__arith_normalize_lit] at hNorm

private theorem mk_arith_trichotomy_parts_of_ne_stuck
    {r1 r2 a b a2 b2 : Term} :
    __mk_arith_trichotomy
      (Term.Apply (Term.Apply r1 a) b)
      (Term.Apply (Term.Apply r2 a2) b2) ≠ Term.Stuck ->
    a = a2 ∧ b = b2 ∧ __arith_rel_trichotomy r1 r2 a b ≠ Term.Stuck := by
  intro hProg
  have hReq :
      __eo_requires (__eo_and (__eo_eq a a2) (__eo_eq b b2))
        (Term.Boolean true) (__arith_rel_trichotomy r1 r2 a b) ≠ Term.Stuck := by
    simpa [__mk_arith_trichotomy] using hProg
  have hGuard :
      __eo_and (__eo_eq a a2) (__eo_eq b b2) = Term.Boolean true :=
    eo_requires_arg_eq_of_ne_stuck hReq
  have hBody :
      __arith_rel_trichotomy r1 r2 a b ≠ Term.Stuck :=
    eo_requires_body_ne_stuck_of_ne_stuck hReq
  have hParts := eo_and_true hGuard
  exact ⟨eo_eq_true_eq hParts.1, eo_eq_true_eq hParts.2, hBody⟩

private theorem typed___eo_prog_arith_trichotomy_impl
    (F1 F2 : Term) :
    RuleProofs.eo_has_bool_type F1 ->
    RuleProofs.eo_has_bool_type F2 ->
    __eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type
      (__eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2)) := by
  intro hF1 hF2 hProg
  change RuleProofs.eo_has_bool_type
    (__mk_arith_trichotomy
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F1))
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F2)))
  change __mk_arith_trichotomy
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F1))
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F2)) ≠
    Term.Stuck at hProg
  generalize hN1 :
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F1) = N1 at hProg ⊢
  generalize hN2 :
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F2) = N2 at hProg ⊢
  change __mk_arith_trichotomy N1 N2 ≠ Term.Stuck at hProg
  cases N1 with
  | Apply f1 b =>
      cases f1 with
      | Apply r1 a =>
          cases N2 with
          | Apply f2 b2 =>
              cases f2 with
              | Apply r2 a2 =>
                  rcases mk_arith_trichotomy_parts_of_ne_stuck hProg with
                    ⟨ha2, hb2, hBodyNe⟩
                  subst a2
                  subst b2
                  rcases arith_rel_trichotomy_ne_stuck_cases r1 r2 a b hBodyNe with
                    hEqLt | hRest
                  · rcases hEqLt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hN2Lt :=
                      arith_normalize_lit_not_lt_has_bool_type F2 a b hF2 hN2
                    have hArith :=
                      rel_operands_arith_type_of_lt_has_bool_type a b hN2Lt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hGtBool := eo_has_bool_type_gt_of_arith a b hArith
                    change RuleProofs.eo_has_bool_type
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.eq) (Term.UOp UserOp.lt) a b))
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_eq_lt_eq a b ha hb]
                    exact hGtBool
                  rcases hRest with hEqGt | hRest
                  · rcases hEqGt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hN2Gt :=
                      arith_normalize_lit_not_gt_has_bool_type F2 a b hF2 hN2
                    have hArith :=
                      rel_operands_arith_type_of_gt_has_bool_type a b hN2Gt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hLtBool := eo_has_bool_type_lt_of_arith a b hArith
                    change RuleProofs.eo_has_bool_type
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.eq) (Term.UOp UserOp.gt) a b))
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_eq_gt_eq a b ha hb]
                    exact hLtBool
                  rcases hRest with hGtEq | hRest
                  · rcases hGtEq with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hN1Gt :=
                      arith_normalize_lit_not_gt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_gt_has_bool_type a b hN1Gt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hLtBool := eo_has_bool_type_lt_of_arith a b hArith
                    change RuleProofs.eo_has_bool_type
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.gt) (Term.UOp UserOp.eq) a b))
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_gt_eq_eq a b ha hb]
                    exact hLtBool
                  rcases hRest with hLtEq | hRest
                  · rcases hLtEq with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hN1Lt :=
                      arith_normalize_lit_not_lt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_lt_has_bool_type a b hN1Lt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hGtBool := eo_has_bool_type_gt_of_arith a b hArith
                    change RuleProofs.eo_has_bool_type
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.lt) (Term.UOp UserOp.eq) a b))
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_lt_eq_eq a b ha hb]
                    exact hGtBool
                  rcases hRest with hGtLt | hLtGt
                  · rcases hGtLt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hN1Gt :=
                      arith_normalize_lit_not_gt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_gt_has_bool_type a b hN1Gt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hEqBool := eo_has_bool_type_eq_of_arith a b hArith
                    change RuleProofs.eo_has_bool_type
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.gt) (Term.UOp UserOp.lt) a b))
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_gt_lt_eq a b ha hb]
                    exact hEqBool
                  · rcases hLtGt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hN1Lt :=
                      arith_normalize_lit_not_lt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_lt_has_bool_type a b hN1Lt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hEqBool := eo_has_bool_type_eq_of_arith a b hArith
                    change RuleProofs.eo_has_bool_type
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.lt) (Term.UOp UserOp.gt) a b))
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_lt_gt_eq a b ha hb]
                    exact hEqBool
              | _ =>
                  simp [__mk_arith_trichotomy] at hProg
          | _ =>
              simp [__mk_arith_trichotomy] at hProg
      | _ =>
          simp [__mk_arith_trichotomy] at hProg
  | _ =>
      simp [__mk_arith_trichotomy] at hProg

private theorem facts___eo_prog_arith_trichotomy_impl
    (M : SmtModel) (hM : model_wf M) (F1 F2 : Term) :
    eo_interprets M F1 true ->
    eo_interprets M F2 true ->
    RuleProofs.eo_has_bool_type F1 ->
    RuleProofs.eo_has_bool_type F2 ->
    __eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2) ≠ Term.Stuck ->
    eo_interprets M
      (__eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2)) true := by
  intro hF1True hF2True hF1 hF2 hProg
  change eo_interprets M
    (__mk_arith_trichotomy
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F1))
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F2))) true
  change __mk_arith_trichotomy
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F1))
      (__arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F2)) ≠
    Term.Stuck at hProg
  generalize hN1 :
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F1) = N1 at hProg ⊢
  generalize hN2 :
    __arith_normalize_lit (Term.Apply (Term.UOp UserOp.not) F2) = N2 at hProg ⊢
  cases N1 with
  | Apply f1 b =>
      cases f1 with
      | Apply r1 a =>
          cases N2 with
          | Apply f2 b2 =>
              cases f2 with
              | Apply r2 a2 =>
                  rcases mk_arith_trichotomy_parts_of_ne_stuck hProg with
                    ⟨ha2, hb2, hBodyNe⟩
                  subst a2
                  subst b2
                  rcases arith_rel_trichotomy_ne_stuck_cases r1 r2 a b hBodyNe with
                    hEqLt | hRest
                  · rcases hEqLt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hEqFalse :=
                      arith_normalize_lit_not_eq_false M F1 a b hF1True hF1 hN1
                    have hLtFalse :=
                      arith_normalize_lit_not_lt_false M hM F2 a b hF2True hF2 hN2
                    have hN2Lt :=
                      arith_normalize_lit_not_lt_has_bool_type F2 a b hF2 hN2
                    have hArith :=
                      rel_operands_arith_type_of_lt_has_bool_type a b hN2Lt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hGtBool := eo_has_bool_type_gt_of_arith a b hArith
                    have hBodyTrue :=
                      gt_true_of_eq_false_lt_false M hM a b hEqFalse hLtFalse hGtBool
                    change eo_interprets M
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.eq) (Term.UOp UserOp.lt) a b)) true
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_eq_lt_eq a b ha hb]
                    exact hBodyTrue
                  rcases hRest with hEqGt | hRest
                  · rcases hEqGt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hEqFalse :=
                      arith_normalize_lit_not_eq_false M F1 a b hF1True hF1 hN1
                    have hGtFalse :=
                      arith_normalize_lit_not_gt_false M hM F2 a b hF2True hF2 hN2
                    have hN2Gt :=
                      arith_normalize_lit_not_gt_has_bool_type F2 a b hF2 hN2
                    have hArith :=
                      rel_operands_arith_type_of_gt_has_bool_type a b hN2Gt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hLtBool := eo_has_bool_type_lt_of_arith a b hArith
                    have hBodyTrue :=
                      lt_true_of_eq_false_gt_false M hM a b hEqFalse hGtFalse hLtBool
                    change eo_interprets M
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.eq) (Term.UOp UserOp.gt) a b)) true
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_eq_gt_eq a b ha hb]
                    exact hBodyTrue
                  rcases hRest with hGtEq | hRest
                  · rcases hGtEq with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hGtFalse :=
                      arith_normalize_lit_not_gt_false M hM F1 a b hF1True hF1 hN1
                    have hEqFalse :=
                      arith_normalize_lit_not_eq_false M F2 a b hF2True hF2 hN2
                    have hN1Gt :=
                      arith_normalize_lit_not_gt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_gt_has_bool_type a b hN1Gt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hLtBool := eo_has_bool_type_lt_of_arith a b hArith
                    have hBodyTrue :=
                      lt_true_of_eq_false_gt_false M hM a b hEqFalse hGtFalse hLtBool
                    change eo_interprets M
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.gt) (Term.UOp UserOp.eq) a b)) true
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_gt_eq_eq a b ha hb]
                    exact hBodyTrue
                  rcases hRest with hLtEq | hRest
                  · rcases hLtEq with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hLtFalse :=
                      arith_normalize_lit_not_lt_false M hM F1 a b hF1True hF1 hN1
                    have hEqFalse :=
                      arith_normalize_lit_not_eq_false M F2 a b hF2True hF2 hN2
                    have hN1Lt :=
                      arith_normalize_lit_not_lt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_lt_has_bool_type a b hN1Lt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hGtBool := eo_has_bool_type_gt_of_arith a b hArith
                    have hBodyTrue :=
                      gt_true_of_eq_false_lt_false M hM a b hEqFalse hLtFalse hGtBool
                    change eo_interprets M
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.lt) (Term.UOp UserOp.eq) a b)) true
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_lt_eq_eq a b ha hb]
                    exact hBodyTrue
                  rcases hRest with hGtLt | hLtGt
                  · rcases hGtLt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hGtFalse :=
                      arith_normalize_lit_not_gt_false M hM F1 a b hF1True hF1 hN1
                    have hLtFalse :=
                      arith_normalize_lit_not_lt_false M hM F2 a b hF2True hF2 hN2
                    have hN1Gt :=
                      arith_normalize_lit_not_gt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_gt_has_bool_type a b hN1Gt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hEqBool := eo_has_bool_type_eq_of_arith a b hArith
                    have hBodyTrue :=
                      eq_true_of_lt_false_gt_false M hM a b hLtFalse hGtFalse hEqBool
                    change eo_interprets M
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.gt) (Term.UOp UserOp.lt) a b)) true
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_gt_lt_eq a b ha hb]
                    exact hBodyTrue
                  · rcases hLtGt with ⟨hr1, hr2⟩
                    subst r1
                    subst r2
                    have hLtFalse :=
                      arith_normalize_lit_not_lt_false M hM F1 a b hF1True hF1 hN1
                    have hGtFalse :=
                      arith_normalize_lit_not_gt_false M hM F2 a b hF2True hF2 hN2
                    have hN1Lt :=
                      arith_normalize_lit_not_lt_has_bool_type F1 a b hF1 hN1
                    have hArith :=
                      rel_operands_arith_type_of_lt_has_bool_type a b hN1Lt
                    have ha := left_ne_stuck_of_arith_types a b hArith
                    have hb := right_ne_stuck_of_arith_types a b hArith
                    have hEqBool := eo_has_bool_type_eq_of_arith a b hArith
                    have hBodyTrue :=
                      eq_true_of_lt_false_gt_false M hM a b hLtFalse hGtFalse hEqBool
                    change eo_interprets M
                      (__eo_requires (__eo_and (__eo_eq a a) (__eo_eq b b))
                        (Term.Boolean true)
                        (__arith_rel_trichotomy
                          (Term.UOp UserOp.lt) (Term.UOp UserOp.gt) a b)) true
                    rw [eo_and_eq_refl_true a b ha hb, eo_requires_true_eq,
                      arith_rel_trichotomy_lt_gt_eq a b ha hb]
                    exact hBodyTrue
              | _ =>
                  simp [__mk_arith_trichotomy] at hProg
          | _ =>
              simp [__mk_arith_trichotomy] at hProg
      | _ =>
          simp [__mk_arith_trichotomy] at hProg
  | _ =>
      simp [__mk_arith_trichotomy] at hProg

public theorem cmd_step_arith_trichotomy_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_trichotomy args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_trichotomy args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_trichotomy args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_trichotomy args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n2 premises =>
              cases premises with
              | nil =>
                  let F1 := __eo_state_proven_nth s n1
                  let F2 := __eo_state_proven_nth s n2
                  have hProgTri :
                      __eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2) ≠
                        Term.Stuck := by
                    change __eo_prog_arith_trichotomy
                      (Proof.pf (__eo_state_proven_nth s n1))
                      (Proof.pf (__eo_state_proven_nth s n2)) ≠
                        Term.Stuck at hProg
                    simpa [F1, F2] using hProg
                  have hF1Bool : RuleProofs.eo_has_bool_type F1 :=
                    hPremisesBool F1 (by simp [F1, premiseTermList])
                  have hF2Bool : RuleProofs.eo_has_bool_type F2 :=
                    hPremisesBool F2 (by simp [F2, premiseTermList])
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hF1True : eo_interprets M F1 true :=
                      hTrue F1 (by simp [F1, premiseTermList])
                    have hF2True : eo_interprets M F2 true :=
                      hTrue F2 (by simp [F2, premiseTermList])
                    change eo_interprets M
                      (__eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2)) true
                    exact facts___eo_prog_arith_trichotomy_impl
                      M hM F1 F2 hF1True hF2True hF1Bool hF2Bool hProgTri
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_arith_trichotomy (Proof.pf F1) (Proof.pf F2))
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_arith_trichotomy_impl
                        F1 F2 hF1Bool hF2Bool hProgTri)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
