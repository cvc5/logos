module

public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport
public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport
public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithSimpleSupport

private abbrev intOneTerm : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1)) (Term.Numeral 0)

private abbrev intSuccTerm (t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.plus) t) intOneTerm

private abbrev eqElimRhs (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    (Term.Apply (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
      (Term.Boolean true))

private abbrev subTerm (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg) t) s

private abbrev toIntToRealTerm (t : Term) : Term :=
  Term.Apply (Term.UOp UserOp.to_int) (Term.Apply (Term.UOp UserOp.to_real) t)

private abbrev relTerm (op : UserOp) (t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp op) t) s

private abbrev iteTerm (c t s : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) s

private abbrev minLtTerm (t s : Term) : Term :=
  iteTerm (relTerm UserOp.lt t s) t s

private abbrev maxGeqTerm (t s : Term) : Term :=
  iteTerm (relTerm UserOp.geq t s) t s

private theorem eo_to_smt_plus_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y) =
      SmtTerm.plus (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem eo_to_smt_qdiv_total_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) =
      SmtTerm.qdiv_total (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private theorem numeral_smt_type (n : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral n) = SmtType.Int
  rw [__smtx_typeof.eq_2]

private theorem rational_smt_type (q : native_Rat) :
    __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Real := by
  change __smtx_typeof (SmtTerm.Rational q) = SmtType.Real
  rw [__smtx_typeof.eq_3]

private theorem numeral_has_smt_translation (n : native_Int) :
    RuleProofs.eo_has_smt_translation (Term.Numeral n) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [numeral_smt_type]
  simp

private theorem rational_has_smt_translation (q : native_Rat) :
    RuleProofs.eo_has_smt_translation (Term.Rational q) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [rational_smt_type]
  simp

private theorem numeral_smt_eval (M : SmtModel) (n : native_Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) =
      SmtValue.Numeral n := by
  change __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n
  rw [__smtx_model_eval.eq_2]

private theorem rational_smt_eval (M : SmtModel) (q : native_Rat) :
    __smtx_model_eval M (__eo_to_smt (Term.Rational q)) =
      SmtValue.Rational q := by
  change __smtx_model_eval M (SmtTerm.Rational q) = SmtValue.Rational q
  rw [__smtx_model_eval.eq_3]

private theorem native_qdiv_total_zero (q : native_Rat) :
    native_qdiv_total q (native_mk_rational 0 1) =
      native_mk_rational 0 1 := by
  unfold native_qdiv_total
  rw [native_mk_rational_zero]
  change q / (0 : Rat) = (0 : Rat)
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

private theorem native_mk_rational_zero_den (n : native_Int) :
    native_mk_rational n 0 = native_mk_rational 0 1 := by
  unfold native_mk_rational
  change ((n : Rat) / (0 : Rat)) = ((0 : Rat) / (1 : Rat))
  rw [rat_zero_div_one]
  rw [Rat.div_def, Rat.inv_zero, Rat.mul_zero]

private theorem true_has_bool_type :
    RuleProofs.eo_has_bool_type (Term.Boolean true) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
  rw [__smtx_typeof.eq_1]

private theorem eo_typeof_eq_bool_same {A B : Term}
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B ∧ A ≠ Term.Stuck := by
  exact RuleProofs.eo_typeof_eq_bool_same A B h

private theorem eo_typeof_lt_eq_bool_of_ne_stuck {A B : Term}
    (h : __eo_typeof_lt A B ≠ Term.Stuck) :
    __eo_typeof_lt A B = Term.Bool := by
  exact RuleProofs.eo_typeof_lt_eq_bool_of_ne_stuck A B h

private theorem eo_typeof_lt_bool_cases {A B : Term}
    (h : __eo_typeof_lt A B = Term.Bool) :
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  exact RuleProofs.eo_typeof_lt_bool_cases A B h

private theorem eo_typeof_or_eq_bool_of_ne_stuck {A B : Term}
    (h : __eo_typeof_or A B ≠ Term.Stuck) :
    __eo_typeof_or A B = Term.Bool := by
  cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢

private theorem smt_arith_arg_types_of_eo_rel_bool
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Real) := by
  rcases eo_typeof_lt_bool_cases hTy with hInt | hReal
  · left
    constructor
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t (Term.UOp UserOp.Int) (__eo_to_smt t) rfl hTTrans hInt.1
      simpa [__eo_to_smt_type] using this
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s (Term.UOp UserOp.Int) (__eo_to_smt s) rfl hSTrans hInt.2
      simpa [__eo_to_smt_type] using this
  · right
    constructor
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t (Term.UOp UserOp.Real) (__eo_to_smt t) rfl hTTrans hReal.1
      simpa [__eo_to_smt_type] using this
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s (Term.UOp UserOp.Real) (__eo_to_smt s) rfl hSTrans hReal.2
      simpa [__eo_to_smt_type] using this

private theorem leq_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem lt_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem gt_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem geq_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_geq_eq, typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_geq_eq, typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem ite_smt_type_eq_then_of_same_type
    (C T E : Term)
    (hC : RuleProofs.eo_has_bool_type C)
    (hSame : __smtx_typeof (__eo_to_smt T) = __smtx_typeof (__eo_to_smt E)) :
    __smtx_typeof (__eo_to_smt (iteTerm C T E)) =
      __smtx_typeof (__eo_to_smt T) := by
  unfold RuleProofs.eo_has_bool_type at hC
  change __smtx_typeof (SmtTerm.ite (__eo_to_smt C) (__eo_to_smt T) (__eo_to_smt E)) =
    __smtx_typeof (__eo_to_smt T)
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hC, hSame, native_Teq, native_ite]

private theorem ite_has_smt_translation_same_type
    (C T E : Term)
    (hC : RuleProofs.eo_has_bool_type C)
    (hTTrans : RuleProofs.eo_has_smt_translation T)
    (hSame : __smtx_typeof (__eo_to_smt T) = __smtx_typeof (__eo_to_smt E)) :
    RuleProofs.eo_has_smt_translation (iteTerm C T E) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [ite_smt_type_eq_then_of_same_type C T E hC hSame]
  exact hTTrans

private theorem eo_typeof_not_eq_bool_of_ne_stuck {A : Term}
    (h : __eo_typeof_not A ≠ Term.Stuck) :
    __eo_typeof_not A = Term.Bool := by
  cases A <;> simp [__eo_typeof_not] at h ⊢

private theorem int_decide_lt_eq_not_decide_ge (a b : native_Int) :
    decide (a < b) = native_not (decide (b ≤ a)) := by
  by_cases h : b ≤ a
  · have hNot : ¬ a < b := Int.not_lt_of_ge h
    simp [native_not, h, hNot]
  · have hLt : a < b := Int.lt_of_not_ge h
    simp [native_not, h, hLt]

private theorem rat_decide_lt_eq_not_decide_ge (a b : native_Rat) :
    decide (a < b) = native_not (decide (b ≤ a)) := by
  by_cases h : b ≤ a
  · have hNot : ¬ a < b := Rat.not_lt.mpr h
    simp [native_not, h, hNot]
  · have hLt : a < b := Rat.not_le.mp h
    simp [native_not, h, hLt]

private theorem int_decide_lt_eq_decide_succ_le (a b : native_Int) :
    decide (a < b) = decide (native_zplus a (native_zplus 1 0) ≤ b) := by
  by_cases h : a < b
  · have hSucc : native_zplus a (native_zplus 1 0) ≤ b := by
      simpa [native_zplus] using (Int.lt_iff_add_one_le.mp h)
    simp [h, hSucc]
  · have hSucc : ¬ native_zplus a (native_zplus 1 0) ≤ b := by
      intro hSucc
      exact h (Int.lt_iff_add_one_le.mpr (by
        simpa [native_zplus] using hSucc))
    simp [h, hSucc]

private theorem int_decide_le_eq_not_decide_succ_ge (a b : native_Int) :
    decide (a ≤ b) =
      native_not (decide (native_zplus b (native_zplus 1 0) ≤ a)) := by
  by_cases h : a ≤ b
  · have hSucc : ¬ native_zplus b (native_zplus 1 0) ≤ a := by
      intro hSucc
      have hLt : b < a := Int.lt_iff_add_one_le.mpr (by
        simpa [native_zplus] using hSucc)
      exact (Int.not_lt_of_ge h) hLt
    simp [native_not, h, hSucc]
  · have hSucc : native_zplus b (native_zplus 1 0) ≤ a := by
      have hLt : b < a := Int.lt_of_not_ge h
      simpa [native_zplus] using (Int.lt_iff_add_one_le.mp hLt)
    simp [native_not, h, hSucc]

private theorem int_not_decide_ge_eq_decide_succ_le (a b : native_Int) :
    native_not (decide (b ≤ a)) =
      decide (native_zplus a (native_zplus 1 0) ≤ b) := by
  rw [← int_decide_lt_eq_not_decide_ge a b]
  exact int_decide_lt_eq_decide_succ_le a b

private theorem int_decide_eq_eq_and_ge_le (a b : native_Int) :
    decide (a = b) =
      native_and (decide (b ≤ a)) (native_and (decide (a ≤ b)) true) := by
  by_cases hEq : a = b
  · subst b
    simp [native_and]
  · by_cases hBA : b ≤ a
    · have hAB : ¬ a ≤ b := by
        intro hAB
        exact hEq (Int.le_antisymm hAB hBA)
      simp [hEq, hBA, hAB, native_and]
    · simp [hEq, hBA, native_and]

private theorem rat_decide_eq_eq_and_ge_le (a b : native_Rat) :
    decide (a = b) =
      native_and (decide (b ≤ a)) (native_and (decide (a ≤ b)) true) := by
  by_cases hEq : a = b
  · subst b
    simp [native_and]
  · by_cases hBA : b ≤ a
    · have hAB : ¬ a ≤ b := by
        intro hAB
        exact hEq (Rat.le_antisymm hAB hBA)
      simp [hEq, hBA, hAB, native_and]
    · simp [hEq, hBA, native_and]

private theorem native_zleq_refl_true (a : native_Int) :
    native_zleq a a = true := by
  simp [native_zleq]

private theorem native_qleq_refl_true (a : native_Rat) :
    native_qleq a a = true := by
  simp [native_qleq]

private theorem native_zlt_true_leq (a b : native_Int) :
    native_zlt a b = true -> native_zleq a b = true := by
  unfold native_zlt native_zleq
  intro h
  by_cases hlt : a < b
  · have hle : a ≤ b := Int.le_of_lt hlt
    simp [hlt, hle]
  · simp [hlt] at h

private theorem native_qlt_true_leq (a b : native_Rat) :
    native_qlt a b = true -> native_qleq a b = true := by
  unfold native_qlt native_qleq
  intro h
  by_cases hlt : a < b
  · have hle : a ≤ b := Rat.le_of_lt hlt
    simp [hlt, hle]
  · simp [hlt] at h

private theorem native_zlt_false_leq_swap (a b : native_Int) :
    native_zlt a b = false -> native_zleq b a = true := by
  unfold native_zlt native_zleq
  intro h
  by_cases hlt : a < b
  · simp [hlt] at h
  · have hle : b ≤ a := Int.le_of_not_gt hlt
    simp [hlt, hle]

private theorem native_qlt_false_leq_swap (a b : native_Rat) :
    native_qlt a b = false -> native_qleq b a = true := by
  unfold native_qlt native_qleq
  intro h
  by_cases hlt : a < b
  · simp [hlt] at h
  · have hle : b ≤ a := Rat.not_lt.mp hlt
    simp [hlt, hle]

private theorem native_zleq_false_leq_swap (a b : native_Int) :
    native_zleq a b = false -> native_zleq b a = true := by
  unfold native_zleq
  intro h
  by_cases hle : a ≤ b
  · simp [hle] at h
  · have hlt' : b < a := Int.lt_of_not_ge hle
    have hle' : b ≤ a := Int.le_of_lt hlt'
    simp [hle, hle']

private theorem native_qleq_false_leq_swap (a b : native_Rat) :
    native_qleq a b = false -> native_qleq b a = true := by
  unfold native_qleq
  intro h
  by_cases hle : a ≤ b
  · simp [hle] at h
  · have hlt' : b < a := Rat.not_le.mp hle
    have hle' : b ≤ a := Rat.le_of_lt hlt'
    simp [hle, hle']

private theorem intSucc_typeof_eq_stuck_of_real
    (t : Term)
    (hTReal : __eo_typeof t = Term.Real) :
    __eo_typeof (intSuccTerm t) = Term.Stuck := by
  change __eo_typeof_plus (__eo_typeof t)
      (__eo_typeof_plus Term.Int Term.Int) = Term.Stuck
  rw [hTReal]
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_ite, native_teq, native_not, SmtEval.native_not]

private theorem intSucc_has_smt_translation
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTInt : __eo_typeof t = Term.Int) :
    RuleProofs.eo_has_smt_translation (intSuccTerm t) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hOneTy := numeral_smt_type 1
  have hZeroTy := numeral_smt_type 0
  unfold RuleProofs.eo_has_smt_translation
  rw [eo_to_smt_plus_eq, eo_to_smt_plus_eq, typeof_plus_eq, typeof_plus_eq]
  simp [__smtx_typeof_arith_overload_op_2, hSmtT, hOneTy, hZeroTy]

private theorem eval_intSucc_eq
    (M : SmtModel) (t : Term) (n : native_Int)
    (hEvalT : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral n) :
    __smtx_model_eval M (__eo_to_smt (intSuccTerm t)) =
      SmtValue.Numeral (native_zplus n (native_zplus 1 0)) := by
  have hEvalOne := numeral_smt_eval M 1
  have hEvalZero := numeral_smt_eval M 0
  rw [eo_to_smt_plus_eq, eo_to_smt_plus_eq]
  rw [__smtx_model_eval.eq_14, __smtx_model_eval.eq_14]
  rw [hEvalT, hEvalOne, hEvalZero]
  simp [__smtx_model_eval_plus]

private theorem int_lt_arg_eo_types
    (t s : Term)
    (hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool)
    (hRightNotStuck :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t)) ≠ Term.Stuck) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLeftTy
  rcases eo_typeof_lt_bool_cases hLeftTy with hInt | hReal
  · exact hInt
  · have hSuccStuck := intSucc_typeof_eq_stuck_of_real t hReal.1
    have hRightStuck :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
          (intSuccTerm t)) = Term.Stuck := by
      change __eo_typeof_lt (__eo_typeof s) (__eo_typeof (intSuccTerm t)) =
        Term.Stuck
      simp [hReal.2, hSuccStuck, __eo_typeof_lt]
    exact False.elim (hRightNotStuck hRightStuck)

private theorem int_gt_arg_eo_types
    (t s : Term)
    (hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool)
    (hRightNotStuck :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s)) ≠ Term.Stuck) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLeftTy
  rcases eo_typeof_lt_bool_cases hLeftTy with hInt | hReal
  · exact hInt
  · have hSuccStuck := intSucc_typeof_eq_stuck_of_real s hReal.2
    have hRightStuck :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s)) = Term.Stuck := by
      change __eo_typeof_lt (__eo_typeof t) (__eo_typeof (intSuccTerm s)) =
        Term.Stuck
      simp [hReal.1, hSuccStuck, __eo_typeof_lt]
    exact False.elim (hRightNotStuck hRightStuck)

private theorem leq_norm_arg_eo_types
    (t s : Term)
    (hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) =
        Term.Bool)
    (hRightNotTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s))) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLeftTy
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s)) = Term.Bool :=
    CnfSupport.typeof_not_eq_bool hRightNotTy
  rcases eo_typeof_lt_bool_cases hLeftTy with hInt | hReal
  · exact hInt
  · have hSuccStuck := intSucc_typeof_eq_stuck_of_real s hReal.2
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof (intSuccTerm s)) =
      Term.Bool at hGeqTy
    simp [hReal.1, hSuccStuck, __eo_typeof_lt] at hGeqTy

private theorem geq_tighten_arg_eo_types
    (t s : Term)
    (hLeftNotTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        Term.Bool)
    (hRightNotStuck :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t)) ≠ Term.Stuck) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool :=
    CnfSupport.typeof_not_eq_bool hLeftNotTy
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLeftTy
  rcases eo_typeof_lt_bool_cases hLeftTy with hInt | hReal
  · exact hInt
  · have hSuccStuck := intSucc_typeof_eq_stuck_of_real t hReal.1
    have hRightStuck :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
          (intSuccTerm t)) = Term.Stuck := by
      change __eo_typeof_lt (__eo_typeof s) (__eo_typeof (intSuccTerm t)) =
        Term.Stuck
      simp [hReal.2, hSuccStuck, __eo_typeof_lt]
    exact False.elim (hRightNotStuck hRightStuck)

private theorem eval_lt_not_geq_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hLtTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) = Term.Bool) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLtTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hLtTy with hInt | hReal
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hInt.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hInt.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
      simpa [hInt.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hInt.2])
    rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
    rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_lt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s)) by rfl]
    rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_7, __smtx_model_eval.eq_20]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_lt, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_not, native_zlt, native_zleq,
      int_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (ns ≤ nt))))
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hReal.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hReal.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Real := by
      simpa [hReal.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hReal.2])
    rcases real_value_canonical hEvalTValTy with ⟨qt, hEvalT⟩
    rcases real_value_canonical hEvalSValTy with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_lt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s)) by rfl]
    rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_7, __smtx_model_eval.eq_20]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_lt, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_not, native_qlt, native_qleq,
      rat_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (qs ≤ qt))))

private theorem eval_gt_not_geq_swap_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hGtTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) = Term.Bool) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)))) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hGtTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hGtTy with hInt | hReal
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hInt.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hInt.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
      simpa [hInt.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hInt.2])
    rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
    rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_gt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt s) (__eo_to_smt t)) by rfl]
    rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_7, __smtx_model_eval.eq_20]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_geq,
      __smtx_model_eval_leq, __smtx_model_eval_not, native_zlt, native_zleq,
      int_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (nt ≤ ns))))
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hReal.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hReal.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Real := by
      simpa [hReal.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hReal.2])
    rcases real_value_canonical hEvalTValTy with ⟨qt, hEvalT⟩
    rcases real_value_canonical hEvalSValTy with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_gt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt s) (__eo_to_smt t)) by rfl]
    rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_7, __smtx_model_eval.eq_20]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_geq,
      __smtx_model_eval_leq, __smtx_model_eval_not, native_qlt, native_qleq,
      rat_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (qt ≤ qs))))

private theorem eval_int_lt_geq_succ_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
          (intSuccTerm t)))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSInt
  have hEvalTValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
    simpa [hSmtT] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, hSmtT])
  have hEvalSValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
    simpa [hSmtS] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by simp [term_has_non_none_type, hSmtS])
  rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
  rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
  have hEvalSucc := eval_intSucc_eq M t nt hEvalT
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_lt_eq, eo_to_smt_geq_eq]
  rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_20]
  rw [hEvalT, hEvalS, hEvalSucc]
  simp [__smtx_model_eval_lt, __smtx_model_eval_geq, __smtx_model_eval_leq,
    native_zlt, native_zleq, int_decide_lt_eq_decide_succ_le]
  exact RuleProofs.smtx_model_eval_eq_refl
    (SmtValue.Boolean (decide (nt + 1 ≤ ns)))

private theorem eval_int_gt_geq_succ_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s)))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSInt
  have hEvalTValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
    simpa [hSmtT] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, hSmtT])
  have hEvalSValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
    simpa [hSmtS] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by simp [term_has_non_none_type, hSmtS])
  rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
  rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
  have hEvalSucc := eval_intSucc_eq M s ns hEvalS
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_gt_eq, eo_to_smt_geq_eq]
  rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_20]
  rw [hEvalT, hEvalS, hEvalSucc]
  simp [__smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_geq,
    __smtx_model_eval_leq, native_zlt, native_zleq,
    int_decide_lt_eq_decide_succ_le]
  exact RuleProofs.smtx_model_eval_eq_refl
    (SmtValue.Boolean (decide (ns + 1 ≤ nt)))

private theorem eval_int_leq_not_geq_succ_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
            (intSuccTerm s))))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSInt
  have hEvalTValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
    simpa [hSmtT] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, hSmtT])
  have hEvalSValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
    simpa [hSmtS] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by simp [term_has_non_none_type, hSmtS])
  rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
  rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
  have hEvalSucc := eval_intSucc_eq M s ns hEvalS
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_leq_eq]
  rw [show __eo_to_smt
      (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s))) =
      SmtTerm.not (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt (intSuccTerm s))) by
    rfl]
  rw [__smtx_model_eval.eq_18, __smtx_model_eval.eq_7, __smtx_model_eval.eq_20]
  rw [hEvalT, hEvalS, hEvalSucc]
  simp only [__smtx_model_eval_leq, __smtx_model_eval_geq, __smtx_model_eval_not,
    native_zleq]
  rw [← int_decide_le_eq_not_decide_succ_ge nt ns]
  exact RuleProofs.smtx_model_eval_eq_refl
    (SmtValue.Boolean (decide (nt ≤ ns)))

private theorem eval_int_not_geq_geq_succ_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
          (intSuccTerm t)))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSInt
  have hEvalTValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
    simpa [hSmtT] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by simp [term_has_non_none_type, hSmtT])
  have hEvalSValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
    simpa [hSmtS] using
      Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by simp [term_has_non_none_type, hSmtS])
  rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
  rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
  have hEvalSucc := eval_intSucc_eq M t nt hEvalT
  unfold RuleProofs.smt_value_rel
  rw [show __eo_to_smt
      (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
      SmtTerm.not (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s)) by
    rfl]
  rw [eo_to_smt_geq_eq]
  rw [__smtx_model_eval.eq_7, __smtx_model_eval.eq_20, __smtx_model_eval.eq_20]
  rw [hEvalT, hEvalS, hEvalSucc]
  simp only [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_not,
    native_zleq]
  rw [int_not_decide_ge_eq_decide_succ_le nt ns]
  exact RuleProofs.smtx_model_eval_eq_refl
    (SmtValue.Boolean (decide (native_zplus nt (native_zplus 1 0) ≤ ns)))

private theorem eval_eq_geq_leq_and_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s)))
      (__smtx_model_eval M (__eo_to_smt (eqElimRhs t s))) := by
  rcases hArgTypes with hInt | hReal
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
    have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hSmtT] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hSmtT])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
      simpa [hSmtS] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hSmtS])
    rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
    rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_eq_eq]
    rw [show __eo_to_smt (eqElimRhs t s) =
        SmtTerm.and (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s))
          (SmtTerm.and (SmtTerm.leq (__eo_to_smt t) (__eo_to_smt s))
            (SmtTerm.Boolean true)) by
      rfl]
    rw [smtx_eval_eq_term_eq, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_18, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_eq, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_and, native_veq, native_zeq, native_zleq, native_and,
      int_decide_eq_eq_and_ge_le]
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
    have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hSmtT] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hSmtT])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Real := by
      simpa [hSmtS] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hSmtS])
    rcases real_value_canonical hEvalTValTy with ⟨qt, hEvalT⟩
    rcases real_value_canonical hEvalSValTy with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_eq_eq]
    rw [show __eo_to_smt (eqElimRhs t s) =
        SmtTerm.and (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s))
          (SmtTerm.and (SmtTerm.leq (__eo_to_smt t) (__eo_to_smt s))
            (SmtTerm.Boolean true)) by
      rfl]
    rw [smtx_eval_eq_term_eq, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_18, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_eq, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_and, native_veq, native_qeq, native_qleq, native_and,
      rat_decide_eq_eq_and_ge_le]

private theorem prog_arith_elim_leq_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_leq t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_leq, htSt, hsSt]

private theorem prog_arith_elim_lt_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_lt t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_lt, htSt, hsSt]

private theorem prog_arith_elim_gt_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_gt t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_gt, htSt, hsSt]

private theorem prog_arith_elim_int_lt_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_int_lt t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_int_lt, htSt, hsSt, intSuccTerm, intOneTerm]

private theorem prog_arith_elim_int_gt_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_int_gt t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_int_gt, htSt, hsSt, intSuccTerm, intOneTerm]

private theorem prog_arith_leq_norm_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_leq_norm t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
            (intSuccTerm s))) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_leq_norm, htSt, hsSt, intSuccTerm, intOneTerm]

private theorem prog_arith_geq_tighten_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_geq_tighten t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_geq_tighten, htSt, hsSt, intSuccTerm, intOneTerm]

private theorem prog_arith_eq_elim_int_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_eq_elim_int t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
        (eqElimRhs t s) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_eq_elim_int, htSt, hsSt, eqElimRhs]

private theorem prog_arith_eq_elim_real_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_eq_elim_real t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
        (eqElimRhs t s) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_eq_elim_real, htSt, hsSt, eqElimRhs]

private theorem arith_eq_elim_body_arg_type_cases
    (t s : Term)
    (hResultTy :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
          (eqElimRhs t s)) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
      (__eo_typeof (eqElimRhs t s)) = Term.Bool at hResultTy
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hRhsTy : __eo_typeof (eqElimRhs t s) = Term.Bool := by
    change __eo_typeof_or
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Boolean true))) = Term.Bool
    exact eo_typeof_or_eq_bool_of_ne_stuck hRightNotStuck
  change __eo_typeof_or
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Boolean true))) = Term.Bool at hRhsTy
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool :=
    CnfSupport.typeof_or_eq_bool_left hRhsTy
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hGeqTy
  exact eo_typeof_lt_bool_cases hGeqTy

private theorem arith_eq_elim_int_arg_type_cases_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_eq_elim_int t s) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_eq_elim_int_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
          (eqElimRhs t s)) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  exact arith_eq_elim_body_arg_type_cases t s hResultTy'

private theorem arith_eq_elim_real_arg_type_cases_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_eq_elim_real t s) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_eq_elim_real_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
          (eqElimRhs t s)) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  exact arith_eq_elim_body_arg_type_cases t s hResultTy'

private theorem arith_elim_int_lt_eo_arg_types_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_int_lt t s) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_int_lt_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t))) = Term.Bool at hResultTy'
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  exact int_lt_arg_eo_types t s hLeftTy hRightNotStuck

private theorem arith_elim_int_gt_eo_arg_types_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_int_gt t s) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_int_gt_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s))) = Term.Bool at hResultTy'
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  exact int_gt_arg_eo_types t s hLeftTy hRightNotStuck

private theorem arith_leq_norm_eo_arg_types_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_leq_norm t s) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_leq_norm_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
              (intSuccTerm s)))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
      (__eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s)))) = Term.Bool at hResultTy'
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightNotTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s))) = Term.Bool := by
    change __eo_typeof_not
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s))) = Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hRightNotStuck
  exact leq_norm_arg_eo_types t s hLeftTy hRightNotTy

private theorem arith_geq_tighten_eo_arg_types_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_tighten t s) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_tighten_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t))) = Term.Bool at hResultTy'
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').2
  have hLeftNotTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        Term.Bool := by
    change __eo_typeof_not
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
      Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hLeftNotStuck
  exact geq_tighten_arg_eo_types t s hLeftNotTy hRightNotStuck

theorem typed_arith_elim_leq
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_leq t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_leq t s) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_leq_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
      Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof s) (__eo_typeof t) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hRightNotStuck
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)
    (leq_has_bool_type t s hTTrans hSTrans hLeftTy)
    (geq_has_bool_type s t hSTrans hTTrans hRightTy)

theorem facts_arith_elim_leq
    (M : SmtModel) (_hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_leq t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_leq t s) true := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_leq_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_leq t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)
    hBool' <| by
      unfold RuleProofs.smt_value_rel
      rw [eo_to_smt_leq_eq, eo_to_smt_geq_eq]
      rw [__smtx_model_eval.eq_18, __smtx_model_eval.eq_20]
      simp [__smtx_model_eval_geq]
      exact RuleProofs.smtx_model_eval_eq_refl
        (__smtx_model_eval_leq (__smtx_model_eval M (__eo_to_smt t))
          (__smtx_model_eval M (__eo_to_smt s)))

theorem typed_arith_elim_lt
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_lt t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_lt t s) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_lt_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) =
      Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightNotTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        Term.Bool := by
    change __eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
      Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hRightNotStuck
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    exact CnfSupport.typeof_not_eq_bool hRightNotTy
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    (lt_has_bool_type t s hTTrans hSTrans hLeftTy)
    (RuleProofs.eo_has_bool_type_not_of_bool_arg
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
      (geq_has_bool_type t s hTTrans hSTrans hGeqTy))

theorem facts_arith_elim_lt
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_lt t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_lt t s) true := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_lt_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_lt t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) := by
    simpa [hProgEq] using hBool
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) =
      Term.Bool at hResultTy'
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    hBool'
    (eval_lt_not_geq_rel M hM t s hTTrans hSTrans hLeftTy)

theorem typed_arith_elim_gt
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_gt t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_gt t s) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_gt_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) =
      Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightNotTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
        Term.Bool := by
    change __eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
      Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hRightNotStuck
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t) =
        Term.Bool := by
    exact CnfSupport.typeof_not_eq_bool hRightNotTy
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))
    (gt_has_bool_type t s hTTrans hSTrans hLeftTy)
    (RuleProofs.eo_has_bool_type_not_of_bool_arg
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)
      (geq_has_bool_type s t hSTrans hTTrans hGeqTy))

theorem facts_arith_elim_gt
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_gt t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_gt t s) true := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_gt_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_gt t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) := by
    simpa [hProgEq] using hBool
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) =
      Term.Bool at hResultTy'
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))
    hBool'
    (eval_gt_not_geq_swap_rel M hM t s hTTrans hSTrans hLeftTy)

theorem typed_arith_elim_int_lt
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_int_lt t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_int_lt t s) := by
  have hArgTypes :=
    arith_elim_int_lt_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_int_lt_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t))) = Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t)) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof s) (__eo_typeof (intSuccTerm t)) =
      Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hRightNotStuck
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t))
    (lt_has_bool_type t s hTTrans hSTrans hLeftTy)
    (geq_has_bool_type s (intSuccTerm t) hSTrans
      (intSucc_has_smt_translation t hTTrans hArgTypes.1) hRightTy)

theorem facts_arith_elim_int_lt
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_int_lt t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_int_lt t s) true := by
  have hArgTypes :=
    arith_elim_int_lt_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_int_lt_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_int_lt t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
            (intSuccTerm t))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t))
    hBool'
    (eval_int_lt_geq_succ_rel M hM t s hTTrans hSTrans
      hArgTypes.1 hArgTypes.2)

theorem typed_arith_elim_int_gt
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_int_gt t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_int_gt t s) := by
  have hArgTypes :=
    arith_elim_int_gt_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_int_gt_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s))) = Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s)) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof (intSuccTerm s)) =
      Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hRightNotStuck
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s))
    (gt_has_bool_type t s hTTrans hSTrans hLeftTy)
    (geq_has_bool_type t (intSuccTerm s) hTTrans
      (intSucc_has_smt_translation s hSTrans hArgTypes.2) hRightTy)

theorem facts_arith_elim_int_gt
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_int_gt t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_int_gt t s) true := by
  have hArgTypes :=
    arith_elim_int_gt_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_int_gt_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_int_gt t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
            (intSuccTerm s))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s))
    hBool'
    (eval_int_gt_geq_succ_rel M hM t s hTTrans hSTrans
      hArgTypes.1 hArgTypes.2)

theorem typed_arith_leq_norm
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_leq_norm t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_leq_norm t s) := by
  have hArgTypes :=
    arith_leq_norm_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_leq_norm_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
      (__eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s)))) = Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightNotTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
          (intSuccTerm s))) = Term.Bool := by
    change __eo_typeof_not
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s))) = Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hRightNotStuck
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
        (intSuccTerm s)) = Term.Bool :=
    CnfSupport.typeof_not_eq_bool hRightNotTy
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s)))
    (leq_has_bool_type t s hTTrans hSTrans hLeftTy)
    (RuleProofs.eo_has_bool_type_not_of_bool_arg
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s))
      (geq_has_bool_type t (intSuccTerm s) hTTrans
        (intSucc_has_smt_translation s hSTrans hArgTypes.2) hGeqTy))

theorem facts_arith_leq_norm
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_leq_norm t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_leq_norm t s) true := by
  have hArgTypes :=
    arith_leq_norm_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_leq_norm_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_leq_norm t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t)
              (intSuccTerm s)))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) (intSuccTerm s)))
    hBool'
    (eval_int_leq_not_geq_succ_rel M hM t s hTTrans hSTrans
      hArgTypes.1 hArgTypes.2)

theorem typed_arith_geq_tighten
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_tighten t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_geq_tighten t s) := by
  have hArgTypes :=
    arith_geq_tighten_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_tighten_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t))) = Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftNotTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        Term.Bool := by
    change __eo_typeof_not
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
      Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hLeftNotStuck
  have hGeqLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool :=
    CnfSupport.typeof_not_eq_bool hLeftNotTy
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
        (intSuccTerm t)) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof s) (__eo_typeof (intSuccTerm t)) =
      Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hRightNotStuck
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t))
    (RuleProofs.eo_has_bool_type_not_of_bool_arg
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
      (geq_has_bool_type t s hTTrans hSTrans hGeqLeftTy))
    (geq_has_bool_type s (intSuccTerm t) hSTrans
      (intSucc_has_smt_translation t hTTrans hArgTypes.1) hRightTy)

theorem facts_arith_geq_tighten
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_tighten t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_geq_tighten t s) true := by
  have hArgTypes :=
    arith_geq_tighten_eo_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_tighten_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_geq_tighten t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s)
            (intSuccTerm t))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) (intSuccTerm t))
    hBool'
    (eval_int_not_geq_geq_succ_rel M hM t s hTTrans hSTrans
      hArgTypes.1 hArgTypes.2)

private theorem typed_arith_eq_elim_body
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
        (eqElimRhs t s)) := by
  have hSameSmt :
      __smtx_typeof (__eo_to_smt t) = __smtx_typeof (__eo_to_smt s) ∧
        __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rcases hArgTypes with hInt | hReal
    · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
        RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
          t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
      have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
        RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
          s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
      constructor
      · rw [hSmtT, hSmtS]
      · simp [hSmtT]
    · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
        RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
          t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
      have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
        RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
          s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
      constructor
      · rw [hSmtT, hSmtS]
      · simp [hSmtT]
  have hRelTy : __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool := by
    rcases hArgTypes with hInt | hReal
    · simp [hInt.1, hInt.2, __eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not, SmtEval.native_not]
    · simp [hReal.1, hReal.2, __eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not, SmtEval.native_not]
  have hEqLeftBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t s
      hSameSmt.1 hSameSmt.2
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact hRelTy
  have hLeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact hRelTy
  have hGeqBool := geq_has_bool_type t s hTTrans hSTrans hGeqTy
  have hLeqBool := leq_has_bool_type t s hTTrans hSTrans hLeqTy
  have hInnerAndBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_and_of_bool_args
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
      (Term.Boolean true) hLeqBool true_has_bool_type
  have hRhsBool : RuleProofs.eo_has_bool_type (eqElimRhs t s) := by
    exact RuleProofs.eo_has_bool_type_and_of_bool_args
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
      (Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
        (Term.Boolean true))
      hGeqBool hInnerAndBool
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s)
    (eqElimRhs t s)
    hEqLeftBool hRhsBool

private theorem facts_arith_eq_elim_body
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s))
        (eqElimRhs t s)) true := by
  have hBool := typed_arith_eq_elim_body t s hTTrans hSTrans hArgTypes
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s)
    (eqElimRhs t s)
    hBool
    (eval_eq_geq_leq_and_rel M hM t s hTTrans hSTrans hArgTypes)

theorem typed_arith_eq_elim_int
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_eq_elim_int t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_eq_elim_int t s) := by
  have hArgTypes :=
    arith_eq_elim_int_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_eq_elim_int_eq_of_nonstuck t s ht hs
  rw [hProgEq]
  exact typed_arith_eq_elim_body t s hTTrans hSTrans hArgTypes

theorem facts_arith_eq_elim_int
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_eq_elim_int t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_eq_elim_int t s) true := by
  have hArgTypes :=
    arith_eq_elim_int_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_eq_elim_int_eq_of_nonstuck t s ht hs
  rw [hProgEq]
  exact facts_arith_eq_elim_body M hM t s hTTrans hSTrans hArgTypes

theorem typed_arith_eq_elim_real
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_eq_elim_real t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_eq_elim_real t s) := by
  have hArgTypes :=
    arith_eq_elim_real_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_eq_elim_real_eq_of_nonstuck t s ht hs
  rw [hProgEq]
  exact typed_arith_eq_elim_body t s hTTrans hSTrans hArgTypes

theorem facts_arith_eq_elim_real
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_eq_elim_real t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_eq_elim_real t s) true := by
  have hArgTypes :=
    arith_eq_elim_real_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_eq_elim_real_eq_of_nonstuck t s ht hs
  rw [hProgEq]
  exact facts_arith_eq_elim_body M hM t s hTTrans hSTrans hArgTypes

private theorem sub_typeof_eq_int
    (t s : Term)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    __eo_typeof (subTerm t s) = Term.Int := by
  change __eo_typeof_plus (__eo_typeof t) (__eo_typeof s) = Term.Int
  rw [hTInt, hSInt]
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_ite, native_teq, native_not, SmtEval.native_not]

private theorem sub_typeof_eq_real
    (t s : Term)
    (hTReal : __eo_typeof t = Term.Real)
    (hSReal : __eo_typeof s = Term.Real) :
    __eo_typeof (subTerm t s) = Term.Real := by
  change __eo_typeof_plus (__eo_typeof t) (__eo_typeof s) = Term.Real
  rw [hTReal, hSReal]
  simp [__eo_typeof_plus, __eo_requires, __eo_eq, __is_arith_type,
    native_ite, native_teq, native_not, SmtEval.native_not]

private theorem sub_has_smt_translation_int
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    RuleProofs.eo_has_smt_translation (subTerm t s) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSInt
  unfold RuleProofs.eo_has_smt_translation
  rw [show __eo_to_smt (subTerm t s) =
      SmtTerm.neg (__eo_to_smt t) (__eo_to_smt s) by rfl]
  rw [typeof_neg_eq]
  simp [__smtx_typeof_arith_overload_op_2, hSmtT, hSmtS]

private theorem sub_has_smt_translation_real
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTReal : __eo_typeof t = Term.Real)
    (hSReal : __eo_typeof s = Term.Real) :
    RuleProofs.eo_has_smt_translation (subTerm t s) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Real (__eo_to_smt t) rfl hTTrans hTReal
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Real (__eo_to_smt s) rfl hSTrans hSReal
  unfold RuleProofs.eo_has_smt_translation
  rw [show __eo_to_smt (subTerm t s) =
      SmtTerm.neg (__eo_to_smt t) (__eo_to_smt s) by rfl]
  rw [typeof_neg_eq]
  simp [__smtx_typeof_arith_overload_op_2, hSmtT, hSmtS]

private theorem prog_arith_geq_norm1_int_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_geq_norm1_int t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
          (Term.Numeral 0)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_geq_norm1_int, subTerm, htSt, hsSt]

private theorem prog_arith_geq_norm1_real_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_geq_norm1_real t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
          (Term.Rational (native_mk_rational 0 1))) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_geq_norm1_real, subTerm, htSt, hsSt]

private theorem arith_geq_norm1_int_arg_types_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_norm1_int t s) = Term.Bool) :
    __eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_norm1_int_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
        (Term.Numeral 0))) = Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLeftTy
  rcases eo_typeof_lt_bool_cases hLeftTy with hInt | hReal
  · exact hInt
  · have hSubReal := sub_typeof_eq_real t s hReal.1 hReal.2
    have hRightStuck :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
          (Term.Numeral 0)) = Term.Stuck := by
      change __eo_typeof_lt (__eo_typeof (subTerm t s)) Term.Int = Term.Stuck
      simp [hSubReal, __eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not,
        SmtEval.native_not]
    exact False.elim (hRightNotStuck hRightStuck)

private theorem arith_geq_norm1_real_arg_types_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_norm1_real t s) = Term.Bool) :
    __eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_norm1_real_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
        (Term.Rational (native_mk_rational 0 1)))) = Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLeftTy
  rcases eo_typeof_lt_bool_cases hLeftTy with hInt | hReal
  · have hSubInt := sub_typeof_eq_int t s hInt.1 hInt.2
    have hRightStuck :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
          (Term.Rational (native_mk_rational 0 1))) = Term.Stuck := by
      change __eo_typeof_lt (__eo_typeof (subTerm t s)) Term.Real = Term.Stuck
      simp [hSubInt, __eo_typeof_lt, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not,
        SmtEval.native_not]
    exact False.elim (hRightNotStuck hRightStuck)
  · exact hReal

private theorem eval_geq_sub_zero_int_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTInt : __eo_typeof t = Term.Int)
    (hSInt : __eo_typeof s = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
          (Term.Numeral 0)))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Int (__eo_to_smt s) rfl hSTrans hSInt
  rcases smt_eval_int_of_type M hM t hSmtT with ⟨nt, hEvalT⟩
  rcases smt_eval_int_of_type M hM s hSmtS with ⟨ns, hEvalS⟩
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_geq_eq]
  rw [show __eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
        (Term.Numeral 0)) =
      SmtTerm.geq (SmtTerm.neg (__eo_to_smt t) (__eo_to_smt s))
        (SmtTerm.Numeral 0) by rfl]
  rw [__smtx_model_eval.eq_20, __smtx_model_eval.eq_20,
    __smtx_model_eval.eq_15, __smtx_model_eval.eq_2]
  rw [hEvalT, hEvalS]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval__]
  change __smtx_model_eval_eq
      (SmtValue.Boolean (native_zleq ns nt))
      (SmtValue.Boolean (native_zleq 0 (native_zplus nt (native_zneg ns)))) =
    SmtValue.Boolean true
  rw [native_zsub_geq_zero_eq nt ns]
  simp [__smtx_model_eval_eq, native_veq]

private theorem eval_geq_sub_zero_real_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTReal : __eo_typeof t = Term.Real)
    (hSReal : __eo_typeof s = Term.Real) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
          (Term.Rational (native_mk_rational 0 1))))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Real (__eo_to_smt t) rfl hTTrans hTReal
  have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s Term.Real (__eo_to_smt s) rfl hSTrans hSReal
  rcases smt_eval_real_of_type M hM t hSmtT with ⟨qt, hEvalT⟩
  rcases smt_eval_real_of_type M hM s hSmtS with ⟨qs, hEvalS⟩
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_geq_eq]
  rw [show __eo_to_smt
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
        (Term.Rational (native_mk_rational 0 1))) =
      SmtTerm.geq (SmtTerm.neg (__eo_to_smt t) (__eo_to_smt s))
        (SmtTerm.Rational (native_mk_rational 0 1)) by rfl]
  rw [__smtx_model_eval.eq_20, __smtx_model_eval.eq_20,
    __smtx_model_eval.eq_15, __smtx_model_eval.eq_3]
  rw [hEvalT, hEvalS]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval__]
  change __smtx_model_eval_eq
      (SmtValue.Boolean (native_qleq qs qt))
      (SmtValue.Boolean
        (native_qleq (native_mk_rational 0 1)
          (native_qplus qt (native_qneg qs)))) =
    SmtValue.Boolean true
  rw [native_qsub_geq_zero_eq qt qs]
  simp [__smtx_model_eval_eq, native_veq]

theorem typed_arith_geq_norm1_int
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_norm1_int t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_geq_norm1_int t s) := by
  have hArgTypes :=
    arith_geq_norm1_int_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_norm1_int_eq_of_nonstuck t s ht hs
  rw [hProgEq]
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    simp [hArgTypes.1, hArgTypes.2, __eo_typeof_lt, __eo_requires, __eo_eq,
      __is_arith_type, native_ite, native_teq, native_not, SmtEval.native_not]
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
        (Term.Numeral 0)) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof (subTerm t s)) Term.Int = Term.Bool
    rw [sub_typeof_eq_int t s hArgTypes.1 hArgTypes.2]
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, SmtEval.native_not]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
      (Term.Numeral 0))
    (geq_has_bool_type t s hTTrans hSTrans hLeftTy)
    (geq_has_bool_type (subTerm t s) (Term.Numeral 0)
      (sub_has_smt_translation_int t s hTTrans hSTrans hArgTypes.1 hArgTypes.2)
      (numeral_has_smt_translation 0) hRightTy)

theorem facts_arith_geq_norm1_int
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_norm1_int t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_geq_norm1_int t s) true := by
  have hArgTypes :=
    arith_geq_norm1_int_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_norm1_int_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_geq_norm1_int t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
            (Term.Numeral 0))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
      (Term.Numeral 0))
    hBool'
    (eval_geq_sub_zero_int_rel M hM t s hTTrans hSTrans
      hArgTypes.1 hArgTypes.2)

theorem typed_arith_geq_norm1_real
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_norm1_real t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_geq_norm1_real t s) := by
  have hArgTypes :=
    arith_geq_norm1_real_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_norm1_real_eq_of_nonstuck t s ht hs
  rw [hProgEq]
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    simp [hArgTypes.1, hArgTypes.2, __eo_typeof_lt, __eo_requires, __eo_eq,
      __is_arith_type, native_ite, native_teq, native_not, SmtEval.native_not]
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
        (Term.Rational (native_mk_rational 0 1))) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof (subTerm t s)) Term.Real = Term.Bool
    rw [sub_typeof_eq_real t s hArgTypes.1 hArgTypes.2]
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, SmtEval.native_not]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
      (Term.Rational (native_mk_rational 0 1)))
    (geq_has_bool_type t s hTTrans hSTrans hLeftTy)
    (geq_has_bool_type (subTerm t s) (Term.Rational (native_mk_rational 0 1))
      (sub_has_smt_translation_real t s hTTrans hSTrans hArgTypes.1 hArgTypes.2)
      (rational_has_smt_translation (native_mk_rational 0 1)) hRightTy)

theorem facts_arith_geq_norm1_real
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_geq_norm1_real t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_geq_norm1_real t s) true := by
  have hArgTypes :=
    arith_geq_norm1_real_arg_types_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_geq_norm1_real_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_geq_norm1_real t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
            (Term.Rational (native_mk_rational 0 1)))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (subTerm t s))
      (Term.Rational (native_mk_rational 0 1)))
    hBool'
    (eval_geq_sub_zero_real_rel M hM t s hTTrans hSTrans
      hArgTypes.1 hArgTypes.2)

private theorem prog_arith_to_int_elim_to_real_eq_of_nonstuck
    (t : Term)
    (ht : t ≠ Term.Stuck) :
    __eo_prog_arith_to_int_elim_to_real t =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) (toIntToRealTerm t)) t := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  simp [__eo_prog_arith_to_int_elim_to_real, toIntToRealTerm, htSt]

private theorem arith_to_int_elim_arg_type_of_result
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_to_int_elim_to_real t) = Term.Bool) :
    __eo_typeof t = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_to_int_elim_to_real_eq_of_nonstuck t ht
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq
      (__eo_typeof (toIntToRealTerm t)) (__eo_typeof t) = Term.Bool at hResultTy
  rcases eo_typeof_eq_bool_same hResultTy with ⟨hSame, hLeftNonStuck⟩
  change __eo_typeof_to_int (__eo_typeof_to_real (__eo_typeof t)) =
      __eo_typeof t at hSame
  change __eo_typeof_to_int (__eo_typeof_to_real (__eo_typeof t)) ≠
      Term.Stuck at hLeftNonStuck
  cases hTy : __eo_typeof t with
  | UOp op =>
      cases op <;>
        simp [toIntToRealTerm, __eo_typeof_to_int, __eo_typeof_to_real,
          __eo_requires, __eo_eq, __is_arith_type,
          native_ite, native_teq, native_not, SmtEval.native_not, hTy]
          at hSame hLeftNonStuck ⊢
  | _ =>
      simp [toIntToRealTerm, __eo_typeof_to_int, __eo_typeof_to_real,
        __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not, hTy]
        at hSame hLeftNonStuck

private theorem smtx_model_eval_to_int_to_real_of_numeral
    (n : native_Int) :
    __smtx_model_eval_to_int (__smtx_model_eval_to_real (SmtValue.Numeral n)) =
      SmtValue.Numeral n := by
  change SmtValue.Numeral (Rat.floor ((n : Rat) / 1)) = SmtValue.Numeral n
  congr
  have hDiv : ((n : Rat) / 1 : Rat) = (n : Rat) := by
    change ((n : Rat) * ((1 : Rat)⁻¹)) = (n : Rat)
    rw [Rat.inv_def]
    change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
    exact Rat.mul_one _
  rw [hDiv]
  exact Rat.floor_intCast n

private theorem eval_to_int_to_real_rel
    (M : SmtModel) (hM : model_wf M)
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTInt : __eo_typeof t = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (toIntToRealTerm t)))
      (__smtx_model_eval M (__eo_to_smt t)) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  rcases smt_eval_int_of_type M hM t hSmtT with ⟨n, hEvalT⟩
  unfold RuleProofs.smt_value_rel
  rw [show __eo_to_smt (toIntToRealTerm t) =
      SmtTerm.to_int (SmtTerm.to_real (__eo_to_smt t)) by rfl]
  rw [__smtx_model_eval.eq_22, __smtx_model_eval.eq_21, hEvalT]
  rw [smtx_model_eval_to_int_to_real_of_numeral n]
  exact RuleProofs.smtx_model_eval_eq_refl (SmtValue.Numeral n)

theorem typed_arith_to_int_elim_to_real
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_to_int_elim_to_real t) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_to_int_elim_to_real t) := by
  have hTInt := arith_to_int_elim_arg_type_of_result t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_to_int_elim_to_real_eq_of_nonstuck t ht
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (toIntToRealTerm t)) = SmtType.Int := by
    rw [show __eo_to_smt (toIntToRealTerm t) =
        SmtTerm.to_int (SmtTerm.to_real (__eo_to_smt t)) by rfl]
    rw [typeof_to_int_eq, typeof_to_real_eq]
    simp [hSmtT, native_ite, native_Teq]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (toIntToRealTerm t) t
    (by rw [hLeftTy, hSmtT])
    (by rw [hLeftTy]; simp)

theorem facts_arith_to_int_elim_to_real
    (M : SmtModel) (hM : model_wf M)
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_to_int_elim_to_real t) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_to_int_elim_to_real t) true := by
  have hTInt := arith_to_int_elim_arg_type_of_result t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_to_int_elim_to_real_eq_of_nonstuck t ht
  have hBool := typed_arith_to_int_elim_to_real t hTTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (toIntToRealTerm t)) t) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (toIntToRealTerm t) t hBool'
    (eval_to_int_to_real_rel M hM t hTTrans hTInt)

private theorem prog_arith_div_total_zero_real_eq_of_nonstuck
    (t : Term)
    (ht : t ≠ Term.Stuck) :
    __eo_prog_arith_div_total_zero_real t =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
          (Term.Rational (native_mk_rational 0 1))))
        (Term.Rational (native_mk_rational 0 1)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  simp [__eo_prog_arith_div_total_zero_real, htSt]

private theorem prog_arith_div_total_zero_int_eq_of_nonstuck
    (t : Term)
    (ht : t ≠ Term.Stuck) :
    __eo_prog_arith_div_total_zero_int t =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
          (Term.Numeral 0)))
        (Term.Rational (native_mk_rational 0 1)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  simp [__eo_prog_arith_div_total_zero_int, htSt]

private theorem arith_div_total_zero_real_arg_type_of_result
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_div_total_zero_real t) = Term.Bool) :
    __eo_typeof t = Term.Real := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_div_total_zero_real_eq_of_nonstuck t ht
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
        (Term.Rational (native_mk_rational 0 1))))
      Term.Real = Term.Bool at hResultTy
  rcases eo_typeof_eq_bool_same hResultTy with ⟨hSame, hQdivNonStuck⟩
  change __eo_typeof_qdiv (__eo_typeof t) Term.Real = Term.Real at hSame
  change __eo_typeof_qdiv (__eo_typeof t) Term.Real ≠ Term.Stuck at hQdivNonStuck
  cases hTy : __eo_typeof t with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
          __is_arith_type, native_ite, native_teq, native_not,
          SmtEval.native_not, hTy] at hSame hQdivNonStuck ⊢
  | _ =>
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not,
        SmtEval.native_not, hTy] at hSame hQdivNonStuck

private theorem arith_div_total_zero_int_arg_type_of_result
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_div_total_zero_int t) = Term.Bool) :
    __eo_typeof t = Term.Int := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_div_total_zero_int_eq_of_nonstuck t ht
  rw [hProgEq] at hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
        (Term.Numeral 0)))
      Term.Real = Term.Bool at hResultTy
  rcases eo_typeof_eq_bool_same hResultTy with ⟨hSame, hQdivNonStuck⟩
  change __eo_typeof_qdiv (__eo_typeof t) Term.Int = Term.Real at hSame
  change __eo_typeof_qdiv (__eo_typeof t) Term.Int ≠ Term.Stuck at hQdivNonStuck
  cases hTy : __eo_typeof t with
  | UOp op =>
      cases op <;>
        simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
          __is_arith_type, native_ite, native_teq, native_not,
          SmtEval.native_not, hTy] at hSame hQdivNonStuck ⊢
  | _ =>
      simp [__eo_typeof_qdiv, __eo_requires, __eo_eq,
        __is_arith_type, native_ite, native_teq, native_not,
        SmtEval.native_not, hTy] at hSame hQdivNonStuck

private theorem eval_qdiv_total_real_zero_rel
    (M : SmtModel) (hM : model_wf M)
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTReal : __eo_typeof t = Term.Real) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
          (Term.Rational (native_mk_rational 0 1)))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Rational (native_mk_rational 0 1)))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Real (__eo_to_smt t) rfl hTTrans hTReal
  rcases smt_eval_real_of_type M hM t hSmtT with ⟨q, hEvalT⟩
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_qdiv_total_eq, smtx_eval_qdiv_total_term_eq]
  rw [hEvalT, rational_smt_eval M (native_mk_rational 0 1)]
  rw [show __smtx_model_eval_qdiv_total (SmtValue.Rational q)
      (SmtValue.Rational (native_mk_rational 0 1)) =
      SmtValue.Rational (native_mk_rational 0 1) by
    simp [__smtx_model_eval_qdiv_total, native_qdiv_total_zero]]
  exact RuleProofs.smtx_model_eval_eq_refl
    (SmtValue.Rational (native_mk_rational 0 1))

private theorem eval_qdiv_total_int_zero_rel
    (M : SmtModel) (hM : model_wf M)
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTInt : __eo_typeof t = Term.Int) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
          (Term.Numeral 0))))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Rational (native_mk_rational 0 1)))) := by
  have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
  rcases smt_eval_int_of_type M hM t hSmtT with ⟨n, hEvalT⟩
  unfold RuleProofs.smt_value_rel
  rw [eo_to_smt_qdiv_total_eq, smtx_eval_qdiv_total_term_eq]
  rw [hEvalT, numeral_smt_eval M 0,
    rational_smt_eval M (native_mk_rational 0 1)]
  rw [show __smtx_model_eval_qdiv_total (SmtValue.Numeral n) (SmtValue.Numeral 0) =
      SmtValue.Rational (native_mk_rational 0 1) by
    simp [__smtx_model_eval_qdiv_total, native_mk_rational_zero_den]]
  exact RuleProofs.smtx_model_eval_eq_refl
    (SmtValue.Rational (native_mk_rational 0 1))

theorem typed_arith_div_total_zero_real
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_div_total_zero_real t) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_div_total_zero_real t) := by
  have hTReal := arith_div_total_zero_real_arg_type_of_result t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_div_total_zero_real_eq_of_nonstuck t ht
  have hQdivTy :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
          (Term.Rational (native_mk_rational 0 1)))) = SmtType.Real := by
    have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hTReal
    rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hSmtT,
      rational_smt_type (native_mk_rational 0 1)]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
      (Term.Rational (native_mk_rational 0 1)))
    (Term.Rational (native_mk_rational 0 1))
    (by rw [hQdivTy, rational_smt_type])
    (by rw [hQdivTy]; simp)

theorem facts_arith_div_total_zero_real
    (M : SmtModel) (hM : model_wf M)
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_div_total_zero_real t) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_div_total_zero_real t) true := by
  have hTReal := arith_div_total_zero_real_arg_type_of_result t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_div_total_zero_real_eq_of_nonstuck t ht
  have hBool := typed_arith_div_total_zero_real t hTTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
            (Term.Rational (native_mk_rational 0 1))))
          (Term.Rational (native_mk_rational 0 1))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
      (Term.Rational (native_mk_rational 0 1)))
    (Term.Rational (native_mk_rational 0 1))
    hBool'
    (eval_qdiv_total_real_zero_rel M hM t hTTrans hTReal)

theorem typed_arith_div_total_zero_int
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_div_total_zero_int t) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_div_total_zero_int t) := by
  have hTInt := arith_div_total_zero_int_arg_type_of_result t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_div_total_zero_int_eq_of_nonstuck t ht
  have hQdivTy :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
          (Term.Numeral 0))) = SmtType.Real := by
    have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hTInt
    rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hSmtT, numeral_smt_type 0]
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
      (Term.Numeral 0))
    (Term.Rational (native_mk_rational 0 1))
    (by rw [hQdivTy, rational_smt_type])
    (by rw [hQdivTy]; simp)

theorem facts_arith_div_total_zero_int
    (M : SmtModel) (hM : model_wf M)
    (t : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hResultTy : __eo_typeof (__eo_prog_arith_div_total_zero_int t) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_div_total_zero_int t) true := by
  have hTInt := arith_div_total_zero_int_arg_type_of_result t hTTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hProgEq := prog_arith_div_total_zero_int_eq_of_nonstuck t ht
  have hBool := typed_arith_div_total_zero_int t hTTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
            (Term.Numeral 0)))
          (Term.Rational (native_mk_rational 0 1))) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t)
      (Term.Numeral 0))
    (Term.Rational (native_mk_rational 0 1))
    hBool'
    (eval_qdiv_total_int_zero_rel M hM t hTTrans hTInt)

private theorem eq_true_lhs_typeof_bool (lhs : Term)
    (h : __eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) (Term.Boolean true)) =
      Term.Bool) :
    __eo_typeof lhs = Term.Bool := by
  change __eo_typeof_eq (__eo_typeof lhs) Term.Bool = Term.Bool at h
  exact (eo_typeof_eq_bool_same h).1

private theorem smt_types_same_of_eo_arg_type_cases
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    __smtx_typeof (__eo_to_smt t) = __smtx_typeof (__eo_to_smt s) := by
  rcases hArgTypes with hInt | hReal
  · have hT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
    have hS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
    rw [hT, hS]
  · have hT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
    have hS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
    rw [hT, hS]

private theorem arith_rel_typeof_bool_of_arg_type_cases
    (t s : Term)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool := by
  rcases hArgTypes with hInt | hReal
  · rw [hInt.1, hInt.2]
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, SmtEval.native_not]
  · rw [hReal.1, hReal.2]
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, SmtEval.native_not]

private theorem prog_arith_min_lt1_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_min_lt1 t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (relTerm UserOp.leq (minLtTerm t s) t)) (Term.Boolean true) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_min_lt1, relTerm, minLtTerm, iteTerm, htSt, hsSt]

private theorem arith_min_lt1_arg_type_cases_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_min_lt1 t s) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_min_lt1_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.leq (minLtTerm t s) t)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hLeqTy :
      __eo_typeof (relTerm UserOp.leq (minLtTerm t s) t) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.leq (minLtTerm t s) t) hResultTy'
  change __eo_typeof_lt (__eo_typeof (minLtTerm t s)) (__eo_typeof t) =
    Term.Bool at hLeqTy
  rcases eo_typeof_lt_bool_cases hLeqTy with hInt | hReal
  · left
    have hSInt : __eo_typeof s = Term.Int := by
      have hIteTy : __eo_typeof (minLtTerm t s) = Term.Int := hInt.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Int at hIteTy
      rw [hInt.2] at hIteTy
      cases hS : __eo_typeof s with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hS] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hS] at hIteTy
    exact ⟨hInt.2, hSInt⟩
  · right
    have hSReal : __eo_typeof s = Term.Real := by
      have hIteTy : __eo_typeof (minLtTerm t s) = Term.Real := hReal.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Real at hIteTy
      rw [hReal.2] at hIteTy
      cases hS : __eo_typeof s with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hS] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hS] at hIteTy
    exact ⟨hReal.2, hSReal⟩

private theorem eval_min_lt1_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (relTerm UserOp.leq (minLtTerm t s) t)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true))) := by
  rcases hArgTypes with hInt | hReal
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
    rcases smt_eval_int_of_type M hM t hSmtT with ⟨nt, hEvalT⟩
    rcases smt_eval_int_of_type M hM s hSmtS with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.leq (minLtTerm t s) t) =
        SmtTerm.leq
          (SmtTerm.ite (SmtTerm.lt (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt t) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_18, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hLt : native_zlt nt ns
    · have hLe := native_zlt_false_leq_swap nt ns hLt
      simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt, hLe, native_veq]
    · simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt,
        native_zleq_refl_true, native_veq]
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
    rcases smt_eval_real_of_type M hM t hSmtT with ⟨qt, hEvalT⟩
    rcases smt_eval_real_of_type M hM s hSmtS with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.leq (minLtTerm t s) t) =
        SmtTerm.leq
          (SmtTerm.ite (SmtTerm.lt (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt t) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_18, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hLt : native_qlt qt qs
    · have hLe := native_qlt_false_leq_swap qt qs hLt
      simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt, hLe, native_veq]
    · simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt,
        native_qleq_refl_true, native_veq]

theorem typed_arith_min_lt1
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_min_lt1 t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_min_lt1 t s) := by
  have hArgTypes :=
    arith_min_lt1_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_min_lt1_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.leq (minLtTerm t s) t)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hLeqTy :
      __eo_typeof (relTerm UserOp.leq (minLtTerm t s) t) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.leq (minLtTerm t s) t) hResultTy'
  have hCondTy :
      __eo_typeof (relTerm UserOp.lt t s) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact arith_rel_typeof_bool_of_arg_type_cases t s hArgTypes
  have hCondBool : RuleProofs.eo_has_bool_type (relTerm UserOp.lt t s) := by
    exact lt_has_bool_type t s hTTrans hSTrans hCondTy
  have hSame := smt_types_same_of_eo_arg_type_cases t s hTTrans hSTrans hArgTypes
  have hIteTrans :
      RuleProofs.eo_has_smt_translation (minLtTerm t s) :=
    ite_has_smt_translation_same_type (relTerm UserOp.lt t s) t s
      hCondBool hTTrans hSame
  rw [hProgEq]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (relTerm UserOp.leq (minLtTerm t s) t) (Term.Boolean true)
    (leq_has_bool_type (minLtTerm t s) t hIteTrans hTTrans hLeqTy)
    true_has_bool_type

theorem facts_arith_min_lt1
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_min_lt1 t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_min_lt1 t s) true := by
  have hArgTypes :=
    arith_min_lt1_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_min_lt1_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_min_lt1 t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.leq (minLtTerm t s) t)) (Term.Boolean true)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (relTerm UserOp.leq (minLtTerm t s) t)
    (Term.Boolean true)
    hBool'
    (eval_min_lt1_rel M hM t s hTTrans hSTrans hArgTypes)

private theorem prog_arith_min_lt2_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_min_lt2 t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (relTerm UserOp.leq (minLtTerm t s) s)) (Term.Boolean true) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_min_lt2, relTerm, minLtTerm, iteTerm, htSt, hsSt]

private theorem arith_min_lt2_arg_type_cases_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_min_lt2 t s) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_min_lt2_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.leq (minLtTerm t s) s)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hLeqTy :
      __eo_typeof (relTerm UserOp.leq (minLtTerm t s) s) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.leq (minLtTerm t s) s) hResultTy'
  change __eo_typeof_lt (__eo_typeof (minLtTerm t s)) (__eo_typeof s) =
    Term.Bool at hLeqTy
  rcases eo_typeof_lt_bool_cases hLeqTy with hInt | hReal
  · left
    have hTInt : __eo_typeof t = Term.Int := by
      have hIteTy : __eo_typeof (minLtTerm t s) = Term.Int := hInt.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Int at hIteTy
      rw [hInt.2] at hIteTy
      cases hT : __eo_typeof t with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hT] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hT] at hIteTy
    exact ⟨hTInt, hInt.2⟩
  · right
    have hTReal : __eo_typeof t = Term.Real := by
      have hIteTy : __eo_typeof (minLtTerm t s) = Term.Real := hReal.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Real at hIteTy
      rw [hReal.2] at hIteTy
      cases hT : __eo_typeof t with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hT] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hT] at hIteTy
    exact ⟨hTReal, hReal.2⟩

private theorem eval_min_lt2_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (relTerm UserOp.leq (minLtTerm t s) s)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true))) := by
  rcases hArgTypes with hInt | hReal
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
    rcases smt_eval_int_of_type M hM t hSmtT with ⟨nt, hEvalT⟩
    rcases smt_eval_int_of_type M hM s hSmtS with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.leq (minLtTerm t s) s) =
        SmtTerm.leq
          (SmtTerm.ite (SmtTerm.lt (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt s) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_18, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hLt : native_zlt nt ns
    · simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt,
        native_zleq_refl_true, native_veq]
    · have hLe := native_zlt_true_leq nt ns hLt
      simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt, hLe, native_veq]
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
    rcases smt_eval_real_of_type M hM t hSmtT with ⟨qt, hEvalT⟩
    rcases smt_eval_real_of_type M hM s hSmtS with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.leq (minLtTerm t s) s) =
        SmtTerm.leq
          (SmtTerm.ite (SmtTerm.lt (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt s) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_18, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_17, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hLt : native_qlt qt qs
    · simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt,
        native_qleq_refl_true, native_veq]
    · have hLe := native_qlt_true_leq qt qs hLt
      simp [__smtx_model_eval_ite, __smtx_model_eval_lt,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hLt, hLe, native_veq]

theorem typed_arith_min_lt2
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_min_lt2 t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_min_lt2 t s) := by
  have hArgTypes :=
    arith_min_lt2_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_min_lt2_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.leq (minLtTerm t s) s)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hLeqTy :
      __eo_typeof (relTerm UserOp.leq (minLtTerm t s) s) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.leq (minLtTerm t s) s) hResultTy'
  have hCondTy :
      __eo_typeof (relTerm UserOp.lt t s) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact arith_rel_typeof_bool_of_arg_type_cases t s hArgTypes
  have hCondBool : RuleProofs.eo_has_bool_type (relTerm UserOp.lt t s) := by
    exact lt_has_bool_type t s hTTrans hSTrans hCondTy
  have hSame := smt_types_same_of_eo_arg_type_cases t s hTTrans hSTrans hArgTypes
  have hIteTrans :
      RuleProofs.eo_has_smt_translation (minLtTerm t s) :=
    ite_has_smt_translation_same_type (relTerm UserOp.lt t s) t s
      hCondBool hTTrans hSame
  rw [hProgEq]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (relTerm UserOp.leq (minLtTerm t s) s) (Term.Boolean true)
    (leq_has_bool_type (minLtTerm t s) s hIteTrans hSTrans hLeqTy)
    true_has_bool_type

theorem facts_arith_min_lt2
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_min_lt2 t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_min_lt2 t s) true := by
  have hArgTypes :=
    arith_min_lt2_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_min_lt2_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_min_lt2 t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.leq (minLtTerm t s) s)) (Term.Boolean true)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (relTerm UserOp.leq (minLtTerm t s) s)
    (Term.Boolean true)
    hBool'
    (eval_min_lt2_rel M hM t s hTTrans hSTrans hArgTypes)

private theorem prog_arith_max_geq1_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_max_geq1 t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (relTerm UserOp.geq (maxGeqTerm t s) t)) (Term.Boolean true) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_max_geq1, relTerm, maxGeqTerm, iteTerm, htSt, hsSt]

private theorem prog_arith_max_geq2_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_max_geq2 t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (relTerm UserOp.geq (maxGeqTerm t s) s)) (Term.Boolean true) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_max_geq2, relTerm, maxGeqTerm, iteTerm, htSt, hsSt]

private theorem arith_max_geq1_arg_type_cases_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_max_geq1 t s) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_max_geq1_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.geq (maxGeqTerm t s) t)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hGeqTy :
      __eo_typeof (relTerm UserOp.geq (maxGeqTerm t s) t) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.geq (maxGeqTerm t s) t) hResultTy'
  change __eo_typeof_lt (__eo_typeof (maxGeqTerm t s)) (__eo_typeof t) =
    Term.Bool at hGeqTy
  rcases eo_typeof_lt_bool_cases hGeqTy with hInt | hReal
  · left
    have hSInt : __eo_typeof s = Term.Int := by
      have hIteTy : __eo_typeof (maxGeqTerm t s) = Term.Int := hInt.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Int at hIteTy
      rw [hInt.2] at hIteTy
      cases hS : __eo_typeof s with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hS] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hS] at hIteTy
    exact ⟨hInt.2, hSInt⟩
  · right
    have hSReal : __eo_typeof s = Term.Real := by
      have hIteTy : __eo_typeof (maxGeqTerm t s) = Term.Real := hReal.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Real at hIteTy
      rw [hReal.2] at hIteTy
      cases hS : __eo_typeof s with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hS] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hS] at hIteTy
    exact ⟨hReal.2, hSReal⟩

private theorem arith_max_geq2_arg_type_cases_of_result
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_max_geq2 t s) = Term.Bool) :
    (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_max_geq2_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.geq (maxGeqTerm t s) s)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hGeqTy :
      __eo_typeof (relTerm UserOp.geq (maxGeqTerm t s) s) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.geq (maxGeqTerm t s) s) hResultTy'
  change __eo_typeof_lt (__eo_typeof (maxGeqTerm t s)) (__eo_typeof s) =
    Term.Bool at hGeqTy
  rcases eo_typeof_lt_bool_cases hGeqTy with hInt | hReal
  · left
    have hTInt : __eo_typeof t = Term.Int := by
      have hIteTy : __eo_typeof (maxGeqTerm t s) = Term.Int := hInt.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Int at hIteTy
      rw [hInt.2] at hIteTy
      cases hT : __eo_typeof t with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hT] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hInt.2, hT] at hIteTy
    exact ⟨hTInt, hInt.2⟩
  · right
    have hTReal : __eo_typeof t = Term.Real := by
      have hIteTy : __eo_typeof (maxGeqTerm t s) = Term.Real := hReal.1
      change __eo_typeof_ite (__eo_typeof_lt (__eo_typeof t) (__eo_typeof s))
        (__eo_typeof t) (__eo_typeof s) = Term.Real at hIteTy
      rw [hReal.2] at hIteTy
      cases hT : __eo_typeof t with
      | UOp op =>
          cases op <;> simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hT] at hIteTy ⊢
      | _ =>
          simp [__eo_typeof_lt, __eo_typeof_ite,
            __eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
            native_not, SmtEval.native_not, hReal.2, hT] at hIteTy
    exact ⟨hTReal, hReal.2⟩

private theorem eval_max_geq1_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (relTerm UserOp.geq (maxGeqTerm t s) t)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true))) := by
  rcases hArgTypes with hInt | hReal
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
    rcases smt_eval_int_of_type M hM t hSmtT with ⟨nt, hEvalT⟩
    rcases smt_eval_int_of_type M hM s hSmtS with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.geq (maxGeqTerm t s) t) =
        SmtTerm.geq
          (SmtTerm.ite (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt t) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_20, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hGeq : native_zleq ns nt
    · have hLe := native_zleq_false_leq_swap ns nt hGeq
      simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq, hLe, native_veq]
    · simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq,
        native_zleq_refl_true, native_veq]
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
    rcases smt_eval_real_of_type M hM t hSmtT with ⟨qt, hEvalT⟩
    rcases smt_eval_real_of_type M hM s hSmtS with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.geq (maxGeqTerm t s) t) =
        SmtTerm.geq
          (SmtTerm.ite (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt t) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_20, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hGeq : native_qleq qs qt
    · have hLe := native_qleq_false_leq_swap qs qt hGeq
      simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq, hLe, native_veq]
    · simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq,
        native_qleq_refl_true, native_veq]

private theorem eval_max_geq2_rel
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hArgTypes :
      (__eo_typeof t = Term.Int ∧ __eo_typeof s = Term.Int) ∨
      (__eo_typeof t = Term.Real ∧ __eo_typeof s = Term.Real)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (relTerm UserOp.geq (maxGeqTerm t s) s)))
      (__smtx_model_eval M (__eo_to_smt (Term.Boolean true))) := by
  rcases hArgTypes with hInt | hReal
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Int (__eo_to_smt t) rfl hTTrans hInt.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Int :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Int (__eo_to_smt s) rfl hSTrans hInt.2
    rcases smt_eval_int_of_type M hM t hSmtT with ⟨nt, hEvalT⟩
    rcases smt_eval_int_of_type M hM s hSmtS with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.geq (maxGeqTerm t s) s) =
        SmtTerm.geq
          (SmtTerm.ite (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt s) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_20, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hGeq : native_zleq ns nt
    · simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq,
        native_zleq_refl_true, native_veq]
    · simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq, native_veq]
  · have hSmtT : __smtx_typeof (__eo_to_smt t) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t Term.Real (__eo_to_smt t) rfl hTTrans hReal.1
    have hSmtS : __smtx_typeof (__eo_to_smt s) = SmtType.Real :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s Term.Real (__eo_to_smt s) rfl hSTrans hReal.2
    rcases smt_eval_real_of_type M hM t hSmtT with ⟨qt, hEvalT⟩
    rcases smt_eval_real_of_type M hM s hSmtS with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [show __eo_to_smt (relTerm UserOp.geq (maxGeqTerm t s) s) =
        SmtTerm.geq
          (SmtTerm.ite (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s))
            (__eo_to_smt t) (__eo_to_smt s))
          (__eo_to_smt s) by rfl]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_model_eval.eq_20, smtx_eval_ite_term_eq,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_1]
    rw [hEvalT, hEvalS]
    cases hGeq : native_qleq qs qt
    · simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq,
        native_qleq_refl_true, native_veq]
    · simp [__smtx_model_eval_ite, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, hGeq, native_veq]

theorem typed_arith_max_geq1
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_max_geq1 t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_max_geq1 t s) := by
  have hArgTypes :=
    arith_max_geq1_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_max_geq1_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.geq (maxGeqTerm t s) t)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hGeqTy :
      __eo_typeof (relTerm UserOp.geq (maxGeqTerm t s) t) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.geq (maxGeqTerm t s) t) hResultTy'
  have hCondTy :
      __eo_typeof (relTerm UserOp.geq t s) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact arith_rel_typeof_bool_of_arg_type_cases t s hArgTypes
  have hCondBool : RuleProofs.eo_has_bool_type (relTerm UserOp.geq t s) := by
    exact geq_has_bool_type t s hTTrans hSTrans hCondTy
  have hSame := smt_types_same_of_eo_arg_type_cases t s hTTrans hSTrans hArgTypes
  have hIteTrans :
      RuleProofs.eo_has_smt_translation (maxGeqTerm t s) :=
    ite_has_smt_translation_same_type (relTerm UserOp.geq t s) t s
      hCondBool hTTrans hSame
  rw [hProgEq]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (relTerm UserOp.geq (maxGeqTerm t s) t) (Term.Boolean true)
    (geq_has_bool_type (maxGeqTerm t s) t hIteTrans hTTrans hGeqTy)
    true_has_bool_type

theorem typed_arith_max_geq2
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_max_geq2 t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_max_geq2 t s) := by
  have hArgTypes :=
    arith_max_geq2_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_max_geq2_eq_of_nonstuck t s ht hs
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.geq (maxGeqTerm t s) s)) (Term.Boolean true)) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hGeqTy :
      __eo_typeof (relTerm UserOp.geq (maxGeqTerm t s) s) = Term.Bool :=
    eq_true_lhs_typeof_bool (relTerm UserOp.geq (maxGeqTerm t s) s) hResultTy'
  have hCondTy :
      __eo_typeof (relTerm UserOp.geq t s) = Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact arith_rel_typeof_bool_of_arg_type_cases t s hArgTypes
  have hCondBool : RuleProofs.eo_has_bool_type (relTerm UserOp.geq t s) := by
    exact geq_has_bool_type t s hTTrans hSTrans hCondTy
  have hSame := smt_types_same_of_eo_arg_type_cases t s hTTrans hSTrans hArgTypes
  have hIteTrans :
      RuleProofs.eo_has_smt_translation (maxGeqTerm t s) :=
    ite_has_smt_translation_same_type (relTerm UserOp.geq t s) t s
      hCondBool hTTrans hSame
  rw [hProgEq]
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (relTerm UserOp.geq (maxGeqTerm t s) s) (Term.Boolean true)
    (geq_has_bool_type (maxGeqTerm t s) s hIteTrans hSTrans hGeqTy)
    true_has_bool_type

theorem facts_arith_max_geq1
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_max_geq1 t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_max_geq1 t s) true := by
  have hArgTypes :=
    arith_max_geq1_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_max_geq1_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_max_geq1 t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.geq (maxGeqTerm t s) t)) (Term.Boolean true)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (relTerm UserOp.geq (maxGeqTerm t s) t)
    (Term.Boolean true)
    hBool'
    (eval_max_geq1_rel M hM t s hTTrans hSTrans hArgTypes)

theorem facts_arith_max_geq2
    (M : SmtModel) (hM : model_wf M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_max_geq2 t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_max_geq2 t s) true := by
  have hArgTypes :=
    arith_max_geq2_arg_type_cases_of_result t s hTTrans hSTrans hResultTy
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_max_geq2_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_max_geq2 t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (relTerm UserOp.geq (maxGeqTerm t s) s)) (Term.Boolean true)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (relTerm UserOp.geq (maxGeqTerm t s) s)
    (Term.Boolean true)
    hBool'
    (eval_max_geq2_rel M hM t s hTTrans hSTrans hArgTypes)

end ArithSimpleSupport
