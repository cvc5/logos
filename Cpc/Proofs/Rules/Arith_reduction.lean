module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem smt_qdiv_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       let yr := __smtx_to_real_coerce yv
       let xr := __smtx_to_real_coerce xv
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yr (SmtValue.Rational (native_mk_rational 0 1)))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_qdiv_by_zero_id
             (SmtType.FunType SmtType.Real SmtType.Real))
           xr)
         (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [smtx_eval_qdiv_term_eq]

private theorem smt_div_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.div x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_div_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_div_total xv yv)) := by
  rw [__smtx_model_eval.eq_26]

private theorem smt_div_eval_reduction_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.div x (SmtTerm.Numeral 0))
          (SmtTerm.div_total x y))) := by
  rw [smt_div_eval_reduction_self, smtx_eval_ite_term_eq,
    smtx_eval_eq_term_eq, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_26, __smtx_model_eval.eq_31]
  cases hy : __smtx_model_eval M y <;>
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_div_total, native_veq] <;>
    try exact RuleProofs.smt_value_rel_refl _

private theorem smt_mod_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_mod_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_mod_total xv yv)) := by
  rw [__smtx_model_eval.eq_27]

private theorem smt_mod_eval_reduction_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.mod x (SmtTerm.Numeral 0))
          (SmtTerm.mod_total x y))) := by
  rw [smt_mod_eval_reduction_self, smtx_eval_ite_term_eq,
    smtx_eval_eq_term_eq, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_27, __smtx_model_eval.eq_32]
  cases hy : __smtx_model_eval M y <;>
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_mod_total, native_veq] <;>
    try exact RuleProofs.smt_value_rel_refl _

private theorem rat_div_one (q : Rat) : q / (1 : Rat) = q := by
  rw [Rat.div_def]
  have hInvOne : (1 : Rat)⁻¹ = 1 := by
    native_decide
  rw [hInvOne, Rat.mul_one]

private theorem smt_abs_eval_reduction_int_term_rel
    (M : SmtModel) (x : SmtTerm) (n : native_Int)
    (hx : __smtx_model_eval M x = SmtValue.Numeral n) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs x))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.lt x (SmtTerm.Numeral 0))
          (SmtTerm.uneg x)
          x)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [__smtx_model_eval.eq_24, smtx_eval_ite_term_eq,
    __smtx_model_eval.eq_17, __smtx_model_eval.eq_2, __smtx_model_eval.eq_25]
  by_cases hlt : n < 0
  · simp [hx, __smtx_model_eval_abs, __smtx_model_eval_lt,
      __smtx_model_eval_ite, __smtx_model_eval_uneg, __smtx_model_eval_eq,
      native_veq, native_zabs, native_zlt, native_zneg, hlt]
  · simp [hx, __smtx_model_eval_abs, __smtx_model_eval_lt,
      __smtx_model_eval_ite, __smtx_model_eval_uneg, __smtx_model_eval_eq,
      native_veq, native_zabs, native_zlt, native_zneg, hlt]

private theorem smt_abs_eval_reduction_real_term_rel
    (M : SmtModel) (x : SmtTerm) (q : native_Rat)
    (hx : __smtx_model_eval M x = SmtValue.Rational q) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs x))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.lt x (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.uneg x)
          x)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [__smtx_model_eval.eq_24, smtx_eval_ite_term_eq,
    __smtx_model_eval.eq_17, __smtx_model_eval.eq_3, __smtx_model_eval.eq_25]
  by_cases hlt : q < 0
  · simp [hx, __smtx_model_eval_abs, __smtx_model_eval_lt,
      __smtx_model_eval_ite, __smtx_model_eval_uneg, __smtx_model_eval_eq,
      native_veq, native_qabs, native_qlt, native_qneg, native_mk_rational,
      rat_div_one, hlt]
  · simp [hx, __smtx_model_eval_abs, __smtx_model_eval_lt,
      __smtx_model_eval_ite, __smtx_model_eval_uneg, __smtx_model_eval_eq,
      native_veq, native_qabs, native_qlt, native_qneg, native_mk_rational,
      rat_div_one, hlt]

private theorem arith_reduction_abs_arg_cases
    (u : Term)
    (hAbsNN : term_has_non_none_type (SmtTerm.abs (__eo_to_smt u))) :
    (__smtx_typeof (__eo_to_smt u) = SmtType.Int ∧
        __eo_typeof u = Term.UOp UserOp.Int ∧
        __eo_to_smt (__arith_mk_zero (__eo_typeof u)) = SmtTerm.Numeral 0) ∨
      (__smtx_typeof (__eo_to_smt u) = SmtType.Real ∧
        __eo_typeof u = Term.UOp UserOp.Real ∧
        __eo_to_smt (__arith_mk_zero (__eo_typeof u)) =
          SmtTerm.Rational (native_mk_rational 0 1)) := by
  rcases abs_arg_of_non_none hAbsNN with hUSmtTy | hUSmtTy
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hUSmtTy (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    exact Or.inl ⟨hUSmtTy, hUEoTy, by rw [hUEoTy]; rfl⟩
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hUSmtTy (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    exact Or.inr ⟨hUSmtTy, hUEoTy, by rw [hUEoTy]; rfl⟩

private theorem native_to_real_qdiv_total
    (n1 n2 : native_Int) :
    native_qdiv_total (native_to_real n1) (native_to_real n2) =
      native_mk_rational n1 n2 := by
  rw [native_qdiv_total, native_to_real, native_to_real, native_mk_rational,
    native_mk_rational, native_mk_rational]
  rw [Rat.div_def]
  have hInv :
      ((↑n2 / ↑(1 : Int) : Rat)⁻¹) = ((↑(1 : Int) / ↑n2 : Rat)) := by
    simpa [Rat.divInt_eq_div] using (Rat.inv_divInt n2 1)
  rw [hInv]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 1 (d₁ := 1) (d₂ := n2))

private theorem native_to_real_eq_zero_iff (n : native_Int) :
    native_to_real n = native_mk_rational 0 1 ↔ n = 0 := by
  unfold native_to_real native_mk_rational
  simp [rat_div_one]

private theorem native_qmult_qdiv_total_cancel
    (q1 q2 : native_Rat) (h : q2 ≠ 0) :
    native_qmult q2
      (native_qmult (native_qdiv_total q1 q2) (native_mk_rational 1 1)) =
      q1 := by
  unfold native_qmult native_qdiv_total native_mk_rational
  simp [rat_div_one]
  rw [Rat.div_def]
  rw [Rat.mul_comm q1 q2⁻¹]
  rw [← Rat.mul_assoc]
  rw [Rat.mul_inv_cancel q2 h]
  rw [Rat.one_mul]

private theorem native_to_real_qmult_mk_rational_cancel
    (n1 n2 : native_Int) (h : n2 ≠ 0) :
    native_qmult (native_to_real n2)
      (native_qmult (native_mk_rational n1 n2) (native_mk_rational 1 1)) =
      native_to_real n1 := by
  unfold native_qmult native_to_real native_mk_rational
  simp [rat_div_one]
  rw [Rat.div_def]
  rw [Rat.mul_comm (n1 : Rat) (n2 : Rat)⁻¹]
  rw [← Rat.mul_assoc]
  have hRat : (n2 : Rat) ≠ 0 := by
    exact_mod_cast h
  rw [Rat.mul_inv_cancel (n2 : Rat) hRat]
  rw [Rat.one_mul]

private theorem smt_qdiv_eval_reduction_int_term_rel
    (M : SmtModel) (x y : SmtTerm) (n1 n2 : native_Int)
    (hx : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hy : __smtx_model_eval M y = SmtValue.Numeral n2) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.qdiv (SmtTerm.to_real x)
            (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv_total x y))) := by
  rw [smt_qdiv_eval_reduction_self, smtx_eval_ite_term_eq,
    smtx_eval_eq_term_eq, __smtx_model_eval.eq_2,
    smtx_eval_qdiv_term_eq, smtx_eval_qdiv_total_term_eq,
    __smtx_model_eval.eq_21, __smtx_model_eval.eq_3]
  by_cases hZero : n2 = 0
  · simp [hx, hy, hZero, __smtx_model_eval_to_real, __smtx_to_real_coerce,
      __smtx_model_eval_eq,
      __smtx_model_eval_ite, native_veq, native_to_real_eq_zero_iff]
    exact RuleProofs.smt_value_rel_refl _
  · simp [hx, hy, hZero, __smtx_model_eval_to_real, __smtx_to_real_coerce,
      __smtx_model_eval_eq,
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total, native_veq,
      native_to_real_eq_zero_iff, native_to_real_qdiv_total]
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_qdiv_eval_reduction_real_term_rel
    (M : SmtModel) (x y : SmtTerm) (q1 q2 : native_Rat)
    (hx : __smtx_model_eval M x = SmtValue.Rational q1)
    (hy : __smtx_model_eval M y = SmtValue.Rational q2) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv x (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv_total x y))) := by
  rw [smt_qdiv_eval_reduction_self, smtx_eval_ite_term_eq,
    smtx_eval_eq_term_eq, __smtx_model_eval.eq_3,
    smtx_eval_qdiv_term_eq, smtx_eval_qdiv_total_term_eq]
  by_cases hZero : q2 = native_mk_rational 0 1
  · simp [hx, hy, hZero, __smtx_to_real_coerce, __smtx_model_eval_eq,
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
      __smtx_model_eval.eq_3, native_veq]
    exact RuleProofs.smt_value_rel_refl _
  · simp [hx, hy, hZero, __smtx_to_real_coerce, __smtx_model_eval_eq,
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
      __smtx_model_eval.eq_3, native_veq]
    exact RuleProofs.smt_value_rel_refl _

private theorem rat_floor_remainder_nonneg (q : Rat) :
    (0 : Rat) ≤ q - (q.floor : Rat) := by
  rw [Rat.sub_eq_add_neg]
  have hFloor := Rat.floor_le q
  have hShift :
      (q.floor : Rat) + (-(q.floor : Rat)) ≤
        q + (-(q.floor : Rat)) :=
    (Rat.add_le_add_right (a := (q.floor : Rat)) (b := q)
      (c := -(q.floor : Rat))).mpr hFloor
  rwa [Rat.add_neg_cancel] at hShift

private theorem rat_floor_remainder_lt_one (q : Rat) :
    q - (q.floor : Rat) < 1 := by
  rw [Rat.sub_eq_add_neg]
  have hFloor := Rat.lt_floor_add_one q
  have hShift :
      q + (-(q.floor : Rat)) <
        ((q.floor + 1 : Int) : Rat) + (-(q.floor : Rat)) :=
    (Rat.add_lt_add_right (a := q) (b := ((q.floor + 1 : Int) : Rat))
      (c := -(q.floor : Rat))).mpr hFloor
  rw [Rat.intCast_add, Rat.intCast_one] at hShift
  rw [Rat.add_assoc] at hShift
  rw [Rat.add_comm (1 : Rat) (-(q.floor : Rat))] at hShift
  rwa [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add] at hShift

private theorem native_floor_remainder_nonneg (q : Rat) :
    native_qleq (native_mk_rational 0 1)
      (native_qplus q (native_qneg (native_to_real (native_to_int q)))) =
      true := by
  unfold native_qleq native_qplus native_qneg native_to_real native_to_int
    native_mk_rational
  rw [decide_eq_true_eq]
  simp [rat_div_one]
  rw [← Rat.sub_eq_add_neg]
  exact rat_floor_remainder_nonneg q

private theorem native_floor_remainder_lt_one (q : Rat) :
    native_qlt
      (native_qplus q (native_qneg (native_to_real (native_to_int q))))
      (native_mk_rational 1 1) =
      true := by
  unfold native_qlt native_qplus native_qneg native_to_real native_to_int
    native_mk_rational
  rw [decide_eq_true_eq]
  simp [rat_div_one]
  rw [← Rat.sub_eq_add_neg]
  exact rat_floor_remainder_lt_one q

private theorem native_int_pow2_log2_le
    (n : native_Int) (hPos : 0 < n) :
    native_zleq (native_int_pow2 (native_int_log2 n)) n = true := by
  unfold native_zleq
  rw [decide_eq_true_eq]
  unfold native_int_pow2 native_int_log2 native_zexp_total
  simp
  have hnNatNe : n.toNat ≠ 0 := by
    intro h0
    have hle : n ≤ 0 := Int.toNat_eq_zero.mp h0
    exact (Int.not_le.mpr hPos) hle
  have hNat := Nat.log2_self_le hnNatNe
  have hCast : ((2 ^ Nat.log2 n.toNat : Nat) : Int) ≤ (n.toNat : Int) := by
    exact_mod_cast hNat
  -- v4.33 `simp` no longer discharges the `native_zexp_total` sign guard.
  rw [if_neg (by omega : ¬ ((Nat.log2 n.toNat : Int) < 0))]
  have hn : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg (Int.le_of_lt hPos)
  rw [hn] at hCast
  exact_mod_cast hCast

private theorem native_int_lt_next_pow2_log2
    (n : native_Int) (hPos : 0 < n) :
    native_zlt n
      (native_int_pow2
        (native_zplus (native_int_log2 n) (native_zplus 1 0))) =
      true := by
  unfold native_zlt
  rw [decide_eq_true_eq]
  unfold native_int_pow2 native_int_log2 native_zplus native_zexp_total
  simp
  have hNat := (Nat.lt_log2_self (n := n.toNat))
  have hCast :
      ((n.toNat : Nat) : Int) <
        ((2 ^ (Nat.log2 n.toNat + 1) : Nat) : Int) := by
    exact_mod_cast hNat
  rw [if_neg (by omega : ¬ (((Nat.log2 n.toNat : Int) + 1) < 0))]
  have hn : ((n.toNat : Nat) : Int) = n := Int.toNat_of_nonneg (Int.le_of_lt hPos)
  rw [hn] at hCast
  exact_mod_cast hCast

private theorem native_int_log2_of_not_pos
    (n : native_Int) (hNotPos : ¬ 0 < n) :
    native_int_log2 n = 0 := by
  unfold native_int_log2
  have hle : n ≤ 0 := Int.le_of_not_gt hNotPos
  have hToNat : n.toNat = 0 := Int.toNat_eq_zero.mpr hle
  simp [hToNat, Nat.log2_zero]

private theorem native_div_total_lower_bound
    (a b : native_Int) (hNZ : b ≠ 0) :
    native_zleq
      (native_zmult b (native_zmult (native_div_total a b) 1)) a =
      true := by
  have hArith : b * (a / b) ≤ a := by
    let p := b * (a / b)
    let r := a % b
    have hModNonneg : 0 ≤ r := by
      simpa [r] using Int.emod_nonneg a (b := b) hNZ
    have hDecomp : p + r = a := by
      simpa [p, r] using Int.mul_ediv_add_emod a b
    unfold native_Int at *
    have hGoal : p ≤ a := by omega
    simpa [p] using hGoal
  unfold native_zleq
  rw [decide_eq_true_eq]
  simpa [native_zmult, native_div_total] using hArith

private theorem native_div_total_upper_bound_pos
    (a b : native_Int) (hPos : 0 < b) :
    native_zlt a
      (native_zmult b
        (native_zmult
          (native_zplus (native_div_total a b) (native_zplus 1 0)) 1)) =
      true := by
  have hArith : a < b * (a / b + 1) := by
    let p := b * (a / b)
    let r := a % b
    have hModLt : r < b := by
      simpa [r] using Int.emod_lt_of_pos a hPos
    have hDecomp : p + r = a := by
      simpa [p, r] using Int.mul_ediv_add_emod a b
    have hUpper : b * (a / b + 1) = p + b := by
      simp [p, Int.mul_add]
    unfold native_Int at *
    rw [hUpper]
    omega
  unfold native_zlt
  rw [decide_eq_true_eq]
  simpa [native_zmult, native_zplus, native_div_total] using hArith

private theorem native_div_total_upper_bound_neg
    (a b : native_Int) (hNeg : b < 0) :
    native_zlt a
      (native_zmult b
        (native_zmult
          (native_zplus (native_div_total a b) (native_zplus (-1) 0)) 1)) =
      true := by
  have hArith : a < b * (a / b + -1) := by
    let p := b * (a / b)
    let r := a % b
    have hModLt : r < -b := by
      simpa [r] using Int.emod_lt_of_neg a hNeg
    have hDecomp : p + r = a := by
      simpa [p, r] using Int.mul_ediv_add_emod a b
    have hUpper : b * (a / b + -1) = p + -b := by
      simp [p, Int.mul_add]
    unfold native_Int at *
    rw [hUpper]
    omega
  unfold native_zlt
  rw [decide_eq_true_eq]
  simpa [native_zmult, native_zplus, native_div_total] using hArith

private theorem native_mod_total_as_div_remainder
    (a b : native_Int) :
    native_mod_total a b =
      native_zplus a
        (native_zneg
          (native_zmult b (native_zmult (native_div_total a b) 1))) := by
  let p := b * (a / b)
  let r := a % b
  have hDecomp : p + r = a := by
    simpa [p, r] using Int.mul_ediv_add_emod a b
  have hArith : r = a + -p := by
    unfold native_Int at *
    omega
  unfold native_mod_total native_zplus native_zneg
  simpa [native_zmult, native_div_total, p, r] using hArith

private theorem eo_is_z_true_iff_numeral (t : Term) :
    __eo_is_z t = Term.Boolean true ↔ ∃ n, t = Term.Numeral n := by
  cases t <;> simp [__eo_is_z, __eo_is_z_internal, native_teq,
    native_and, native_not]

private theorem eo_is_z_eq_false_of_not_true
    (t : Term) (h : __eo_is_z t ≠ Term.Boolean true) :
    __eo_is_z t = Term.Boolean false := by
  cases t <;> simp [__eo_is_z, __eo_is_z_internal, native_teq,
    native_and, native_not] at *

private theorem arith_reduction_div_total_zero_eq_stuck (a : Term) :
    __arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) (Term.Numeral 0)) =
      Term.Stuck := by
  simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
    __eo_requires, __eo_is_z, __eo_is_z_internal, native_teq,
    native_ite, native_not, native_and]

private theorem arith_reduction_mod_total_zero_eq_stuck (a : Term) :
    __arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) (Term.Numeral 0)) =
      Term.Stuck := by
  simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
    __eo_requires, __eo_is_z, __eo_is_z_internal, native_teq,
    native_ite, native_not, native_and]

private theorem false_of_typeof_stuck_bool
    (h : __eo_typeof Term.Stuck = Term.Bool) : False := by
  have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by
    native_decide
  exact hBad h

private def smtDivTotalQuot (x y : SmtTerm) : SmtTerm :=
  SmtTerm._at_purify (SmtTerm.div_total x y)

private def smtDivTotalProd (x y : SmtTerm) : SmtTerm :=
  SmtTerm.mult y
    (SmtTerm.mult (smtDivTotalQuot x y) (SmtTerm.Numeral 1))

private def smtDivTotalUpper (x y : SmtTerm) (step : native_Int) : SmtTerm :=
  SmtTerm.mult y
    (SmtTerm.mult
      (SmtTerm.plus (smtDivTotalQuot x y)
        (SmtTerm.plus (SmtTerm.Numeral step) (SmtTerm.Numeral 0)))
      (SmtTerm.Numeral 1))

private def smtDivTotalBounds (x y : SmtTerm) (step : native_Int) : SmtTerm :=
  SmtTerm.and (SmtTerm.leq (smtDivTotalProd x y) x)
    (SmtTerm.and (SmtTerm.lt x (smtDivTotalUpper x y step))
      (SmtTerm.Boolean true))

private def smtDivTotalGenericSide (x y : SmtTerm) : SmtTerm :=
  SmtTerm.and
    (SmtTerm.and
      (SmtTerm.imp (SmtTerm.gt y (SmtTerm.Numeral 0))
        (smtDivTotalBounds x y 1))
      (SmtTerm.and
        (SmtTerm.imp (SmtTerm.lt y (SmtTerm.Numeral 0))
          (smtDivTotalBounds x y (-1)))
        (SmtTerm.Boolean true)))
    (SmtTerm.Boolean true)

private theorem smt_div_total_bounds_eval_eq
    (M : SmtModel) (x y : SmtTerm) (n1 n2 step : native_Int)
    (hEvalX : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hEvalY : __smtx_model_eval M y = SmtValue.Numeral n2) :
    __smtx_model_eval M (smtDivTotalBounds x y step) =
      SmtValue.Boolean
        (native_and
          (native_zleq
            (native_zmult n2 (native_zmult (native_div_total n1 n2) 1))
            n1)
          (native_and
            (native_zlt n1
              (native_zmult n2
                (native_zmult
                  (native_zplus (native_div_total n1 n2)
                    (native_zplus step 0))
                  1)))
            true)) := by
  simp [smtDivTotalBounds, smtDivTotalProd, smtDivTotalUpper,
    smtDivTotalQuot, __smtx_model_eval.eq_1, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_9, __smtx_model_eval.eq_13,
    __smtx_model_eval.eq_14, __smtx_model_eval.eq_16,
    __smtx_model_eval.eq_17, __smtx_model_eval.eq_18,
    __smtx_model_eval.eq_31, hEvalX, hEvalY,
    __smtx_model_eval__at_purify, __smtx_model_eval_div_total,
    __smtx_model_eval_plus, __smtx_model_eval_mult,
    __smtx_model_eval_lt, __smtx_model_eval_leq,
    __smtx_model_eval_and, native_zplus, native_and]

private theorem smt_div_total_generic_side_eval
    (M : SmtModel) (x y : SmtTerm) (n1 n2 : native_Int)
    (hEvalX : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hEvalY : __smtx_model_eval M y = SmtValue.Numeral n2) :
    __smtx_model_eval M (smtDivTotalGenericSide x y) =
      SmtValue.Boolean true := by
  have hBoundsPos := smt_div_total_bounds_eval_eq M x y n1 n2 1 hEvalX hEvalY
  have hBoundsNeg :=
    smt_div_total_bounds_eval_eq M x y n1 n2 (-1) hEvalX hEvalY
  by_cases hPos : 0 < n2
  · have hGt : native_zlt 0 n2 = true := by
      unfold native_zlt
      rw [decide_eq_true_eq]
      exact hPos
    have hLtFalse : native_zlt n2 0 = false := by
      unfold native_zlt
      rw [decide_eq_false_iff_not]
      unfold native_Int at *
      omega
    have hNZ : n2 ≠ 0 := by
      intro h0
      subst h0
      unfold native_Int at hPos
      omega
    have hLower := native_div_total_lower_bound n1 n2 hNZ
    have hUpper := native_div_total_upper_bound_pos n1 n2 hPos
    have hUpperS :
        native_zlt n1
          (native_zmult n2 (native_zmult (native_div_total n1 n2 + 1) 1)) =
          true := by
      simpa [native_zplus] using hUpper
    simp [smtDivTotalGenericSide, __smtx_model_eval.eq_1,
      __smtx_model_eval.eq_2, __smtx_model_eval.eq_9,
      __smtx_model_eval.eq_10, __smtx_model_eval.eq_17,
      __smtx_model_eval.eq_19, hEvalY, hGt, hLtFalse, hBoundsPos,
      hBoundsNeg, hLower, hUpperS, __smtx_model_eval_lt,
      __smtx_model_eval_gt, __smtx_model_eval_imp,
      __smtx_model_eval_or, __smtx_model_eval_not,
      __smtx_model_eval_and, native_zplus, native_not, native_or,
      native_and]
  · by_cases hNeg : n2 < 0
    · have hGtFalse : native_zlt 0 n2 = false := by
        unfold native_zlt
        rw [decide_eq_false_iff_not]
        exact hPos
      have hLt : native_zlt n2 0 = true := by
        unfold native_zlt
        rw [decide_eq_true_eq]
        exact hNeg
      have hNZ : n2 ≠ 0 := by
        intro h0
        subst h0
        unfold native_Int at hNeg
        omega
      have hLower := native_div_total_lower_bound n1 n2 hNZ
      have hUpper := native_div_total_upper_bound_neg n1 n2 hNeg
      have hUpperS :
          native_zlt n1
            (native_zmult n2
              (native_zmult (native_div_total n1 n2 + -1) 1)) =
            true := by
        simpa [native_zplus] using hUpper
      simp [smtDivTotalGenericSide, __smtx_model_eval.eq_1,
        __smtx_model_eval.eq_2, __smtx_model_eval.eq_9,
        __smtx_model_eval.eq_10, __smtx_model_eval.eq_17,
        __smtx_model_eval.eq_19, hEvalY, hGtFalse, hLt, hBoundsPos,
        hBoundsNeg, hLower, hUpperS, __smtx_model_eval_lt,
        __smtx_model_eval_gt, __smtx_model_eval_imp,
        __smtx_model_eval_or, __smtx_model_eval_not,
        __smtx_model_eval_and, native_zplus, native_not, native_or,
        native_and]
    · have hGtFalse : native_zlt 0 n2 = false := by
        unfold native_zlt
        rw [decide_eq_false_iff_not]
        exact hPos
      have hLtFalse : native_zlt n2 0 = false := by
        unfold native_zlt
        rw [decide_eq_false_iff_not]
        exact hNeg
      simp [smtDivTotalGenericSide, __smtx_model_eval.eq_1,
        __smtx_model_eval.eq_2, __smtx_model_eval.eq_9,
        __smtx_model_eval.eq_10, __smtx_model_eval.eq_17,
        __smtx_model_eval.eq_19, hEvalY, hGtFalse, hLtFalse,
        hBoundsPos, hBoundsNeg, __smtx_model_eval_lt,
        __smtx_model_eval_gt, __smtx_model_eval_imp,
        __smtx_model_eval_or, __smtx_model_eval_not,
        __smtx_model_eval_and, native_zplus, native_not, native_or,
        native_and]

private theorem smt_div_total_literal_side_eval_pos
    (M : SmtModel) (x : SmtTerm) (n1 n : native_Int)
    (hEvalX : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hPos : 0 < n) :
    __smtx_model_eval M
      (SmtTerm.and (smtDivTotalBounds x (SmtTerm.Numeral n) 1)
        (SmtTerm.Boolean true)) =
      SmtValue.Boolean true := by
  have hNZ : n ≠ 0 := by
    intro h0
    subst h0
    unfold native_Int at hPos
    omega
  have hBounds :=
    smt_div_total_bounds_eval_eq M x (SmtTerm.Numeral n) n1 n 1
      hEvalX (by simp [__smtx_model_eval.eq_2])
  have hLower := native_div_total_lower_bound n1 n hNZ
  have hUpper := native_div_total_upper_bound_pos n1 n hPos
  have hUpperS :
      native_zlt n1
        (native_zmult n (native_zmult (native_div_total n1 n + 1) 1)) =
        true := by
    simpa [native_zplus] using hUpper
  simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_9, hBounds,
    hLower, hUpperS, __smtx_model_eval_and, native_zplus, native_and]

private theorem smt_div_total_literal_side_eval_neg
    (M : SmtModel) (x : SmtTerm) (n1 n : native_Int)
    (hEvalX : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hNeg : n < 0) :
    __smtx_model_eval M
      (SmtTerm.and (smtDivTotalBounds x (SmtTerm.Numeral n) (-1))
        (SmtTerm.Boolean true)) =
      SmtValue.Boolean true := by
  have hNZ : n ≠ 0 := by
    intro h0
    subst h0
    unfold native_Int at hNeg
    omega
  have hBounds :=
    smt_div_total_bounds_eval_eq M x (SmtTerm.Numeral n) n1 n (-1)
      hEvalX (by simp [__smtx_model_eval.eq_2])
  have hLower := native_div_total_lower_bound n1 n hNZ
  have hUpper := native_div_total_upper_bound_neg n1 n hNeg
  have hUpperS :
      native_zlt n1
        (native_zmult n (native_zmult (native_div_total n1 n + -1) 1)) =
        true := by
    simpa [native_zplus] using hUpper
  simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_9, hBounds,
    hLower, hUpperS, __smtx_model_eval_and, native_zplus, native_and]

private theorem smt_div_total_eq_purify_eval
    (M : SmtModel) (x y : SmtTerm) (n1 n2 : native_Int)
    (hEvalX : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hEvalY : __smtx_model_eval M y = SmtValue.Numeral n2) :
    __smtx_model_eval M
      (SmtTerm.eq (SmtTerm.div_total x y)
        (SmtTerm._at_purify (SmtTerm.div_total x y))) =
      SmtValue.Boolean true := by
  simp [__smtx_model_eval.eq_13, __smtx_model_eval.eq_31,
    smtx_eval_eq_term_eq, hEvalX, hEvalY,
    __smtx_model_eval__at_purify, __smtx_model_eval_div_total,
    __smtx_model_eval_eq, native_veq]

private theorem smt_mod_total_eq_remainder_eval
    (M : SmtModel) (x y : SmtTerm) (n1 n2 : native_Int)
    (hEvalX : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hEvalY : __smtx_model_eval M y = SmtValue.Numeral n2) :
    __smtx_model_eval M
      (SmtTerm.eq (SmtTerm.mod_total x y)
        (SmtTerm.neg x (smtDivTotalProd x y))) =
      SmtValue.Boolean true := by
  have hMod := native_mod_total_as_div_remainder n1 n2
  simp [smtDivTotalProd, smtDivTotalQuot, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_13, __smtx_model_eval.eq_15,
    __smtx_model_eval.eq_16, __smtx_model_eval.eq_31,
    __smtx_model_eval.eq_32, smtx_eval_eq_term_eq, hEvalX,
    hEvalY, hMod, __smtx_model_eval__at_purify,
    __smtx_model_eval_div_total, __smtx_model_eval_mod_total,
    __smtx_model_eval_mult, __smtx_model_eval__, __smtx_model_eval_eq,
    native_zplus, native_zneg, native_zmult, native_veq]

private theorem typed_arith_reduction_is_int
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.is_int) u)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.is_int) u)) := by
  have hIsIntNN :
      term_has_non_none_type (SmtTerm.is_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) (Tout := SmtType.Bool)
      (typeof_is_int_eq (__eo_to_smt u)) hIsIntNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq
          (SmtTerm.is_int (__eo_to_smt u))
          (SmtTerm.eq (__eo_to_smt u)
            (SmtTerm.to_real
              (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
              (SmtTerm.neg (__eo_to_smt u)
                (SmtTerm.to_real
                  (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
            (SmtTerm.and
              (SmtTerm.lt
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                (SmtTerm.Rational (native_mk_rational 1 1)))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  rw [typeof_and_eq, typeof_eq_eq, typeof_is_int_eq, typeof_eq_eq,
    typeof_to_real_eq, __smtx_typeof.eq_13, typeof_to_int_eq,
    typeof_and_eq, typeof_and_eq, typeof_leq_eq, typeof_neg_eq,
    typeof_to_real_eq, __smtx_typeof.eq_13, typeof_to_int_eq,
    typeof_and_eq, typeof_lt_eq, typeof_neg_eq, typeof_to_real_eq,
    __smtx_typeof.eq_13, typeof_to_int_eq]
  simp [__smtx_typeof.eq_1, __smtx_typeof.eq_3, __smtx_typeof_eq,
    __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hUSmtTy]

private theorem typed_arith_reduction_to_int
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.to_int) u)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.to_int) u)) := by
  have hToIntNN :
      term_has_non_none_type (SmtTerm.to_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) (Tout := SmtType.Int)
      (typeof_to_int_eq (__eo_to_smt u)) hToIntNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq
          (SmtTerm.to_int (__eo_to_smt u))
          (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
              (SmtTerm.neg (__eo_to_smt u)
                (SmtTerm.to_real
                  (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
            (SmtTerm.and
              (SmtTerm.lt
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                (SmtTerm.Rational (native_mk_rational 1 1)))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  rw [typeof_and_eq, typeof_eq_eq, __smtx_typeof.eq_13, typeof_and_eq,
    typeof_and_eq, typeof_leq_eq, typeof_neg_eq, typeof_to_real_eq,
    __smtx_typeof.eq_13, typeof_to_int_eq, typeof_and_eq, typeof_lt_eq,
    typeof_neg_eq, typeof_to_real_eq, __smtx_typeof.eq_13,
    typeof_to_int_eq]
  simp [__smtx_typeof.eq_1, __smtx_typeof.eq_3, __smtx_typeof_eq,
    __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hUSmtTy]

private theorem typed_arith_reduction_qdiv
    (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) := by
  have hQdivNN :
      term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
      (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v))
            (SmtTerm.ite
              (SmtTerm.eq (__eo_to_smt v) (SmtTerm.Numeral 0))
              (SmtTerm.qdiv (SmtTerm.to_real (__eo_to_smt u))
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))) =
        SmtType.Bool
    rw [typeof_eq_eq, typeof_qdiv_eq, typeof_ite_eq, typeof_eq_eq,
      typeof_qdiv_eq, typeof_to_real_eq, __smtx_typeof.eq_3,
      typeof_qdiv_total_eq, __smtx_typeof.eq_2]
    simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
      __smtx_typeof_arith_overload_op_2_ret, native_ite, native_Teq,
      hArgs.1, hArgs.2]
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v))
            (SmtTerm.ite
              (SmtTerm.eq (__eo_to_smt v)
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.qdiv (__eo_to_smt u)
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))) =
        SmtType.Bool
    rw [typeof_eq_eq, typeof_qdiv_eq, typeof_ite_eq, typeof_eq_eq,
      __smtx_typeof.eq_3, typeof_qdiv_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof.eq_3,
      native_ite, native_Teq,
      hArgs.1, hArgs.2]

private theorem typed_arith_reduction_qdiv_total
    (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) := by
  have hQdivNN :
      term_has_non_none_type
        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total)
      (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    have hVToRealTy :
        __eo_typeof (Term.Apply (Term.UOp UserOp.to_real) v) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_to_real (__eo_typeof v) = Term.UOp UserOp.Real
      rw [hVEoTy]
      rfl
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
      __arith_mk_one, hVToRealTy]
    change
      __smtx_typeof
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
              (SmtTerm._at_purify
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
            (SmtTerm.and
              (SmtTerm.imp
                (SmtTerm.not
                  (SmtTerm.eq (SmtTerm.to_real (__eo_to_smt v))
                    (SmtTerm.Rational (native_mk_rational 0 1))))
                (SmtTerm.eq
                  (SmtTerm.mult (SmtTerm.to_real (__eo_to_smt v))
                    (SmtTerm.mult
                      (SmtTerm._at_purify
                        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                      (SmtTerm.Rational (native_mk_rational 1 1))))
                  (SmtTerm.to_real (__eo_to_smt u))))
              (SmtTerm.Boolean true))) =
        SmtType.Bool
    rw [typeof_and_eq, typeof_eq_eq, typeof_qdiv_total_eq,
      __smtx_typeof.eq_13, typeof_and_eq, typeof_imp_eq, typeof_not_eq,
      typeof_eq_eq, typeof_to_real_eq, __smtx_typeof.eq_3,
      typeof_eq_eq, typeof_mult_eq, typeof_to_real_eq, typeof_mult_eq,
      __smtx_typeof.eq_13, typeof_qdiv_total_eq, __smtx_typeof.eq_3,
      typeof_to_real_eq, __smtx_typeof.eq_1]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1, hArgs.2]
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hVTrans : RuleProofs.eo_has_smt_translation v := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.2]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    have hVNe : v ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
      __arith_mk_one]
    change
      __smtx_typeof
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
              (SmtTerm._at_purify
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
            (SmtTerm.and
              (SmtTerm.imp
                (SmtTerm.not
                  (SmtTerm.eq (__eo_to_smt v)
                    (SmtTerm.Rational (native_mk_rational 0 1))))
                (SmtTerm.eq
                  (SmtTerm.mult (__eo_to_smt v)
                    (SmtTerm.mult
                      (SmtTerm._at_purify
                        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                      (SmtTerm.Rational (native_mk_rational 1 1))))
                  (__eo_to_smt u)))
              (SmtTerm.Boolean true))) =
        SmtType.Bool
    rw [typeof_and_eq, typeof_eq_eq, typeof_qdiv_total_eq,
      __smtx_typeof.eq_13, typeof_and_eq, typeof_imp_eq, typeof_not_eq,
      typeof_eq_eq, __smtx_typeof.eq_3, typeof_eq_eq, typeof_mult_eq,
      typeof_mult_eq, __smtx_typeof.eq_13, typeof_qdiv_total_eq,
      __smtx_typeof.eq_3, __smtx_typeof.eq_1]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_div_total_literal
    (a : Term) (n : native_Int)
    (hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int)
    (hNZ : n ≠ 0) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a)
          (Term.Numeral n))) := by
  unfold RuleProofs.eo_has_bool_type
  have hNZ0 : ¬0 = n := by
    intro h
    exact hNZ h.symm
  by_cases hNeg : native_zlt n 0 = true
  · simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_teq, native_ite, native_not, native_and, hNZ0, hNeg]
    change
      __smtx_typeof
        (SmtTerm.and
          (SmtTerm.eq (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))
            (SmtTerm._at_purify
              (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq
                (SmtTerm.mult (SmtTerm.Numeral n)
                  (SmtTerm.mult
                    (SmtTerm._at_purify
                      (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                    (SmtTerm.Numeral 1)))
                (__eo_to_smt a))
              (SmtTerm.and
                (SmtTerm.lt (__eo_to_smt a)
                  (SmtTerm.mult (SmtTerm.Numeral n)
                    (SmtTerm.mult
                      (SmtTerm.plus
                        (SmtTerm._at_purify
                          (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                        (SmtTerm.plus (SmtTerm.Numeral (-1))
                          (SmtTerm.Numeral 0)))
                      (SmtTerm.Numeral 1))))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtType.Bool
    repeat
      first
      | rw [typeof_and_eq]
      | rw [typeof_eq_eq]
      | rw [typeof_lt_eq]
      | rw [typeof_leq_eq]
      | rw [typeof_mult_eq]
      | rw [typeof_plus_eq]
      | rw [typeof_div_total_eq]
      | rw [__smtx_typeof.eq_1]
      | rw [__smtx_typeof.eq_2]
      | rw [__smtx_typeof.eq_13]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1]
  · simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_teq, native_ite, native_not, native_and, hNZ0, hNeg]
    change
      __smtx_typeof
        (SmtTerm.and
          (SmtTerm.eq (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))
            (SmtTerm._at_purify
              (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq
                (SmtTerm.mult (SmtTerm.Numeral n)
                  (SmtTerm.mult
                    (SmtTerm._at_purify
                      (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                    (SmtTerm.Numeral 1)))
                (__eo_to_smt a))
              (SmtTerm.and
                (SmtTerm.lt (__eo_to_smt a)
                  (SmtTerm.mult (SmtTerm.Numeral n)
                    (SmtTerm.mult
                      (SmtTerm.plus
                        (SmtTerm._at_purify
                          (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                        (SmtTerm.plus (SmtTerm.Numeral 1)
                          (SmtTerm.Numeral 0)))
                      (SmtTerm.Numeral 1))))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtType.Bool
    repeat
      first
      | rw [typeof_and_eq]
      | rw [typeof_eq_eq]
      | rw [typeof_lt_eq]
      | rw [typeof_leq_eq]
      | rw [typeof_mult_eq]
      | rw [typeof_plus_eq]
      | rw [typeof_div_total_eq]
      | rw [__smtx_typeof.eq_1]
      | rw [__smtx_typeof.eq_2]
      | rw [__smtx_typeof.eq_13]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1]

private theorem typed_arith_reduction_div_total_generic
    (a b : Term)
    (hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int)
    (hIsZ : ¬__eo_is_z b = Term.Boolean true) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)) := by
  have hIsZFalse : __eo_is_z b = Term.Boolean false :=
    eo_is_z_eq_false_of_not_true b hIsZ
  unfold RuleProofs.eo_has_bool_type
  simp [__arith_reduction_pred, __eo_mk_apply, __eo_ite,hIsZFalse, native_teq, native_ite]
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b))
          (SmtTerm._at_purify
            (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.imp (SmtTerm.gt (__eo_to_smt b) (SmtTerm.Numeral 0))
              (SmtTerm.and
                (SmtTerm.leq
                  (SmtTerm.mult (__eo_to_smt b)
                    (SmtTerm.mult
                      (SmtTerm._at_purify
                        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                      (SmtTerm.Numeral 1)))
                  (__eo_to_smt a))
                (SmtTerm.and
                  (SmtTerm.lt (__eo_to_smt a)
                    (SmtTerm.mult (__eo_to_smt b)
                      (SmtTerm.mult
                        (SmtTerm.plus
                          (SmtTerm._at_purify
                            (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                          (SmtTerm.plus (SmtTerm.Numeral 1)
                            (SmtTerm.Numeral 0)))
                        (SmtTerm.Numeral 1))))
                  (SmtTerm.Boolean true))))
            (SmtTerm.and
              (SmtTerm.imp (SmtTerm.lt (__eo_to_smt b) (SmtTerm.Numeral 0))
                (SmtTerm.and
                  (SmtTerm.leq
                    (SmtTerm.mult (__eo_to_smt b)
                      (SmtTerm.mult
                        (SmtTerm._at_purify
                          (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                        (SmtTerm.Numeral 1)))
                    (__eo_to_smt a))
                  (SmtTerm.and
                    (SmtTerm.lt (__eo_to_smt a)
                      (SmtTerm.mult (__eo_to_smt b)
                        (SmtTerm.mult
                          (SmtTerm.plus
                            (SmtTerm._at_purify
                              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                            (SmtTerm.plus (SmtTerm.Numeral (-1))
                              (SmtTerm.Numeral 0)))
                          (SmtTerm.Numeral 1))))
                    (SmtTerm.Boolean true))))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  repeat
    first
    | rw [typeof_and_eq]
    | rw [typeof_eq_eq]
    | rw [typeof_imp_eq]
    | rw [typeof_gt_eq]
    | rw [typeof_lt_eq]
    | rw [typeof_leq_eq]
    | rw [typeof_mult_eq]
    | rw [typeof_plus_eq]
    | rw [typeof_div_total_eq]
    | rw [__smtx_typeof.eq_1]
    | rw [__smtx_typeof.eq_2]
    | rw [__smtx_typeof.eq_13]
  simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_div_total
    (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
    (hTy :
      __eo_typeof
        (__arith_reduction_pred
          (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)) := by
  have hDivNN :
      term_has_non_none_type
        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.div_total) (R := SmtType.Int)
      (typeof_div_total_eq (__eo_to_smt a) (__eo_to_smt b)) hDivNN
  by_cases hIsZ : __eo_is_z b = Term.Boolean true
  · rcases (eo_is_z_true_iff_numeral b).mp hIsZ with ⟨n, rfl⟩
    have hNZ : n ≠ 0 := by
      intro h0
      subst h0
      rw [arith_reduction_div_total_zero_eq_stuck a] at hTy
      cases hTy
    exact typed_arith_reduction_div_total_literal a n hArgs hNZ
  · exact typed_arith_reduction_div_total_generic a b hArgs hIsZ

private theorem typed_arith_reduction_mod_total_literal
    (a : Term) (n : native_Int)
    (hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int)
    (hNZ : n ≠ 0) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a)
          (Term.Numeral n))) := by
  unfold RuleProofs.eo_has_bool_type
  have hNZ0 : ¬0 = n := by
    intro h
    exact hNZ h.symm
  by_cases hNeg : native_zlt n 0 = true
  · simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_teq, native_ite, native_not, native_and, hNZ0, hNeg]
    change
      __smtx_typeof
        (SmtTerm.and
          (SmtTerm.eq (SmtTerm.mod_total (__eo_to_smt a) (SmtTerm.Numeral n))
            (SmtTerm.neg (__eo_to_smt a)
              (SmtTerm.mult (SmtTerm.Numeral n)
                (SmtTerm.mult
                  (SmtTerm._at_purify
                    (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                  (SmtTerm.Numeral 1)))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq
                (SmtTerm.mult (SmtTerm.Numeral n)
                  (SmtTerm.mult
                    (SmtTerm._at_purify
                      (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                    (SmtTerm.Numeral 1)))
                (__eo_to_smt a))
              (SmtTerm.and
                (SmtTerm.lt (__eo_to_smt a)
                  (SmtTerm.mult (SmtTerm.Numeral n)
                    (SmtTerm.mult
                      (SmtTerm.plus
                        (SmtTerm._at_purify
                          (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                        (SmtTerm.plus (SmtTerm.Numeral (-1))
                          (SmtTerm.Numeral 0)))
                      (SmtTerm.Numeral 1))))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtType.Bool
    repeat
      first
      | rw [typeof_and_eq]
      | rw [typeof_eq_eq]
      | rw [typeof_lt_eq]
      | rw [typeof_leq_eq]
      | rw [typeof_neg_eq]
      | rw [typeof_mult_eq]
      | rw [typeof_plus_eq]
      | rw [typeof_div_total_eq]
      | rw [typeof_mod_total_eq]
      | rw [__smtx_typeof.eq_1]
      | rw [__smtx_typeof.eq_2]
      | rw [__smtx_typeof.eq_13]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1]
  · simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_teq, native_ite, native_not, native_and, hNZ0, hNeg]
    change
      __smtx_typeof
        (SmtTerm.and
          (SmtTerm.eq (SmtTerm.mod_total (__eo_to_smt a) (SmtTerm.Numeral n))
            (SmtTerm.neg (__eo_to_smt a)
              (SmtTerm.mult (SmtTerm.Numeral n)
                (SmtTerm.mult
                  (SmtTerm._at_purify
                    (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                  (SmtTerm.Numeral 1)))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq
                (SmtTerm.mult (SmtTerm.Numeral n)
                  (SmtTerm.mult
                    (SmtTerm._at_purify
                      (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                    (SmtTerm.Numeral 1)))
                (__eo_to_smt a))
              (SmtTerm.and
                (SmtTerm.lt (__eo_to_smt a)
                  (SmtTerm.mult (SmtTerm.Numeral n)
                    (SmtTerm.mult
                      (SmtTerm.plus
                        (SmtTerm._at_purify
                          (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n)))
                        (SmtTerm.plus (SmtTerm.Numeral 1)
                          (SmtTerm.Numeral 0)))
                      (SmtTerm.Numeral 1))))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtType.Bool
    repeat
      first
      | rw [typeof_and_eq]
      | rw [typeof_eq_eq]
      | rw [typeof_lt_eq]
      | rw [typeof_leq_eq]
      | rw [typeof_neg_eq]
      | rw [typeof_mult_eq]
      | rw [typeof_plus_eq]
      | rw [typeof_div_total_eq]
      | rw [typeof_mod_total_eq]
      | rw [__smtx_typeof.eq_1]
      | rw [__smtx_typeof.eq_2]
      | rw [__smtx_typeof.eq_13]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1]

private theorem typed_arith_reduction_mod_total_generic
    (a b : Term)
    (hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int)
    (hIsZ : ¬__eo_is_z b = Term.Boolean true) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)) := by
  have hIsZFalse : __eo_is_z b = Term.Boolean false :=
    eo_is_z_eq_false_of_not_true b hIsZ
  unfold RuleProofs.eo_has_bool_type
  simp [__arith_reduction_pred, __eo_mk_apply, __eo_ite,hIsZFalse, native_teq, native_ite]
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b))
          (SmtTerm.neg (__eo_to_smt a)
            (SmtTerm.mult (__eo_to_smt b)
              (SmtTerm.mult
                (SmtTerm._at_purify
                  (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                (SmtTerm.Numeral 1)))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.imp (SmtTerm.gt (__eo_to_smt b) (SmtTerm.Numeral 0))
              (SmtTerm.and
                (SmtTerm.leq
                  (SmtTerm.mult (__eo_to_smt b)
                    (SmtTerm.mult
                      (SmtTerm._at_purify
                        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                      (SmtTerm.Numeral 1)))
                  (__eo_to_smt a))
                (SmtTerm.and
                  (SmtTerm.lt (__eo_to_smt a)
                    (SmtTerm.mult (__eo_to_smt b)
                      (SmtTerm.mult
                        (SmtTerm.plus
                          (SmtTerm._at_purify
                            (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                          (SmtTerm.plus (SmtTerm.Numeral 1)
                            (SmtTerm.Numeral 0)))
                        (SmtTerm.Numeral 1))))
                  (SmtTerm.Boolean true))))
            (SmtTerm.and
              (SmtTerm.imp (SmtTerm.lt (__eo_to_smt b) (SmtTerm.Numeral 0))
                (SmtTerm.and
                  (SmtTerm.leq
                    (SmtTerm.mult (__eo_to_smt b)
                      (SmtTerm.mult
                        (SmtTerm._at_purify
                          (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                        (SmtTerm.Numeral 1)))
                    (__eo_to_smt a))
                  (SmtTerm.and
                    (SmtTerm.lt (__eo_to_smt a)
                      (SmtTerm.mult (__eo_to_smt b)
                        (SmtTerm.mult
                          (SmtTerm.plus
                            (SmtTerm._at_purify
                              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))
                            (SmtTerm.plus (SmtTerm.Numeral (-1))
                              (SmtTerm.Numeral 0)))
                          (SmtTerm.Numeral 1))))
                    (SmtTerm.Boolean true))))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  repeat
    first
    | rw [typeof_and_eq]
    | rw [typeof_eq_eq]
    | rw [typeof_imp_eq]
    | rw [typeof_gt_eq]
    | rw [typeof_lt_eq]
    | rw [typeof_leq_eq]
    | rw [typeof_neg_eq]
    | rw [typeof_mult_eq]
    | rw [typeof_plus_eq]
    | rw [typeof_div_total_eq]
    | rw [typeof_mod_total_eq]
    | rw [__smtx_typeof.eq_1]
    | rw [__smtx_typeof.eq_2]
    | rw [__smtx_typeof.eq_13]
  simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_mod_total
    (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
    (hTy :
      __eo_typeof
        (__arith_reduction_pred
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)) := by
  have hModNN :
      term_has_non_none_type
        (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.mod_total) (R := SmtType.Int)
      (typeof_mod_total_eq (__eo_to_smt a) (__eo_to_smt b)) hModNN
  by_cases hIsZ : __eo_is_z b = Term.Boolean true
  · rcases (eo_is_z_true_iff_numeral b).mp hIsZ with ⟨n, rfl⟩
    have hNZ : n ≠ 0 := by
      intro h0
      subst h0
      rw [arith_reduction_mod_total_zero_eq_stuck a] at hTy
      cases hTy
    exact typed_arith_reduction_mod_total_literal a n hArgs hNZ
  · exact typed_arith_reduction_mod_total_generic a b hArgs hIsZ

private theorem typed_arith_reduction_div
    (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))) := by
  have hDivNN :
      term_has_non_none_type (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int)
      (typeof_div_eq (__eo_to_smt a) (__eo_to_smt b)) hDivNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b))
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
            (SmtTerm.div (__eo_to_smt a) (SmtTerm.Numeral 0))
            (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))) =
      SmtType.Bool
  rw [typeof_eq_eq, typeof_div_eq, typeof_ite_eq, typeof_eq_eq,
    typeof_div_eq, typeof_div_total_eq]
  rw [__smtx_typeof.eq_2]
  simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
    native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_mod
    (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))) := by
  have hModNN :
      term_has_non_none_type (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt a) (__eo_to_smt b)) hModNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b))
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
            (SmtTerm.mod (__eo_to_smt a) (SmtTerm.Numeral 0))
            (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)))) =
      SmtType.Bool
  rw [typeof_eq_eq, typeof_mod_eq, typeof_ite_eq, typeof_eq_eq,
    typeof_mod_eq, typeof_mod_total_eq]
  rw [__smtx_typeof.eq_2]
  simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
    native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_abs
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.abs) u)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.abs) u))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt) u)
                (__arith_mk_zero (__eo_typeof u))))
            (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
          u)) := by
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_reduction_abs_arg_cases u hAbsNN with hInt | hReal
  ·
      rcases hInt with ⟨hUSmtTy, _hUEoTy, hZero⟩
      unfold RuleProofs.eo_has_bool_type
      change
        __smtx_typeof
            (SmtTerm.eq
              (SmtTerm.abs (__eo_to_smt u))
              (SmtTerm.ite
                (SmtTerm.lt (__eo_to_smt u)
                  (__eo_to_smt (__arith_mk_zero (__eo_typeof u))))
                (SmtTerm.uneg (__eo_to_smt u))
                (__eo_to_smt u))) =
          SmtType.Bool
      rw [hZero]
      rw [typeof_eq_eq, typeof_abs_eq, typeof_ite_eq, typeof_lt_eq, typeof_uneg_eq]
      rw [__smtx_typeof.eq_2]
      simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
        __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2_ret,
        native_ite, native_Teq, hUSmtTy]
  ·
      rcases hReal with ⟨hUSmtTy, _hUEoTy, hZero⟩
      unfold RuleProofs.eo_has_bool_type
      change
        __smtx_typeof
            (SmtTerm.eq
              (SmtTerm.abs (__eo_to_smt u))
              (SmtTerm.ite
                (SmtTerm.lt (__eo_to_smt u)
                  (__eo_to_smt (__arith_mk_zero (__eo_typeof u))))
                (SmtTerm.uneg (__eo_to_smt u))
                (__eo_to_smt u))) =
          SmtType.Bool
      rw [hZero]
      rw [typeof_eq_eq, typeof_abs_eq, typeof_ite_eq, typeof_lt_eq, typeof_uneg_eq]
      rw [__smtx_typeof.eq_3]
      simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
        __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2_ret,
        native_ite, native_Teq, hUSmtTy]

private theorem typed_arith_reduction_int_log2
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.int_log2) u)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.int_log2) u)) := by
  have hLogNN :
      term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2)
      (typeof_int_log2_eq (__eo_to_smt u)) hLogNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq
          (SmtTerm.int_log2 (__eo_to_smt u))
          (SmtTerm._at_purify (SmtTerm.int_log2 (__eo_to_smt u))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.imp
              (SmtTerm.lt (SmtTerm.Numeral 0) (__eo_to_smt u))
              (SmtTerm.and
                (SmtTerm.leq
                  (SmtTerm.int_pow2
                    (SmtTerm._at_purify (SmtTerm.int_log2 (__eo_to_smt u))))
                  (__eo_to_smt u))
                (SmtTerm.and
                  (SmtTerm.lt (__eo_to_smt u)
                    (SmtTerm.int_pow2
                      (SmtTerm.plus
                        (SmtTerm._at_purify
                          (SmtTerm.int_log2 (__eo_to_smt u)))
                        (SmtTerm.plus (SmtTerm.Numeral 1)
                          (SmtTerm.Numeral 0)))))
                  (SmtTerm.Boolean true))))
            (SmtTerm.and
              (SmtTerm.imp
                (SmtTerm.not
                  (SmtTerm.lt (SmtTerm.Numeral 0) (__eo_to_smt u)))
                (SmtTerm.eq
                  (SmtTerm._at_purify (SmtTerm.int_log2 (__eo_to_smt u)))
                  (SmtTerm.Numeral 0)))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  repeat
    first
    | rw [typeof_and_eq]
    | rw [typeof_eq_eq]
    | rw [typeof_imp_eq]
    | rw [typeof_not_eq]
    | rw [typeof_lt_eq]
    | rw [typeof_leq_eq]
    | rw [typeof_int_pow2_eq]
    | rw [typeof_plus_eq]
    | rw [typeof_int_log2_eq]
    | rw [__smtx_typeof.eq_13]
    | rw [__smtx_typeof.eq_2]
    | rw [__smtx_typeof.eq_1]
  simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hUSmtTy]

private theorem typed_arith_reduction_abs_of_trans
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.abs) u)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u)) := by
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_reduction_abs_arg_cases u hAbsNN with hInt | hReal
  ·
      rcases hInt with ⟨hUSmtTy, hUEoTy, _hZero⟩
      have hUTrans : RuleProofs.eo_has_smt_translation u := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hUSmtTy]
        simp
      have hUNe : u ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
      have hPred :
          __arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u) =
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) u))
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.ite)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.lt) u)
                      (__arith_mk_zero (__eo_typeof u))))
                  (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
                u)) := by
        simp [__arith_reduction_pred, __eo_mk_apply, hUEoTy,
          __arith_mk_zero]
      rw [hPred]
      exact typed_arith_reduction_abs u hTrans
  ·
      rcases hReal with ⟨hUSmtTy, hUEoTy, _hZero⟩
      have hUTrans : RuleProofs.eo_has_smt_translation u := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hUSmtTy]
        simp
      have hUNe : u ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
      have hPred :
          __arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u) =
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) u))
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.ite)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.lt) u)
                      (__arith_mk_zero (__eo_typeof u))))
                  (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
                u)) := by
        simp [__arith_reduction_pred, __eo_mk_apply, hUEoTy,
          __arith_mk_zero]
      rw [hPred]
      exact typed_arith_reduction_abs u hTrans

private theorem typed_arith_reduction_of_trans
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof (__arith_reduction_pred t) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__arith_reduction_pred t) := by
  cases t with
  | Apply f x =>
      cases f with
      | UOp op =>
          by_cases hIsInt : op = UserOp.is_int
          · subst op
            exact typed_arith_reduction_is_int x hTrans
          · by_cases hToInt : op = UserOp.to_int
            · subst op
              exact typed_arith_reduction_to_int x hTrans
            · by_cases hAbs : op = UserOp.abs
              · subst op
                exact typed_arith_reduction_abs_of_trans x hTrans
              · by_cases hLog : op = UserOp.int_log2
                · subst op
                  exact typed_arith_reduction_int_log2 x hTrans
                · simp [__arith_reduction_pred, hIsInt, hToInt, hAbs, hLog] at hTy
                  exact False.elim (false_of_typeof_stuck_bool hTy)
      | Apply g u =>
          cases g with
          | UOp op =>
              by_cases hQdiv : op = UserOp.qdiv
              · subst op
                exact typed_arith_reduction_qdiv u x hTrans
              · by_cases hDiv : op = UserOp.div
                · subst op
                  simpa [__arith_reduction_pred] using
                    typed_arith_reduction_div u x hTrans
                · by_cases hMod : op = UserOp.mod
                  · subst op
                    simpa [__arith_reduction_pred] using
                      typed_arith_reduction_mod u x hTrans
                  · by_cases hQdivTotal : op = UserOp.qdiv_total
                    · subst op
                      exact typed_arith_reduction_qdiv_total u x hTrans
                    · by_cases hDivTotal : op = UserOp.div_total
                      · subst op
                        exact typed_arith_reduction_div_total u x hTrans hTy
                      · by_cases hModTotal : op = UserOp.mod_total
                        · subst op
                          exact typed_arith_reduction_mod_total u x hTrans hTy
                        · simp [__arith_reduction_pred, hQdiv, hDiv, hMod,
                            hQdivTotal, hDivTotal, hModTotal] at hTy
                          exact False.elim (false_of_typeof_stuck_bool hTy)
          | _ =>
              simp [__arith_reduction_pred] at hTy
              exact False.elim (false_of_typeof_stuck_bool hTy)
      | _ =>
          simp [__arith_reduction_pred] at hTy
          exact False.elim (false_of_typeof_stuck_bool hTy)
  | _ =>
      simp [__arith_reduction_pred] at hTy
      exact False.elim (false_of_typeof_stuck_bool hTy)

private theorem facts_arith_reduction_is_int
    (M : SmtModel) (hM : model_wf M) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.is_int) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.is_int) u))
      true := by
  have hBool := typed_arith_reduction_is_int u hTrans
  have hIsIntNN :
      term_has_non_none_type (SmtTerm.is_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) (Tout := SmtType.Bool)
      (typeof_is_int_eq (__eo_to_smt u)) hIsIntNN
  have hEvalUTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real hUSmtTy
      (by simp) type_inhabited_real
  rcases real_value_canonical hEvalUTy with ⟨q, hEvalU⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · change
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.eq
            (SmtTerm.is_int (__eo_to_smt u))
            (SmtTerm.eq (__eo_to_smt u)
              (SmtTerm.to_real
                (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
              (SmtTerm.and
                (SmtTerm.lt
                  (SmtTerm.neg (__eo_to_smt u)
                    (SmtTerm.to_real
                      (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                  (SmtTerm.Rational (native_mk_rational 1 1)))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtValue.Boolean true
    simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
      __smtx_model_eval.eq_9, __smtx_model_eval.eq_13,
      __smtx_model_eval.eq_15, __smtx_model_eval.eq_17,
      __smtx_model_eval.eq_18, __smtx_model_eval.eq_21,
      __smtx_model_eval.eq_22, __smtx_model_eval.eq_23,
      smtx_eval_eq_term_eq, hEvalU, __smtx_model_eval__at_purify,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_is_int, __smtx_model_eval_eq,
      __smtx_model_eval__, __smtx_model_eval_leq, __smtx_model_eval_lt,
      __smtx_model_eval_and, native_veq, native_floor_remainder_nonneg,
      native_floor_remainder_lt_one, native_and, eq_comm]

private theorem facts_arith_reduction_to_int
    (M : SmtModel) (hM : model_wf M) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.to_int) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.to_int) u))
      true := by
  have hBool := typed_arith_reduction_to_int u hTrans
  have hToIntNN :
      term_has_non_none_type (SmtTerm.to_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) (Tout := SmtType.Int)
      (typeof_to_int_eq (__eo_to_smt u)) hToIntNN
  have hEvalUTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real hUSmtTy
      (by simp) type_inhabited_real
  rcases real_value_canonical hEvalUTy with ⟨q, hEvalU⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · change
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.eq
            (SmtTerm.to_int (__eo_to_smt u))
            (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
              (SmtTerm.and
                (SmtTerm.lt
                  (SmtTerm.neg (__eo_to_smt u)
                    (SmtTerm.to_real
                      (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                  (SmtTerm.Rational (native_mk_rational 1 1)))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtValue.Boolean true
    simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
      __smtx_model_eval.eq_9, __smtx_model_eval.eq_13,
      __smtx_model_eval.eq_15, __smtx_model_eval.eq_17,
      __smtx_model_eval.eq_18, __smtx_model_eval.eq_21,
      __smtx_model_eval.eq_22, smtx_eval_eq_term_eq,
      hEvalU, __smtx_model_eval__at_purify,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_eq, __smtx_model_eval__,
      __smtx_model_eval_leq, __smtx_model_eval_lt, __smtx_model_eval_and,
      native_veq, native_floor_remainder_nonneg,
      native_floor_remainder_lt_one, native_and]

private theorem facts_arith_reduction_qdiv
    (M : SmtModel) (hM : model_wf M) (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
      true := by
  have hBool := typed_arith_reduction_qdiv u v hTrans
  have hQdivNN :
      term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
      (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Int :=
      smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Int
        hArgs.1 (by simp) type_inhabited_int
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Int :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Int
        hArgs.2 (by simp) type_inhabited_int
    rcases int_value_canonical hEvalUTy with ⟨n1, hEvalU⟩
    rcases int_value_canonical hEvalVTy with ⟨n2, hEvalV⟩
    have hPred :
        __arith_reduction_pred
            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v) =
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
                    (Term.Numeral 0)))
                (Term.Apply (Term.UOp UserOp._at_div_by_zero)
                  (Term.Apply (Term.UOp UserOp.to_real) u)))
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) := by
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    rw [hPred]
    apply RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
              (Term.Numeral 0)))
          (Term.Apply (Term.UOp UserOp._at_div_by_zero)
            (Term.Apply (Term.UOp UserOp.to_real) u)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
    · simpa [hPred] using hBool
    · change RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)))
        (__smtx_model_eval M
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt v) (SmtTerm.Numeral 0))
            (SmtTerm.qdiv (SmtTerm.to_real (__eo_to_smt u))
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
      exact smt_qdiv_eval_reduction_int_term_rel M
        (__eo_to_smt u) (__eo_to_smt v) n1 n2 hEvalU hEvalV
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Real :=
      smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real
        hArgs.1 (by simp) type_inhabited_real
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Real :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Real
        hArgs.2 (by simp) type_inhabited_real
    rcases real_value_canonical hEvalUTy with ⟨q1, hEvalU⟩
    rcases real_value_canonical hEvalVTy with ⟨q2, hEvalV⟩
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    have hPred :
        __arith_reduction_pred
            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v) =
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
                    (Term.Rational (native_mk_rational 0 1))))
                (Term.Apply (Term.UOp UserOp._at_div_by_zero) u))
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) := by
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    rw [hPred]
    apply RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
              (Term.Rational (native_mk_rational 0 1))))
          (Term.Apply (Term.UOp UserOp._at_div_by_zero) u))
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
    · simpa [hPred] using hBool
    · change RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)))
        (__smtx_model_eval M
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt v)
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.qdiv (__eo_to_smt u)
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
      exact smt_qdiv_eval_reduction_real_term_rel M
        (__eo_to_smt u) (__eo_to_smt v) q1 q2 hEvalU hEvalV

private theorem facts_arith_reduction_qdiv_total
    (M : SmtModel) (hM : model_wf M) (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
      true := by
  have hBool := typed_arith_reduction_qdiv_total u v hTrans
  have hQdivNN :
      term_has_non_none_type
        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total)
      (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Int := by
      exact smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Int
        hArgs.1 (by simp) type_inhabited_int
    have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    have hVToRealTy :
        __eo_typeof (Term.Apply (Term.UOp UserOp.to_real) v) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_to_real (__eo_typeof v) = Term.UOp UserOp.Real
      rw [hVEoTy]
      rfl
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Int :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Int
        hArgs.2 (by simp) type_inhabited_int
    rcases int_value_canonical hEvalUTy with ⟨n1, hEvalU⟩
    rcases int_value_canonical hEvalVTy with ⟨n2, hEvalV⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M _ ?_ ?_
    · simpa [RuleProofs.eo_has_bool_type] using hBool
    · change
        __smtx_model_eval M (__eo_to_smt
            (__arith_reduction_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) =
          SmtValue.Boolean true
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
        __arith_mk_one, hVToRealTy]
      change
        __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
                (SmtTerm._at_purify
                  (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
              (SmtTerm.and
                (SmtTerm.imp
                  (SmtTerm.not
                    (SmtTerm.eq (SmtTerm.to_real (__eo_to_smt v))
                      (SmtTerm.Rational (native_mk_rational 0 1))))
                  (SmtTerm.eq
                    (SmtTerm.mult (SmtTerm.to_real (__eo_to_smt v))
                      (SmtTerm.mult
                        (SmtTerm._at_purify
                          (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                        (SmtTerm.Rational (native_mk_rational 1 1))))
                    (SmtTerm.to_real (__eo_to_smt u))))
                (SmtTerm.Boolean true))) =
          SmtValue.Boolean true
      by_cases hZero : n2 = 0
      · simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_7, __smtx_model_eval.eq_9,
          __smtx_model_eval.eq_10, __smtx_model_eval.eq_13,
          __smtx_model_eval.eq_16, __smtx_model_eval.eq_21,
          smtx_eval_qdiv_total_term_eq, smtx_eval_eq_term_eq,
          hEvalU, hEvalV, hZero, __smtx_model_eval__at_purify,
          __smtx_model_eval_to_real, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and, native_to_real_eq_zero_iff]
      · have hCancel :
          native_qmult (native_to_real n2)
            (native_qmult (native_mk_rational n1 n2)
              (native_mk_rational 1 1)) =
            native_to_real n1 :=
          native_to_real_qmult_mk_rational_cancel n1 n2 hZero
        simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_7, __smtx_model_eval.eq_9,
          __smtx_model_eval.eq_10, __smtx_model_eval.eq_13,
          __smtx_model_eval.eq_16, __smtx_model_eval.eq_21,
          smtx_eval_qdiv_total_term_eq, smtx_eval_eq_term_eq,
          hEvalU, hEvalV, hZero, hCancel, __smtx_model_eval__at_purify,
          __smtx_model_eval_to_real, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and, native_to_real_eq_zero_iff]
  · have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Real := by
      exact smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real
        hArgs.1 (by simp) type_inhabited_real
    have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hVTrans : RuleProofs.eo_has_smt_translation v := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.2]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    have hVNe : v ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Real :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Real
        hArgs.2 (by simp) type_inhabited_real
    rcases real_value_canonical hEvalUTy with ⟨q1, hEvalU⟩
    rcases real_value_canonical hEvalVTy with ⟨q2, hEvalV⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M _ ?_ ?_
    · simpa [RuleProofs.eo_has_bool_type] using hBool
    · change
        __smtx_model_eval M (__eo_to_smt
            (__arith_reduction_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) =
          SmtValue.Boolean true
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
        __arith_mk_one]
      change
        __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
                (SmtTerm._at_purify
                  (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
              (SmtTerm.and
                (SmtTerm.imp
                  (SmtTerm.not
                    (SmtTerm.eq (__eo_to_smt v)
                      (SmtTerm.Rational (native_mk_rational 0 1))))
                  (SmtTerm.eq
                    (SmtTerm.mult (__eo_to_smt v)
                      (SmtTerm.mult
                        (SmtTerm._at_purify
                          (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                        (SmtTerm.Rational (native_mk_rational 1 1))))
                    (__eo_to_smt u)))
                (SmtTerm.Boolean true))) =
          SmtValue.Boolean true
      by_cases hZero : q2 = native_mk_rational 0 1
      · simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_7, __smtx_model_eval.eq_9,
          __smtx_model_eval.eq_10, __smtx_model_eval.eq_13,
          __smtx_model_eval.eq_16, smtx_eval_qdiv_total_term_eq,
          smtx_eval_eq_term_eq, hEvalU, hEvalV, hZero,
          __smtx_model_eval__at_purify, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and]
      · have hNZ : q2 ≠ 0 := by
          intro hQ2
          apply hZero
          rw [hQ2]
          unfold native_mk_rational
          simp [rat_div_one]
        have hCancel :
            native_qmult q2
              (native_qmult (native_qdiv_total q1 q2)
                (native_mk_rational 1 1)) =
              q1 :=
          native_qmult_qdiv_total_cancel q1 q2 hNZ
        simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_7, __smtx_model_eval.eq_9,
          __smtx_model_eval.eq_10, __smtx_model_eval.eq_13,
          __smtx_model_eval.eq_16, smtx_eval_qdiv_total_term_eq,
          smtx_eval_eq_term_eq, hEvalU, hEvalV, hZero, hCancel,
          __smtx_model_eval__at_purify, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and]

private theorem facts_arith_reduction_div
    (M : SmtModel) (a b : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
              (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
            (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
        (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
          (SmtTerm.div (__eo_to_smt a) (SmtTerm.Numeral 0))
          (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b))))
    exact smt_div_eval_reduction_term_rel M (__eo_to_smt a) (__eo_to_smt b)

private theorem facts_arith_reduction_mod
    (M : SmtModel) (a b : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
              (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
        (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
          (SmtTerm.mod (__eo_to_smt a) (SmtTerm.Numeral 0))
          (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b))))
    exact smt_mod_eval_reduction_term_rel M (__eo_to_smt a) (__eo_to_smt b)

private theorem facts_arith_reduction_abs
    (M : SmtModel) (hM : model_wf M) (u : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.abs) u))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.lt) u)
                  (__arith_mk_zero (__eo_typeof u))))
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
            u))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.abs) u))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt) u)
                (__arith_mk_zero (__eo_typeof u))))
            (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
          u))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.UOp UserOp.abs) u)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.lt) u)
            (__arith_mk_zero (__eo_typeof u))))
        (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
      u)
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs (__eo_to_smt u)))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.lt (__eo_to_smt u) (__eo_to_smt (__arith_mk_zero (__eo_typeof u))))
          (SmtTerm.uneg (__eo_to_smt u))
          (__eo_to_smt u)))
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.UOp UserOp.abs) u)
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.lt) u)
              (__arith_mk_zero (__eo_typeof u))))
          (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
        u)
      hBool with ⟨_hSame, hAbsNonNone⟩
    have hAbsNN :
        term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
      unfold term_has_non_none_type
      exact hAbsNonNone
    rcases arith_reduction_abs_arg_cases u hAbsNN with hInt | hReal
    ·
        rcases hInt with ⟨hUSmtTy, _hUEoTy, hZero⟩
        have hEvalUTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
              SmtType.Int :=
          smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Int
            hUSmtTy (by simp) type_inhabited_int
        rcases int_value_canonical hEvalUTy with ⟨n, hEvalU⟩
        rw [hZero]
        exact smt_abs_eval_reduction_int_term_rel M (__eo_to_smt u) n hEvalU
    ·
        rcases hReal with ⟨hUSmtTy, _hUEoTy, hZero⟩
        have hEvalUTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
              SmtType.Real :=
          smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real
            hUSmtTy (by simp) type_inhabited_real
        rcases real_value_canonical hEvalUTy with ⟨q, hEvalU⟩
        rw [hZero]
        exact smt_abs_eval_reduction_real_term_rel M (__eo_to_smt u) q hEvalU

private theorem facts_arith_reduction_abs_from_trans
    (M : SmtModel) (hM : model_wf M) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.abs) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u))
      true := by
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  rcases arith_reduction_abs_arg_cases u hAbsNN with hInt | hReal
  ·
      rcases hInt with ⟨hUSmtTy, hUEoTy, _hZero⟩
      have hUTrans : RuleProofs.eo_has_smt_translation u := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hUSmtTy]
        simp
      have hUNe : u ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
      have hPred :
          __arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u) =
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) u))
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.ite)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.lt) u)
                      (__arith_mk_zero (__eo_typeof u))))
                  (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
                u)) := by
        simp [__arith_reduction_pred, __eo_mk_apply, hUEoTy,
          __arith_mk_zero]
      rw [hPred]
      exact facts_arith_reduction_abs M hM u
        (typed_arith_reduction_abs u hTrans)
  ·
      rcases hReal with ⟨hUSmtTy, hUEoTy, _hZero⟩
      have hUTrans : RuleProofs.eo_has_smt_translation u := by
        unfold RuleProofs.eo_has_smt_translation
        rw [hUSmtTy]
        simp
      have hUNe : u ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
      have hPred :
          __arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u) =
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.abs) u))
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.ite)
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.lt) u)
                      (__arith_mk_zero (__eo_typeof u))))
                  (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
                u)) := by
        simp [__arith_reduction_pred, __eo_mk_apply, hUEoTy,
          __arith_mk_zero]
      rw [hPred]
      exact facts_arith_reduction_abs M hM u
        (typed_arith_reduction_abs u hTrans)

private theorem facts_arith_reduction_int_log2
    (M : SmtModel) (hM : model_wf M) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.int_log2) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.int_log2) u))
      true := by
  have hBool := typed_arith_reduction_int_log2 u hTrans
  have hLogNN :
      term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2)
      (typeof_int_log2_eq (__eo_to_smt u)) hLogNN
  have hEvalUTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Int
      hUSmtTy (by simp) type_inhabited_int
  rcases int_value_canonical hEvalUTy with ⟨n, hEvalU⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · change
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.eq
            (SmtTerm.int_log2 (__eo_to_smt u))
            (SmtTerm._at_purify (SmtTerm.int_log2 (__eo_to_smt u))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.imp
                (SmtTerm.lt (SmtTerm.Numeral 0) (__eo_to_smt u))
                (SmtTerm.and
                  (SmtTerm.leq
                    (SmtTerm.int_pow2
                      (SmtTerm._at_purify
                        (SmtTerm.int_log2 (__eo_to_smt u))))
                    (__eo_to_smt u))
                  (SmtTerm.and
                    (SmtTerm.lt (__eo_to_smt u)
                      (SmtTerm.int_pow2
                        (SmtTerm.plus
                          (SmtTerm._at_purify
                            (SmtTerm.int_log2 (__eo_to_smt u)))
                          (SmtTerm.plus (SmtTerm.Numeral 1)
                            (SmtTerm.Numeral 0)))))
                    (SmtTerm.Boolean true))))
              (SmtTerm.and
                (SmtTerm.imp
                  (SmtTerm.not
                    (SmtTerm.lt (SmtTerm.Numeral 0) (__eo_to_smt u)))
                  (SmtTerm.eq
                    (SmtTerm._at_purify
                      (SmtTerm.int_log2 (__eo_to_smt u)))
                    (SmtTerm.Numeral 0)))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtValue.Boolean true
    by_cases hPos : 0 < n
    · have hLe : native_zleq (native_int_pow2 (native_int_log2 n)) n = true :=
        native_int_pow2_log2_le n hPos
      have hLt :
          native_zlt n
            (native_int_pow2
              (native_zplus (native_int_log2 n) (native_zplus 1 0))) =
            true :=
        native_int_lt_next_pow2_log2 n hPos
      have hLt' :
          native_zlt n (native_int_pow2 (native_int_log2 n + 1)) = true := by
        simpa [native_zplus] using hLt
      have hCond : native_zlt 0 n = true := by
        unfold native_zlt
        rw [decide_eq_true_eq]
        exact hPos
      simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_2,
        __smtx_model_eval.eq_7, __smtx_model_eval.eq_9, __smtx_model_eval.eq_10,
        __smtx_model_eval.eq_13, __smtx_model_eval.eq_14,
        __smtx_model_eval.eq_17, __smtx_model_eval.eq_18,
        __smtx_model_eval.eq_29, __smtx_model_eval.eq_30,
        smtx_eval_eq_term_eq, hEvalU, hCond, hLe, hLt',
        __smtx_model_eval__at_purify, __smtx_model_eval_int_log2,
        __smtx_model_eval_int_pow2, __smtx_model_eval_plus,
        __smtx_model_eval_lt, __smtx_model_eval_leq,
        __smtx_model_eval_eq, __smtx_model_eval_not,
        __smtx_model_eval_or, __smtx_model_eval_imp,
        __smtx_model_eval_and, native_veq, native_zplus, native_not,
        native_or, native_and]
    · have hLog0 : native_int_log2 n = 0 :=
        native_int_log2_of_not_pos n hPos
      have hCond : native_zlt 0 n = false := by
        unfold native_zlt
        rw [decide_eq_false_iff_not]
        exact hPos
      simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_2,
        __smtx_model_eval.eq_7, __smtx_model_eval.eq_9, __smtx_model_eval.eq_10,
        __smtx_model_eval.eq_13, __smtx_model_eval.eq_14,
        __smtx_model_eval.eq_17, __smtx_model_eval.eq_18,
        __smtx_model_eval.eq_29, __smtx_model_eval.eq_30,
        smtx_eval_eq_term_eq, hEvalU, hCond, hLog0,
        __smtx_model_eval__at_purify, __smtx_model_eval_int_log2,
        __smtx_model_eval_int_pow2, __smtx_model_eval_plus,
        __smtx_model_eval_lt, __smtx_model_eval_leq,
        __smtx_model_eval_eq, __smtx_model_eval_not,
        __smtx_model_eval_or, __smtx_model_eval_imp,
        __smtx_model_eval_and, native_veq, native_zplus, native_not,
        native_or, native_and]

private theorem facts_arith_reduction_div_total
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
    (hTy :
      __eo_typeof
        (__arith_reduction_pred
          (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)) =
        Term.Bool) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
      true := by
  have hBool := typed_arith_reduction_div_total a b hTrans hTy
  have hDivNN :
      term_has_non_none_type
        (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.div_total) (R := SmtType.Int)
      (typeof_div_total_eq (__eo_to_smt a) (__eo_to_smt b)) hDivNN
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt a) SmtType.Int
      hArgs.1 (by simp) type_inhabited_int
  have hEvalBTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt b) SmtType.Int
      hArgs.2 (by simp) type_inhabited_int
  rcases int_value_canonical hEvalATy with ⟨n1, hEvalA⟩
  rcases int_value_canonical hEvalBTy with ⟨n2, hEvalB⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · by_cases hIsZ : __eo_is_z b = Term.Boolean true
    · rcases (eo_is_z_true_iff_numeral b).mp hIsZ with ⟨n, rfl⟩
      have hNZ : n ≠ 0 := by
        intro h0
        subst h0
        rw [arith_reduction_div_total_zero_eq_stuck a] at hTy
        cases hTy
      have hNZ0 : ¬0 = n := by
        intro h0
        exact hNZ h0.symm
      change
        __smtx_model_eval M
            (__eo_to_smt
              (__arith_reduction_pred
                (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a)
                  (Term.Numeral n)))) =
          SmtValue.Boolean true
      by_cases hNeg : n < 0
      · have hNegBool : native_zlt n 0 = true := by
          unfold native_zlt
          rw [decide_eq_true_eq]
          exact hNeg
        simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
          __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
          native_teq, native_ite, native_not, native_and, hNZ0, hNegBool]
        change
          __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))
                (SmtTerm._at_purify
                  (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))))
              (SmtTerm.and
                (smtDivTotalBounds (__eo_to_smt a) (SmtTerm.Numeral n) (-1))
                (SmtTerm.Boolean true))) =
            SmtValue.Boolean true
        have hEq :=
          smt_div_total_eq_purify_eval M (__eo_to_smt a) (SmtTerm.Numeral n)
            n1 n hEvalA (by simp [__smtx_model_eval.eq_2])
        have hSide :=
          smt_div_total_literal_side_eval_neg M (__eo_to_smt a) n1 n
            hEvalA hNeg
        simp [__smtx_model_eval.eq_9, hEq, hSide,
          __smtx_model_eval_and, native_and]
      · have hNegBool : native_zlt n 0 = false := by
          unfold native_zlt
          rw [decide_eq_false_iff_not]
          exact hNeg
        have hPos : 0 < n := by
          unfold native_Int at *
          omega
        simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
          __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
          native_teq, native_ite, native_not, native_and, hNZ0, hNegBool]
        change
          __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))
                (SmtTerm._at_purify
                  (SmtTerm.div_total (__eo_to_smt a) (SmtTerm.Numeral n))))
              (SmtTerm.and
                (smtDivTotalBounds (__eo_to_smt a) (SmtTerm.Numeral n) 1)
                (SmtTerm.Boolean true))) =
            SmtValue.Boolean true
        have hEq :=
          smt_div_total_eq_purify_eval M (__eo_to_smt a) (SmtTerm.Numeral n)
            n1 n hEvalA (by simp [__smtx_model_eval.eq_2])
        have hSide :=
          smt_div_total_literal_side_eval_pos M (__eo_to_smt a) n1 n
            hEvalA hPos
        simp [__smtx_model_eval.eq_9, hEq, hSide,
          __smtx_model_eval_and, native_and]
    · have hIsZFalse : __eo_is_z b = Term.Boolean false :=
        eo_is_z_eq_false_of_not_true b hIsZ
      change
        __smtx_model_eval M
            (__eo_to_smt
              (__arith_reduction_pred
                (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))) =
          SmtValue.Boolean true
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_ite,
        hIsZFalse, native_teq, native_ite]
      change
        __smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b))
              (SmtTerm._at_purify
                (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b))))
            (smtDivTotalGenericSide (__eo_to_smt a) (__eo_to_smt b))) =
          SmtValue.Boolean true
      have hEq :=
        smt_div_total_eq_purify_eval M (__eo_to_smt a) (__eo_to_smt b)
          n1 n2 hEvalA hEvalB
      have hSide :=
        smt_div_total_generic_side_eval M (__eo_to_smt a) (__eo_to_smt b)
          n1 n2 hEvalA hEvalB
      simp [__smtx_model_eval.eq_9, hEq, hSide,
        __smtx_model_eval_and, native_and]

private theorem facts_arith_reduction_mod_total
    (M : SmtModel) (hM : model_wf M) (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
    (hTy :
      __eo_typeof
        (__arith_reduction_pred
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)) =
        Term.Bool) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
      true := by
  have hBool := typed_arith_reduction_mod_total a b hTrans hTy
  have hModNN :
      term_has_non_none_type
        (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    exact hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.mod_total) (R := SmtType.Int)
      (typeof_mod_total_eq (__eo_to_smt a) (__eo_to_smt b)) hModNN
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt a) SmtType.Int
      hArgs.1 (by simp) type_inhabited_int
  have hEvalBTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
        SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt b) SmtType.Int
      hArgs.2 (by simp) type_inhabited_int
  rcases int_value_canonical hEvalATy with ⟨n1, hEvalA⟩
  rcases int_value_canonical hEvalBTy with ⟨n2, hEvalB⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · by_cases hIsZ : __eo_is_z b = Term.Boolean true
    · rcases (eo_is_z_true_iff_numeral b).mp hIsZ with ⟨n, rfl⟩
      have hNZ : n ≠ 0 := by
        intro h0
        subst h0
        rw [arith_reduction_mod_total_zero_eq_stuck a] at hTy
        cases hTy
      have hNZ0 : ¬0 = n := by
        intro h0
        exact hNZ h0.symm
      change
        __smtx_model_eval M
            (__eo_to_smt
              (__arith_reduction_pred
                (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a)
                  (Term.Numeral n)))) =
          SmtValue.Boolean true
      by_cases hNeg : n < 0
      · have hNegBool : native_zlt n 0 = true := by
          unfold native_zlt
          rw [decide_eq_true_eq]
          exact hNeg
        simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
          __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
          native_teq, native_ite, native_not, native_and, hNZ0, hNegBool]
        change
          __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.mod_total (__eo_to_smt a) (SmtTerm.Numeral n))
                (SmtTerm.neg (__eo_to_smt a)
                  (smtDivTotalProd (__eo_to_smt a) (SmtTerm.Numeral n))))
              (SmtTerm.and
                (smtDivTotalBounds (__eo_to_smt a) (SmtTerm.Numeral n) (-1))
                (SmtTerm.Boolean true))) =
            SmtValue.Boolean true
        have hEq :=
          smt_mod_total_eq_remainder_eval M (__eo_to_smt a) (SmtTerm.Numeral n)
            n1 n hEvalA (by simp [__smtx_model_eval.eq_2])
        have hSide :=
          smt_div_total_literal_side_eval_neg M (__eo_to_smt a) n1 n
            hEvalA hNeg
        simp [__smtx_model_eval.eq_9, hEq, hSide,
          __smtx_model_eval_and, native_and]
      · have hNegBool : native_zlt n 0 = false := by
          unfold native_zlt
          rw [decide_eq_false_iff_not]
          exact hNeg
        have hPos : 0 < n := by
          unfold native_Int at *
          omega
        simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
          __eo_requires, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
          native_teq, native_ite, native_not, native_and, hNZ0, hNegBool]
        change
          __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.mod_total (__eo_to_smt a) (SmtTerm.Numeral n))
                (SmtTerm.neg (__eo_to_smt a)
                  (smtDivTotalProd (__eo_to_smt a) (SmtTerm.Numeral n))))
              (SmtTerm.and
                (smtDivTotalBounds (__eo_to_smt a) (SmtTerm.Numeral n) 1)
                (SmtTerm.Boolean true))) =
            SmtValue.Boolean true
        have hEq :=
          smt_mod_total_eq_remainder_eval M (__eo_to_smt a) (SmtTerm.Numeral n)
            n1 n hEvalA (by simp [__smtx_model_eval.eq_2])
        have hSide :=
          smt_div_total_literal_side_eval_pos M (__eo_to_smt a) n1 n
            hEvalA hPos
        simp [__smtx_model_eval.eq_9, hEq, hSide,
          __smtx_model_eval_and, native_and]
    · have hIsZFalse : __eo_is_z b = Term.Boolean false :=
        eo_is_z_eq_false_of_not_true b hIsZ
      change
        __smtx_model_eval M
            (__eo_to_smt
              (__arith_reduction_pred
                (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))) =
          SmtValue.Boolean true
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_ite,
        hIsZFalse, native_teq, native_ite]
      change
        __smtx_model_eval M
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b))
              (SmtTerm.neg (__eo_to_smt a)
                (smtDivTotalProd (__eo_to_smt a) (__eo_to_smt b))))
            (smtDivTotalGenericSide (__eo_to_smt a) (__eo_to_smt b))) =
          SmtValue.Boolean true
      have hEq :=
        smt_mod_total_eq_remainder_eval M (__eo_to_smt a) (__eo_to_smt b)
          n1 n2 hEvalA hEvalB
      have hSide :=
        smt_div_total_generic_side_eval M (__eo_to_smt a) (__eo_to_smt b)
          n1 n2 hEvalA hEvalB
      simp [__smtx_model_eval.eq_9, hEq, hSide,
        __smtx_model_eval_and, native_and]

private theorem facts_arith_reduction_of_trans
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof (__arith_reduction_pred t) = Term.Bool) :
    eo_interprets M (__arith_reduction_pred t) true := by
  cases t with
  | Apply f x =>
      cases f with
      | UOp op =>
          by_cases hIsInt : op = UserOp.is_int
          · subst op
            exact facts_arith_reduction_is_int M hM x hTrans
          · by_cases hToInt : op = UserOp.to_int
            · subst op
              exact facts_arith_reduction_to_int M hM x hTrans
            · by_cases hAbs : op = UserOp.abs
              · subst op
                exact facts_arith_reduction_abs_from_trans M hM x hTrans
              · by_cases hLog : op = UserOp.int_log2
                · subst op
                  exact facts_arith_reduction_int_log2 M hM x hTrans
                · simp [__arith_reduction_pred, hIsInt, hToInt, hAbs, hLog] at hTy
                  exact False.elim (false_of_typeof_stuck_bool hTy)
      | Apply g u =>
          cases g with
          | UOp op =>
              by_cases hQdiv : op = UserOp.qdiv
              · subst op
                exact facts_arith_reduction_qdiv M hM u x hTrans
              · by_cases hDiv : op = UserOp.div
                · subst op
                  simpa [__arith_reduction_pred] using
                    facts_arith_reduction_div M u x
                      (typed_arith_reduction_div u x hTrans)
                · by_cases hMod : op = UserOp.mod
                  · subst op
                    simpa [__arith_reduction_pred] using
                      facts_arith_reduction_mod M u x
                        (typed_arith_reduction_mod u x hTrans)
                  · by_cases hQdivTotal : op = UserOp.qdiv_total
                    · subst op
                      exact facts_arith_reduction_qdiv_total M hM u x hTrans
                    · by_cases hDivTotal : op = UserOp.div_total
                      · subst op
                        exact facts_arith_reduction_div_total M hM u x hTrans hTy
                      · by_cases hModTotal : op = UserOp.mod_total
                        · subst op
                          exact facts_arith_reduction_mod_total M hM u x hTrans hTy
                        · simp [__arith_reduction_pred, hQdiv, hDiv, hMod,
                            hQdivTotal, hDivTotal, hModTotal] at hTy
                          exact False.elim (false_of_typeof_stuck_bool hTy)
          | _ =>
              simp [__arith_reduction_pred] at hTy
              exact False.elim (false_of_typeof_stuck_bool hTy)
      | _ =>
          simp [__arith_reduction_pred] at hTy
          exact False.elim (false_of_typeof_stuck_bool hTy)
  | _ =>
      simp [__arith_reduction_pred] at hTy
      exact False.elim (false_of_typeof_stuck_bool hTy)

private theorem arith_reduction_prog_eq_pred (t : Term) :
    __eo_prog_arith_reduction t = __arith_reduction_pred t := by
  cases t <;> rfl

private theorem typed___eo_prog_arith_reduction_impl
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof (__eo_prog_arith_reduction t) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_reduction t) := by
  rw [arith_reduction_prog_eq_pred t]
  exact typed_arith_reduction_of_trans t hTrans
    (by simpa [arith_reduction_prog_eq_pred t] using hTy)

private theorem facts___eo_prog_arith_reduction_impl
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t)
    (hTy : __eo_typeof (__eo_prog_arith_reduction t) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_reduction t) true := by
  rw [arith_reduction_prog_eq_pred t]
  exact facts_arith_reduction_of_trans M hM t hTrans
    (by simpa [arith_reduction_prog_eq_pred t] using hTy)

public theorem cmd_step_arith_reduction_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_reduction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.arith_reduction args premises ≠
        Term.Stuck :=
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
              let T := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons T CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hTTrans : RuleProofs.eo_has_smt_translation T := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_arith_reduction T) = Term.Bool
                at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_reduction T) true
                exact facts___eo_prog_arith_reduction_impl M hM T hTTrans
                  hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_arith_reduction T)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_arith_reduction T)
                  (typed___eo_prog_arith_reduction_impl T hTTrans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
