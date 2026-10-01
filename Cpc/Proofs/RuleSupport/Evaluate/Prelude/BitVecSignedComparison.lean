module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import all Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StrReplaceAllSupport
public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Init.Data.Repr
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecSignExtend
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecSignExtend

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.smt_bv_msb_set (w n : native_Int) : native_Bool :=
  native_zeq
    (native_mod_total
      (native_div_total n (native_int_pow2 (w - 1))) 2) 1

theorem EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_formula
    (w n1 n2 : native_Int) :
    __smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_or
          (native_and
            (native_not (EvaluateProofInternal.smt_bv_msb_set w n1))
            (EvaluateProofInternal.smt_bv_msb_set w n2))
          (native_and
            (native_veq
              (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n1))
              (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n2)))
            (native_zlt n2 n1))) := by
  simp [__smtx_model_eval_bvsgt, __smtx_model_eval__,
    __smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_bvugt,
    EvaluateProofInternal.smt_bv_msb_set, __smtx_bv_sizeof_value, native_binary_extract,
    native_zplus, SmtEval.native_zplus, native_zneg,
    SmtEval.native_zneg]
  have hArg : w + -1 = w - 1 := by
    rw [Int.sub_eq_add_neg]
  have hWidth : w + -(w - 1) = 1 := by
    rw [Int.sub_eq_add_neg]
    change w + -(w + -1) = 1
    calc
      w + -(w + -1) = w + (-w + 1) := by
        rw [Int.neg_add, Int.neg_neg]
      _ = w + -w + 1 := by
        rw [← Int.add_assoc]
      _ = 0 + 1 := by
        rw [Int.add_right_neg]
      _ = 1 := by
        rfl
  have hPow1 : native_int_pow2 1 = 2 := by
    native_decide
  simp [hArg, hWidth, hPow1, native_veq, native_zeq,
    SmtEval.native_zeq]

theorem EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
    {w n : native_Int}
    (hwpos : 0 < w)
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    n = native_mod_total n (native_int_pow2 (w - 1)) := by
  let p := native_int_pow2 (w - 1)
  let q := native_div_total n p
  let r := native_mod_total n p
  have hpPos : 0 < p := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hwp0
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
  have hqNonneg : 0 <= q :=
    Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
  have hqLt2 : q < 2 := by
    have hlt : n < 2 * p := by
      simpa [hPow] using hRange.2
    exact Int.ediv_lt_of_lt_mul hpPos hlt
  have hqCases : q = 0 ∨ q = 1 := by
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · have hqPos : 0 < q := by
        rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
        · exact hlt
        · exact False.elim (hq0 heq.symm)
      have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
      have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
      exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
  have hDivMod : p * q + r = n := by
    simpa [q, r, p, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod n p
  rcases hqCases with hq | hq
  · have hnEq : n = r := by
      rw [hq] at hDivMod
      simp at hDivMod
      exact hDivMod.symm
    simpa [r, p] using hnEq
  · have hSignTrue : EvaluateProofInternal.smt_bv_msb_set w n = true := by
      dsimp [EvaluateProofInternal.smt_bv_msb_set, q, p] at hq ⊢
      rw [hq]
      simp [native_mod_total, native_zeq, SmtEval.native_zeq]
    rw [hSign] at hSignTrue
    cases hSignTrue

theorem EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
    {w n : native_Int}
    (hwpos : 0 < w)
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    n =
      native_int_pow2 (w - 1) +
        native_mod_total n (native_int_pow2 (w - 1)) := by
  let p := native_int_pow2 (w - 1)
  let q := native_div_total n p
  let r := native_mod_total n p
  have hpPos : 0 < p := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hwp0
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
  have hqNonneg : 0 <= q :=
    Int.ediv_nonneg hRange.1 (Int.le_of_lt hpPos)
  have hqLt2 : q < 2 := by
    have hlt : n < 2 * p := by
      simpa [hPow] using hRange.2
    exact Int.ediv_lt_of_lt_mul hpPos hlt
  have hqCases : q = 0 ∨ q = 1 := by
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    · have hqPos : 0 < q := by
        rcases Int.lt_or_eq_of_le hqNonneg with hlt | heq
        · exact hlt
        · exact False.elim (hq0 heq.symm)
      have hqGe1 : 1 <= q := (Int.add_one_le_iff).mpr hqPos
      have hqLe1 : q <= 1 := Int.le_of_lt_add_one hqLt2
      exact Or.inr (Int.le_antisymm hqLe1 hqGe1)
  have hDivMod : p * q + r = n := by
    simpa [q, r, p, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod n p
  rcases hqCases with hq | hq
  · have hSignFalse : EvaluateProofInternal.smt_bv_msb_set w n = false := by
      dsimp [EvaluateProofInternal.smt_bv_msb_set, q, p] at hq ⊢
      rw [hq]
      simp [native_mod_total, native_zeq, SmtEval.native_zeq]
    rw [hSign] at hSignFalse
    cases hSignFalse
  · have hnEq : n = p + r := by
      rw [hq] at hDivMod
      simp at hDivMod
      exact hDivMod.symm
    simpa [p, r] using hnEq

theorem EvaluateProofInternal.native_mod_pow2_pred_range_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    0 <= native_mod_total n (native_int_pow2 (w - 1)) ∧
      native_mod_total n (native_int_pow2 (w - 1)) <
        native_int_pow2 (w - 1) := by
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hpPos : 0 < native_int_pow2 (w - 1) :=
    EvaluateProofInternal.native_int_pow2_pos_of_nonneg hwp0
  constructor
  · simpa [native_mod_total] using
      Int.emod_nonneg n (Int.ne_of_gt hpPos)
  · simpa [native_mod_total] using
      Int.emod_lt_of_pos n hpPos

theorem EvaluateProofInternal.smt_bvsgt_formula_eq_signed_gt
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    native_or
        (native_and
          (native_not (EvaluateProofInternal.smt_bv_msb_set w n1))
          (EvaluateProofInternal.smt_bv_msb_set w n2))
        (native_and
          (native_veq
            (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n1))
            (SmtValue.Boolean (EvaluateProofInternal.smt_bv_msb_set w n2)))
          (native_zlt n2 n1)) =
      native_zlt (native_binary_uts w n2) (native_binary_uts w n1) := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let r1 := native_mod_total n1 p
    let r2 := native_mod_total n2 p
    have hUts1 :
        (if EvaluateProofInternal.smt_bv_msb_set w n1 then
            native_zplus (native_zneg p) r1
          else r1) =
          native_binary_uts w n1 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n1) hw0 hCanon1
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r1, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hUts2 :
        (if EvaluateProofInternal.smt_bv_msb_set w n2 then
            native_zplus (native_zneg p) r2
          else r2) =
          native_binary_uts w n2 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n2) hw0 hCanon2
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r2, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hr1Range :
        0 <= r1 ∧ r1 < p := by
      simpa [r1, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n1) hwpos
    have hr2Range :
        0 <= r2 ∧ r2 < p := by
      simpa [r2, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n2) hwpos
    cases hSign1 : EvaluateProofInternal.smt_bv_msb_set w n1 <;>
      cases hSign2 : EvaluateProofInternal.smt_bv_msb_set w n2
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      simp
      simp [native_or, native_and, native_not, native_veq]
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hr1Nonneg : 0 <= r1 := hr1Range.1
      have hr2Lt : r2 < p := hr2Range.2
      have hLt : native_zplus (native_zneg p) r2 < r1 := by
        change -p + r2 < r1
        have hNeg : -p + r2 < 0 := by
          have hAdd := Int.add_lt_add_right hr2Lt (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        exact Int.lt_of_lt_of_le hNeg hr1Nonneg
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1]
      simp [native_or, native_and, native_not, native_veq,
        native_zlt, SmtEval.native_zlt, hLt]
    · have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      have hr2Nonneg : 0 <= r2 := hr2Range.1
      have hr1Lt : r1 < p := hr1Range.2
      have hNotLt : ¬ r2 < native_zplus (native_zneg p) r1 := by
        change ¬ r2 < -p + r1
        intro hLt
        have hNeg : -p + r1 < 0 := by
          have hAdd := Int.add_lt_add_right hr1Lt (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        exact (Int.not_lt_of_ge hr2Nonneg) (Int.lt_trans hLt hNeg)
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN2]
      simp [native_or, native_and, native_not, native_veq,
        native_zlt, SmtEval.native_zlt, hNotLt]
    · have hN1 :
          n1 = p + r1 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = p + r2 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      have hCmp :
          native_zlt (p + r2) (p + r1) =
            native_zlt
              (native_zplus (native_zneg p) r2)
              (native_zplus (native_zneg p) r1) := by
        simp [native_zlt, SmtEval.native_zlt, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2, hCmp]
      simp [native_or, native_and, native_not, native_veq]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange1 := bitvec_payload_range_of_canonical hw0 hCanon1
    have hRange2 := bitvec_payload_range_of_canonical hw0 hCanon2
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hn1Eq : n1 = 0 := by
      have hlt : n1 < 1 := by
        simpa [hPow0] using hRange1.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange1.1
    have hn2Eq : n2 = 0 := by
      have hlt : n2 < 1 := by
        simpa [hPow0] using hRange2.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange2.1
    subst n1
    subst n2
    native_decide

theorem EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_zlt (native_binary_uts w n2)
          (native_binary_uts w n1)) := by
  rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_formula]
  rw [EvaluateProofInternal.smt_bvsgt_formula_eq_signed_gt hw0 hCanon1 hCanon2]

theorem EvaluateProofInternal.native_binary_uts_eq_iff_canonical
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    native_binary_uts w n1 = native_binary_uts w n2 ↔ n1 = n2 := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let r1 := native_mod_total n1 p
    let r2 := native_mod_total n2 p
    have hUts1 :
        (if EvaluateProofInternal.smt_bv_msb_set w n1 then
            native_zplus (native_zneg p) r1
          else r1) =
          native_binary_uts w n1 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n1) hw0 hCanon1
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r1, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hUts2 :
        (if EvaluateProofInternal.smt_bv_msb_set w n2 then
            native_zplus (native_zneg p) r2
          else r2) =
          native_binary_uts w n2 := by
      have hsimpa :=
        EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n2) hw0 hCanon2
      try simp [EvaluateProofInternal.smt_bv_msb_set, p, r2, Int.sub_eq_add_neg] at hsimpa ⊢
      exact hsimpa
    have hr1Range :
        0 <= r1 ∧ r1 < p := by
      simpa [r1, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n1) hwpos
    have hr2Range :
        0 <= r2 ∧ r2 < p := by
      simpa [r2, p] using
        EvaluateProofInternal.native_mod_pow2_pred_range_of_pos (w := w) (n := n2) hwpos
    cases hSign1 : EvaluateProofInternal.smt_bv_msb_set w n1 <;>
      cases hSign2 : EvaluateProofInternal.smt_bv_msb_set w n2
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      simp
    · have hN1 :
          n1 = r1 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = p + r2 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      constructor
      · intro hEq
        simp at hEq
        have hNeg : native_zplus (native_zneg p) r2 < 0 := by
          change -p + r2 < 0
          have hAdd := Int.add_lt_add_right hr2Range.2 (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        rw [← hEq] at hNeg
        exact False.elim ((Int.not_lt_of_ge hr1Range.1) hNeg)
      · intro hEq
        have hGe : p <= p + r2 :=
          Int.le_add_of_nonneg_right hr2Range.1
        have hLt : p + r2 < p := by
          rw [← hEq]
          exact hr1Range.2
        exact False.elim ((Int.not_lt_of_ge hGe) hLt)
    · have hN1 :
          n1 = p + r1 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = r2 :=
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      constructor
      · intro hEq
        simp at hEq
        have hNeg : native_zplus (native_zneg p) r1 < 0 := by
          change -p + r1 < 0
          have hAdd := Int.add_lt_add_right hr1Range.2 (-p)
          simpa [Int.add_comm, Int.add_right_neg] using hAdd
        rw [hEq] at hNeg
        exact False.elim ((Int.not_lt_of_ge hr2Range.1) hNeg)
      · intro hEq
        have hGe : p <= p + r1 :=
          Int.le_add_of_nonneg_right hr1Range.1
        have hLt : p + r1 < p := by
          rw [hEq]
          exact hr2Range.2
        exact False.elim ((Int.not_lt_of_ge hGe) hLt)
    · have hN1 :
          n1 = p + r1 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n1) hwpos hw0 hCanon1 hSign1
      have hN2 :
          n2 = p + r2 :=
        EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
          (w := w) (n := n2) hwpos hw0 hCanon2 hSign2
      rw [← hUts1, ← hUts2, hSign1, hSign2, hN1, hN2]
      simp [native_zplus, native_zneg]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange1 := bitvec_payload_range_of_canonical hw0 hCanon1
    have hRange2 := bitvec_payload_range_of_canonical hw0 hCanon2
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hn1Eq : n1 = 0 := by
      have hlt : n1 < 1 := by
        simpa [hPow0] using hRange1.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange1.1
    have hn2Eq : n2 = 0 := by
      have hlt : n2 < 1 := by
        simpa [hPow0] using hRange2.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange2.1
    subst n1
    subst n2
    native_decide

theorem EvaluateProofInternal.native_veq_binary_eq_signed_teq_of_canonical
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    native_veq (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      native_teq (Term.Numeral (native_binary_uts w n2))
        (Term.Numeral (native_binary_uts w n1)) := by
  have hIff :=
    EvaluateProofInternal.native_binary_uts_eq_iff_canonical
      (w := w) (n1 := n1) (n2 := n2) hw0 hCanon1 hCanon2
  by_cases hEq : n1 = n2
  · subst n2
    simp [native_veq, native_teq]
  · have hUtsNe :
        native_binary_uts w n2 ≠ native_binary_uts w n1 := by
      intro hUts
      exact hEq (hIff.mp hUts.symm)
    simp [native_veq, native_teq, hEq, hUtsNe]

theorem EvaluateProofInternal.smtx_model_eval_bvsge_binary_eq_uts
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvsge (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_or
          (native_zlt (native_binary_uts w n2)
            (native_binary_uts w n1))
          (native_teq (Term.Numeral (native_binary_uts w n2))
            (Term.Numeral (native_binary_uts w n1)))) := by
  rw [__smtx_model_eval_bvsge]
  rw [EvaluateProofInternal.smtx_model_eval_bvsgt_binary_eq_uts hw0 hCanon1 hCanon2]
  simp [__smtx_model_eval_or, __smtx_model_eval_eq]
  rw [EvaluateProofInternal.native_veq_binary_eq_signed_teq_of_canonical
    hw0 hCanon1 hCanon2]

theorem EvaluateProofInternal.native_teq_term_numeral_comm
    (n1 n2 : native_Int) :
    native_teq (Term.Numeral n1) (Term.Numeral n2) =
      native_teq (Term.Numeral n2) (Term.Numeral n1) := by
  by_cases hEq : n1 = n2
  · subst n2
    simp [native_teq]
  · have hEq' : n2 ≠ n1 := by
      intro h
      exact hEq h.symm
    simp [native_teq, hEq, hEq']

theorem EvaluateProofInternal.smtx_model_eval_bvsle_binary_eq_uts
    {w n1 n2 : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon1 :
      native_zeq n1
          (native_mod_total n1 (native_int_pow2 w)) =
        true)
    (hCanon2 :
      native_zeq n2
          (native_mod_total n2 (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvsle (SmtValue.Binary w n1) (SmtValue.Binary w n2) =
      SmtValue.Boolean
        (native_or
          (native_zlt (native_binary_uts w n1)
            (native_binary_uts w n2))
          (native_teq (Term.Numeral (native_binary_uts w n2))
            (Term.Numeral (native_binary_uts w n1)))) := by
  rw [__smtx_model_eval_bvsle]
  rw [EvaluateProofInternal.smtx_model_eval_bvsge_binary_eq_uts
    (w := w) (n1 := n2) (n2 := n1) hw0 hCanon2 hCanon1]
  rw [EvaluateProofInternal.native_teq_term_numeral_comm]

