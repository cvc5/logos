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
public import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecSignedComparison
import all Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecSignedComparison

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.eo_eval_bvashr_rhs (a b : Term) : Term :=
  let runAmt := __eo_to_z (__run_evaluate b)
  let runA := __run_evaluate a
  let powAmt :=
    __eo_ite (__eo_is_z runAmt)
      (__eo_ite (__eo_is_neg runAmt) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) runAmt))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) runAmt)
  __eo_to_bin (__bv_bitwidth (__eo_typeof a))
    (__eo_zdiv (EvaluateProofInternal.eo_signed_bv_value runA) powAmt)

theorem EvaluateProofInternal.native_mod_two_eq_zero_of_ne_one
    (x : native_Int)
    (hNeOne :
      native_zeq (native_mod_total x 2) 1 = false) :
    native_mod_total x 2 = 0 := by
  let r := native_mod_total x 2
  have hrNonneg : 0 <= r := by
    simpa [r, native_mod_total] using
      Int.emod_nonneg x (by decide : (2 : Int) ≠ 0)
  have hrLt : r < 2 := by
    simpa [r, native_mod_total] using
      Int.emod_lt_of_pos x (by decide : 0 < (2 : Int))
  have hrNeOne : r ≠ 1 := by
    intro h
    have hTrue : native_zeq r 1 = true := by
      simp [native_zeq, SmtEval.native_zeq, h]
    rw [show native_zeq r 1 =
        native_zeq (native_mod_total x 2) 1 by rfl] at hTrue
    rw [hTrue] at hNeOne
    cases hNeOne
  have hrLeOne : r <= 1 := Int.le_of_lt_add_one hrLt
  rcases Int.lt_or_eq_of_le hrLeOne with hrLtOne | hrEqOne
  · have hrLeZero : r <= 0 := Int.le_of_lt_add_one hrLtOne
    exact Int.le_antisymm hrLeZero hrNonneg
  · exact False.elim (hrNeOne hrEqOne)

theorem EvaluateProofInternal.native_mod_two_eq_one_of_eq_one
    (x : native_Int)
    (hOne :
      native_zeq (native_mod_total x 2) 1 = true) :
    native_mod_total x 2 = 1 := by
  simpa [native_zeq, SmtEval.native_zeq] using hOne

theorem EvaluateProofInternal.native_veq_bvashr_msb_zero_of_false
    (w n : native_Int)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    native_veq
        (SmtValue.Binary 1
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2))
        (SmtValue.Binary 1 0) =
      true := by
  have hZero :=
    EvaluateProofInternal.native_mod_two_eq_zero_of_ne_one
      (native_div_total n (native_int_pow2 (w - 1))) hSign
  rw [hZero]
  simp [native_veq]

theorem EvaluateProofInternal.native_veq_bvashr_msb_zero_of_true
    (w n : native_Int)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    native_veq
        (SmtValue.Binary 1
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2))
        (SmtValue.Binary 1 0) =
      false := by
  have hOne :=
    EvaluateProofInternal.native_mod_two_eq_one_of_eq_one
      (native_div_total n (native_int_pow2 (w - 1))) hSign
  rw [hOne]
  simp [native_veq]

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_lshr_of_msb_false
    {w n s : native_Int}
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_div_total n (native_int_pow2 s))
          (native_int_pow2 w)) := by
  have hArg :
      native_zplus w (native_zneg 1) = w - 1 := by
    change w + -1 = w - 1
    rw [Int.sub_eq_add_neg]
  have hWidth :
      native_zplus
          (native_zplus (w - 1) 1)
          (native_zneg (w - 1)) =
        1 := by
    change (w - 1) + 1 + -(w - 1) = 1
    calc
      (w - 1) + 1 + -(w - 1) = w + -(w - 1) := by
        have hSub : (w - 1) + 1 = w := by
          rw [Int.sub_eq_add_neg]
          rw [Int.add_assoc]
          have hConst : (-1 : Int) + 1 = 0 := by native_decide
          rw [hConst, Int.add_zero]
        rw [hSub]
      _ = 1 := by
        rw [Int.sub_eq_add_neg]
        change w + -(w + -1) = 1
        rw [Int.neg_add, Int.neg_neg]
        rw [← Int.add_assoc]
        rw [Int.add_right_neg, Int.zero_add]
  have hPow1 : native_int_pow2 1 = 2 := by
    native_decide
  have hMsbZero :=
    EvaluateProofInternal.native_veq_bvashr_msb_zero_of_false w n hSign
  simp [__smtx_model_eval_bvashr, __smtx_model_eval__,
    __smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_ite, __smtx_model_eval_bvlshr,
    __smtx_bv_sizeof_value, native_binary_extract, hArg, hWidth,
    hPow1, hMsbZero]

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_not_lshr_not_of_msb_true
    {w n s : native_Int}
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_binary_not w
            (native_mod_total
              (native_div_total
                (native_mod_total (native_binary_not w n)
                  (native_int_pow2 w))
                (native_int_pow2 s))
              (native_int_pow2 w)))
          (native_int_pow2 w)) := by
  have hArg :
      native_zplus w (native_zneg 1) = w - 1 := by
    change w + -1 = w - 1
    rw [Int.sub_eq_add_neg]
  have hWidth :
      native_zplus
          (native_zplus (w - 1) 1)
          (native_zneg (w - 1)) =
        1 := by
    change (w - 1) + 1 + -(w - 1) = 1
    calc
      (w - 1) + 1 + -(w - 1) = w + -(w - 1) := by
        have hSub : (w - 1) + 1 = w := by
          rw [Int.sub_eq_add_neg]
          rw [Int.add_assoc]
          have hConst : (-1 : Int) + 1 = 0 := by native_decide
          rw [hConst, Int.add_zero]
        rw [hSub]
      _ = 1 := by
        rw [Int.sub_eq_add_neg]
        change w + -(w + -1) = 1
        rw [Int.neg_add, Int.neg_neg]
        rw [← Int.add_assoc]
        rw [Int.add_right_neg, Int.zero_add]
  have hPow1 : native_int_pow2 1 = 2 := by
    native_decide
  have hMsbOne :=
    EvaluateProofInternal.native_veq_bvashr_msb_zero_of_true w n hSign
  simp [__smtx_model_eval_bvashr, __smtx_model_eval__,
    __smtx_model_eval_extract, __smtx_model_eval_eq,
    __smtx_model_eval_ite, __smtx_model_eval_bvlshr,
    __smtx_model_eval_bvnot, __smtx_bv_sizeof_value,
    native_binary_extract, hArg, hWidth, hPow1, hMsbOne]

theorem EvaluateProofInternal.native_binary_uts_eq_self_of_msb_false
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = false) :
    native_binary_uts w n = n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    have hN : n = native_mod_total n p := by
      simpa [EvaluateProofInternal.smt_bv_msb_set, p, Int.sub_eq_add_neg] using
        EvaluateProofInternal.smt_bv_msb_false_eq_mod_of_pos
          (w := w) (n := n) hwpos hw0 hCanon hSign
    rw [native_binary_uts]
    change native_zplus
        (native_zmult 2
          (native_mod_total n
            (native_int_pow2 (native_zplus w (native_zneg 1)))))
        (native_zneg n) = n
    have hpEq :
        native_int_pow2 (native_zplus w (native_zneg 1)) = p := by
      simp [p, native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.sub_eq_add_neg]
    rw [hpEq]
    rw [← hN]
    simp [native_zplus, native_zmult, native_zneg]
    rw [Int.two_mul, Int.add_assoc, Int.add_right_neg, Int.add_zero]
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide

theorem EvaluateProofInternal.native_binary_not_eq_pow_sub_succ
    (w n : native_Int) :
    native_binary_not w n =
      native_int_pow2 w - (n + 1) := by
  simp [native_binary_not, native_zplus, native_zneg,
    Int.sub_eq_add_neg]

theorem EvaluateProofInternal.native_binary_not_range_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    0 <= native_binary_not w n ∧
      native_binary_not w n < native_int_pow2 w := by
  have hRange := bitvec_payload_range_of_canonical hw0 hCanon
  have hRaw := EvaluateProofInternal.native_binary_not_eq_pow_sub_succ w n
  constructor
  · rw [hRaw]
    exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hRange.2)
  · rw [hRaw]
    exact Int.sub_lt_self _ (Int.lt_add_one_of_le hRange.1)

theorem EvaluateProofInternal.native_binary_not_mod_self_of_canonical
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    native_mod_total (native_binary_not w n) (native_int_pow2 w) =
      native_binary_not w n := by
  have hRange := EvaluateProofInternal.native_binary_not_range_of_canonical
    (w := w) (n := n) hw0 hCanon
  simpa [native_mod_total] using
    Int.emod_eq_of_lt hRange.1 hRange.2

theorem EvaluateProofInternal.smt_bv_msb_true_width_pos
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    0 < w := by
  by_cases hwpos : 0 < w
  · exact hwpos
  · have hw : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwEq : w = 0 :=
      Int.le_antisymm (Int.le_of_not_gt hwpos) hw
    subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    have hSignFalse : EvaluateProofInternal.smt_bv_msb_set 0 0 = false := by
      native_decide
    rw [hSignFalse] at hSign
    cases hSign

theorem EvaluateProofInternal.native_binary_uts_eq_sub_pow_of_msb_true
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    native_binary_uts w n = n - native_int_pow2 w := by
  have hwpos :=
    EvaluateProofInternal.smt_bv_msb_true_width_pos
      (w := w) (n := n) hw0 hCanon hSign
  let p := native_int_pow2 (w - 1)
  let r := native_mod_total n p
  have hN : n = p + r := by
    simpa [EvaluateProofInternal.smt_bv_msb_set, p, r, Int.sub_eq_add_neg] using
      EvaluateProofInternal.smt_bv_msb_true_eq_pow_add_mod_of_pos
        (w := w) (n := n) hwpos hw0 hCanon hSign
  have hPow : native_int_pow2 w = 2 * p := by
    simpa [p] using EvaluateProofInternal.native_int_pow2_succ_pred (w := w) hwpos
  have hpEq :
      native_int_pow2 (native_zplus w (native_zneg 1)) = p := by
    simp [p, native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.sub_eq_add_neg]
  rw [native_binary_uts]
  change
    native_zplus
        (native_zmult 2
          (native_mod_total n
            (native_int_pow2 (native_zplus w (native_zneg 1)))))
        (native_zneg n) =
      n - native_int_pow2 w
  rw [hpEq]
  change 2 * r + -n = n - native_int_pow2 w
  rw [hN, hPow]
  change 2 * r + -(p + r) = p + r - 2 * p
  calc
    2 * r + -(p + r) = r + -p := by
      rw [Int.two_mul, Int.neg_add]
      calc
        r + r + (-p + -r) = r + r + (-r + -p) := by
          rw [Int.add_comm (-p) (-r)]
        _ = r + r + -r + -p := by
          rw [← Int.add_assoc]
        _ = r + -p := by
          rw [show r + r + -r = r by
            rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]]
    _ = p + r - 2 * p := by
      rw [Int.two_mul]
      change r + -p = p + r - (p + p)
      rw [Int.sub_eq_add_neg, Int.neg_add]
      symm
      calc
        p + r + (-p + -p) = p + r + -p + -p := by
          rw [← Int.add_assoc]
        _ = r + -p := by
          rw [show p + r + -p = r by
            calc
              p + r + -p = p + (r + -p) := by rw [Int.add_assoc]
              _ = p + (-p + r) := by rw [Int.add_comm r (-p)]
              _ = p + -p + r := by rw [← Int.add_assoc]
              _ = r := by rw [Int.add_right_neg, Int.zero_add]]
        _ = r + -p := rfl

theorem EvaluateProofInternal.native_int_pow2_ge_one_of_nonneg
    {s : native_Int} (hs0 : 0 <= s) :
    1 <= native_int_pow2 s := by
  have hpos := EvaluateProofInternal.native_int_pow2_pos_of_nonneg hs0
  exact (Int.add_one_le_iff).mpr hpos

theorem EvaluateProofInternal.native_neg_succ_div_pow2_eq_neg_div_succ
    {m s : native_Int}
    (hm0 : 0 <= m)
    (hs0 : 0 <= s) :
    native_div_total (-(m + 1)) (native_int_pow2 s) =
      -(native_div_total m (native_int_pow2 s) + 1) := by
  let d := native_int_pow2 s
  let q := native_div_total m d
  let r := native_mod_total m d
  have hdPos : 0 < d := by
    dsimp [d]
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hs0
  have hdNe : d ≠ 0 := Int.ne_of_gt hdPos
  have hDivMod : d * q + r = m := by
    simpa [q, r, d, native_div_total, native_mod_total] using
      Int.mul_ediv_add_emod m d
  have hr0 : 0 <= r := by
    simpa [r, native_mod_total] using
      Int.emod_nonneg m hdNe
  have hrlt : r < d := by
    simpa [r, native_mod_total] using
      Int.emod_lt_of_pos m hdPos
  have hUpper :
      native_div_total (-(m + 1)) d <= -(q + 1) := by
    rw [native_div_total]
    rw [(Int.ediv_le_iff_le_mul (k := d)
      (x := -(m + 1)) (y := -(q + 1)) hdPos)]
    have hEq : m + 1 = d * q + (r + 1) := by
      rw [← hDivMod]
      rw [← Int.add_assoc]
    calc
      -(m + 1) = -(d * q + (r + 1)) := by rw [hEq]
      _ = -(d * q) + -(r + 1) := by rw [Int.neg_add]
      _ < -(d * q) := by
        have hr1pos : 0 < r + 1 := Int.lt_add_one_of_le hr0
        have hneg : -(r + 1) < 0 := by
          have h := Int.neg_lt_neg hr1pos
          simpa using h
        have h := Int.add_lt_add_left hneg (-(d * q))
        simpa using h
      _ = -(q + 1) * d + d := by
        calc
          -(d * q) = -(q * d) := by rw [Int.mul_comm d q]
          _ = -q * d := by rw [Int.neg_mul_eq_neg_mul]
          _ = (-(q + 1) + 1) * d := by
            have hCoeff : -(q + 1) + 1 = -q := by
              rw [Int.neg_add]
              change -q + -1 + 1 = -q
              rw [Int.add_assoc]
              have hConst : (-1 : Int) + 1 = 0 := by native_decide
              rw [hConst, Int.add_zero]
            rw [hCoeff]
          _ = -(q + 1) * d + 1 * d := by rw [Int.add_mul]
          _ = -(q + 1) * d + d := by rw [Int.one_mul]
  have hLower :
      -(q + 1) <= native_div_total (-(m + 1)) d := by
    rw [native_div_total]
    apply Int.le_of_not_gt
    intro hLt
    have hLtMul :=
      (Int.ediv_lt_iff_lt_mul (a := -(m + 1))
        (b := -(q + 1)) (c := d) hdPos).mp hLt
    have hNot : ¬ -(m + 1) < -(q + 1) * d := by
      intro h
      have hLe : m + 1 <= (q + 1) * d := by
        have hEq : m + 1 = d * q + (r + 1) := by
          rw [← hDivMod]
          rw [← Int.add_assoc]
        have hr1le : r + 1 <= d := (Int.add_one_le_iff).mpr hrlt
        have hStep : d * q + (r + 1) <= d * q + d :=
          Int.add_le_add_left hr1le (d * q)
        have hRight : d * q + d = (q + 1) * d := by
          calc
            d * q + d = q * d + d := by rw [Int.mul_comm d q]
            _ = q * d + 1 * d := by rw [Int.one_mul]
            _ = (q + 1) * d := by rw [Int.add_mul]
        rw [hEq]
        rw [← hRight]
        exact hStep
      have hNegLe : -((q + 1) * d) <= -(m + 1) :=
        Int.neg_le_neg hLe
      have hNegMul : -((q + 1) * d) = -(q + 1) * d := by
        rw [Int.neg_mul_eq_neg_mul]
      rw [hNegMul] at hNegLe
      exact (Int.not_lt_of_ge hNegLe) h
    exact hNot hLtMul
  change native_div_total (-(m + 1)) d = -(native_div_total m d + 1)
  exact Int.le_antisymm hUpper hLower

theorem EvaluateProofInternal.int_sub_eq_neg_sub_succ_add_one
    (n p : native_Int) :
    n - p = -(p - (n + 1) + 1) := by
  grind

theorem EvaluateProofInternal.int_sub_sub_neg_succ_eq
    (p q : native_Int) :
    p - (q + 1) - (-(q + 1)) = p := by
  grind

theorem EvaluateProofInternal.native_bvashr_negative_payload_eq_signed_div
    {w n s : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hShiftCanon :
      native_zeq s
          (native_mod_total s (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    native_mod_total
        (native_binary_not w
          (native_mod_total
            (native_div_total
              (native_mod_total (native_binary_not w n)
                (native_int_pow2 w))
              (native_int_pow2 s))
            (native_int_pow2 w)))
        (native_int_pow2 w) =
      native_mod_total
        (native_div_total (native_binary_uts w n)
          (native_int_pow2 s))
        (native_int_pow2 w) := by
  have hWNonneg : 0 <= w := by
    simpa [native_zleq, SmtEval.native_zleq] using hw0
  have hShiftRange :=
    bitvec_payload_range_of_canonical hw0 hShiftCanon
  have hs0 : 0 <= s := hShiftRange.1
  let P := native_int_pow2 w
  let d := native_int_pow2 s
  let m := native_binary_not w n
  have hPPos : 0 < P := by
    dsimp [P]
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hWNonneg
  have hdPos : 0 < d := by
    dsimp [d]
    exact EvaluateProofInternal.native_int_pow2_pos_of_nonneg hs0
  have hdGeOne : 1 <= d := (Int.add_one_le_iff).mpr hdPos
  have hMRange :
      0 <= m ∧ m < P := by
    simpa [m, P] using
      EvaluateProofInternal.native_binary_not_range_of_canonical
        (w := w) (n := n) hw0 hCanon
  have hNotMod :
      native_mod_total (native_binary_not w n) P =
        native_binary_not w n := by
    simpa [P] using
      EvaluateProofInternal.native_binary_not_mod_self_of_canonical
        (w := w) (n := n) hw0 hCanon
  let q := native_div_total m d
  have hQRange : 0 <= q ∧ q < P := by
    constructor
    · dsimp [q, native_div_total]
      exact Int.ediv_nonneg hMRange.1 (Int.le_of_lt hdPos)
    · have hPLePD : P <= P * d := by
        have hMul := Int.mul_le_mul_of_nonneg_left hdGeOne
          (Int.le_of_lt hPPos)
        simpa [Int.mul_one] using hMul
      have hMLtPD : m < P * d :=
        Int.lt_of_lt_of_le hMRange.2 hPLePD
      dsimp [q, native_div_total]
      exact Int.ediv_lt_of_lt_mul hdPos hMLtPD
  have hQMod :
      native_mod_total q P = q := by
    simpa [native_mod_total] using
      Int.emod_eq_of_lt hQRange.1 hQRange.2
  have hSignedArg :
      native_binary_uts w n = -(m + 1) := by
    have hUts :=
      EvaluateProofInternal.native_binary_uts_eq_sub_pow_of_msb_true
        (w := w) (n := n) hw0 hCanon hSign
    have hMRaw : m = P - (n + 1) := by
      dsimp [m, P]
      exact EvaluateProofInternal.native_binary_not_eq_pow_sub_succ w n
    rw [hUts, hMRaw]
    dsimp [P]
    exact EvaluateProofInternal.int_sub_eq_neg_sub_succ_add_one n (native_int_pow2 w)
  have hNegDiv :
      native_div_total (-(m + 1)) d = -(q + 1) := by
    dsimp [q, d]
    exact EvaluateProofInternal.native_neg_succ_div_pow2_eq_neg_div_succ
      (m := m) (s := s) hMRange.1 hs0
  rw [hNotMod]
  change
    native_mod_total
        (native_binary_not w
          (native_mod_total (native_div_total m d) P))
        P =
      native_mod_total
        (native_div_total (native_binary_uts w n) d) P
  rw [show native_div_total m d = q by rfl]
  rw [hQMod]
  rw [hSignedArg, hNegDiv]
  rw [EvaluateProofInternal.native_binary_not_eq_pow_sub_succ w q]
  change
    native_mod_total (P - (q + 1)) P =
      native_mod_total (-(q + 1)) P
  rw [native_mod_total, native_mod_total]
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  have hDiff : P - (q + 1) - (-(q + 1)) = P := by
    exact EvaluateProofInternal.int_sub_sub_neg_succ_eq P q
  rw [hDiff]
  simp

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div_of_msb_true
    {w n s : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hShiftCanon :
      native_zeq s
          (native_mod_total s (native_int_pow2 w)) =
        true)
    (hSign : EvaluateProofInternal.smt_bv_msb_set w n = true) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_div_total (native_binary_uts w n)
            (native_int_pow2 s))
          (native_int_pow2 w)) := by
  rw [EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_not_lshr_not_of_msb_true hSign]
  rw [EvaluateProofInternal.native_bvashr_negative_payload_eq_signed_div
    hw0 hCanon hShiftCanon hSign]

theorem EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div
    {w n s : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true)
    (hShiftCanon :
      native_zeq s
          (native_mod_total s (native_int_pow2 w)) =
        true) :
    __smtx_model_eval_bvashr (SmtValue.Binary w n) (SmtValue.Binary w s) =
      SmtValue.Binary w
        (native_mod_total
          (native_div_total (native_binary_uts w n)
            (native_int_pow2 s))
          (native_int_pow2 w)) := by
  by_cases hSignFalse : EvaluateProofInternal.smt_bv_msb_set w n = false
  · rw [EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_lshr_of_msb_false hSignFalse]
    rw [EvaluateProofInternal.native_binary_uts_eq_self_of_msb_false hw0 hCanon hSignFalse]
  · have hSignTrue : EvaluateProofInternal.smt_bv_msb_set w n = true := by
      cases hSign : EvaluateProofInternal.smt_bv_msb_set w n <;>
        simp [hSign] at hSignFalse ⊢
    exact EvaluateProofInternal.smtx_model_eval_bvashr_binary_eq_signed_div_of_msb_true
      hw0 hCanon hShiftCanon hSignTrue

