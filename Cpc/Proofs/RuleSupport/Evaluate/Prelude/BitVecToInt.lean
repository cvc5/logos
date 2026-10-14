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

theorem EvaluateProofInternal.sbv_to_int_payload_eq_uts_core
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    (if native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          0 then
        n
      else
        native_zplus n (native_zneg (native_int_pow2 w))) =
      native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · let p := native_int_pow2 (w - 1)
    let q := native_div_total n p
    let r := native_mod_total n p
    have hpPos : 0 < p := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hnot : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
      simp [p, native_int_pow2, native_zexp_total, hnot]
      exact Int.pow_pos (by decide)
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
    have hNMod : native_mod_total n p = r := by
      rfl
    rcases hqCases with hq | hq
    · have hSignZero : native_zeq (native_mod_total q 2) 0 = true := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              0 =
            true := by
        simpa [q, p] using hSignZero
      rw [hCond]
      change n = native_binary_uts w n
      rw [native_binary_uts]
      change n =
        native_zplus (native_zmult 2 (native_mod_total n p))
          (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.add_assoc]
      rw [Int.add_right_neg]
      rw [Int.add_zero]
    · have hSignZero : native_zeq (native_mod_total q 2) 0 = false := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = p + r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              0 =
            false := by
        simpa [q, p] using hSignZero
      rw [hCond]
      change
        native_zplus n (native_zneg (native_int_pow2 w)) =
          native_binary_uts w n
      rw [native_binary_uts, hPow]
      change
        native_zplus n (native_zneg (2 * p)) =
          native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      have hLeftCancel :
          p + r + (-p + -p) = r + -p := by
        have hCancel : p + r + -p = r := by
          calc
            p + r + -p = p + (r + -p) := by rw [Int.add_assoc]
            _ = p + (-p + r) := by rw [Int.add_comm r (-p)]
            _ = p + -p + r := by rw [← Int.add_assoc]
            _ = r := by rw [Int.add_right_neg, Int.zero_add]
        calc
          p + r + (-p + -p) = p + r + -p + -p := by
            rw [← Int.add_assoc]
          _ = r + -p := by rw [hCancel]
      have hRightCancel :
          r + r + (-p + -r) = r + -p := by
        have hCancel : r + r + -r = r := by
          calc
            r + r + -r = r + (r + -r) := by rw [Int.add_assoc]
            _ = r := by rw [Int.add_right_neg, Int.add_zero]
        calc
          r + r + (-p + -r) = r + r + (-r + -p) := by
            rw [Int.add_comm (-p) (-r)]
          _ = r + r + -r + -p := by
            rw [← Int.add_assoc]
          _ = r + -p := by rw [hCancel]
      calc
        p + r + -(2 * p) = p + r + -(p + p) := by
          rw [Int.two_mul]
        _ = p + r + (-p + -p) := by
          rw [Int.neg_add]
        _ = r + -p := hLeftCancel
        _ = r + r + (-p + -r) := hRightCancel.symm
        _ = 2 * r + -(p + r) := by
          rw [Int.two_mul, Int.neg_add]
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

def EvaluateProofInternal.eo_eval_sbv_to_int_rhs (x : Term) : Term :=
  let _v0 := __run_evaluate x
  let _v1 := __bv_bitwidth (__eo_typeof _v0)
  let _v2 := __eo_to_z _v0
  let _v3 :=
    __eo_add (__bv_bitwidth (__eo_typeof x))
      (Term.Numeral (-1 : native_Int))
  __eo_ite (__eo_eq _v1 (Term.Numeral 0)) (Term.Numeral 0)
    (__eo_ite
      (__eo_eq (__eo_extract x _v3 _v3) (Term.Binary 1 0))
      _v2
      (__eo_add _v2
        (__eo_neg
          (__eo_ite (__eo_is_z _v1)
            (__eo_ite (__eo_is_neg _v1) (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) _v1))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2) _v1)))))

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_binary_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true) :
    EvaluateProofInternal.eo_eval_sbv_to_int_rhs (Term.Binary w n) =
      Term.Numeral (native_binary_uts w n) := by
  by_cases hwz : w = 0
  · subst w
    have hRange := bitvec_payload_range_of_canonical hw0 hCanon
    have hPow0 : native_int_pow2 0 = 1 := by
      native_decide
    have hnEq : n = 0 := by
      have hlt : n < 1 := by
        simpa [hPow0] using hRange.2
      exact Int.le_antisymm (Int.le_of_lt_add_one hlt) hRange.1
    subst n
    native_decide
  · have hw0Int : 0 <= w := by
      simpa [native_zleq, SmtEval.native_zleq] using hw0
    have hwpos : 0 < w := by
      rcases Int.lt_or_eq_of_le hw0Int with hlt | heq
      · exact hlt
      · exact False.elim (hwz heq.symm)
    have hEqW0 :
        __eo_eq (Term.Numeral w) (Term.Numeral 0) =
          Term.Boolean false := by
      have h0w : ¬ (0 : native_Int) = w := by
        intro h
        exact hwz h.symm
      simp [__eo_eq, native_teq, h0w]
    have hPowExpr :
        __eo_ite (__eo_is_z (Term.Numeral w))
          (__eo_ite (__eo_is_neg (Term.Numeral w)) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) (Term.Numeral w)))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral w)) =
        Term.Numeral (native_int_pow2 w) :=
      EvaluateProofInternal.eo_int_pow2_literal_eq w
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    change
      __eo_ite (__eo_eq (Term.Numeral w) (Term.Numeral 0))
          (Term.Numeral 0)
          (__eo_ite
            (__eo_eq
              (__eo_extract (Term.Binary w n)
                (Term.Numeral (native_zplus w (native_zneg 1)))
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (Term.Binary 1 0))
            (Term.Numeral n)
            (__eo_add (Term.Numeral n)
              (__eo_neg
                (__eo_ite (__eo_is_z (Term.Numeral w))
                  (__eo_ite (__eo_is_neg (Term.Numeral w))
                    (Term.Numeral 0)
                    (__eo_pow (Term.Numeral 2) (Term.Numeral w)))
                  (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                    (Term.Numeral w)))))) =
        Term.Numeral (native_binary_uts w n)
    rw [hEqW0, eo_ite_false,
      EvaluateProofInternal.eo_sbv_to_int_msb_zero_eq_of_pos (w := w) (n := n) hwpos]
    cases hSignZero :
        native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          0
    · rw [eo_ite_false, hPowExpr]
      simp [__eo_add, __eo_neg]
      simpa [hSignZero] using
        EvaluateProofInternal.sbv_to_int_payload_eq_uts_core
          (w := w) (n := n) hw0 hCanon
    · rw [eo_ite_true]
      exact congrArg Term.Numeral
        (by
          simpa [hSignZero] using
            EvaluateProofInternal.sbv_to_int_payload_eq_uts_core
              (w := w) (n := n) hw0 hCanon)

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_arg_binary_of_pos_typeof_int
    (x : Term) {w n : native_Int}
    (hRun : __run_evaluate x = Term.Binary w n)
    (hwpos : 0 < w)
    (hTy : __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
      Term.UOp UserOp.Int) :
    x = Term.Binary w n := by
  have hEqW0 :
      __eo_eq (Term.Numeral w) (Term.Numeral 0) =
        Term.Boolean false := by
    have hwz : ¬ w = 0 := by
      intro h
      subst w
      exact (by native_decide : ¬ (0 : native_Int) < 0) hwpos
    have h0w : ¬ (0 : native_Int) = w := by
      intro h
      exact hwz h.symm
    simp [__eo_eq, native_teq, h0w]
  have hRunGuard :
      __eo_eq (__bv_bitwidth (__eo_typeof (Term.Binary w n)))
          (Term.Numeral 0) =
        Term.Boolean false := by
    change __eo_eq (Term.Numeral w) (Term.Numeral 0) =
      Term.Boolean false
    exact hEqW0
  cases x
  case Binary wx nx =>
    change Term.Binary wx nx = Term.Binary w n
    change Term.Binary wx nx = Term.Binary w n at hRun
    exact hRun
  case String s =>
    change Term.String s = Term.Binary w n at hRun
    cases hRun
  all_goals
    exfalso
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs] at hTy
    rw [hRun, hRunGuard, eo_ite_false] at hTy
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq] at hTy
    change Term.Stuck = Term.UOp UserOp.Int at hTy
    cases hTy

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_eq_zero_of_run_typeof_zero
    (x : Term)
    (hRunTy :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) :
    EvaluateProofInternal.eo_eval_sbv_to_int_rhs x = Term.Numeral 0 := by
  dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
  rw [hRunTy]
  rfl

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_arg_binary_of_pos_run_typeof_int
    (x : Term) {k : native_Int}
    (hRunTy :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k))
    (hkpos : 0 < k)
    (hTy : __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
      Term.UOp UserOp.Int) :
    ∃ w n : native_Int, x = Term.Binary w n := by
  have hGuard :
      __eo_eq (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
          (Term.Numeral 0) =
        Term.Boolean false := by
    rw [hRunTy]
    have hkz : ¬ k = 0 := by
      intro h
      subst k
      exact (by native_decide : ¬ (0 : native_Int) < 0) hkpos
    have h0k : ¬ (0 : native_Int) = k := by
      intro h
      exact hkz h.symm
    simp [__bv_bitwidth, __eo_eq, native_teq, h0k]
  cases x
  case Binary w n =>
    exact ⟨w, n, rfl⟩
  case String s =>
    exfalso
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs] at hTy
    rw [hGuard, eo_ite_false] at hTy
    have hIdx :
        __eo_add (__bv_bitwidth (__eo_typeof (Term.String s)))
            (Term.Numeral (-1 : native_Int)) =
          Term.Stuck := by
      rfl
    rw [hIdx] at hTy
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq] at hTy
    change Term.Stuck = Term.UOp UserOp.Int at hTy
    cases hTy
  all_goals
    exfalso
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs] at hTy
    rw [hGuard, eo_ite_false] at hTy
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq] at hTy
    change Term.Stuck = Term.UOp UserOp.Int at hTy
    cases hTy

theorem EvaluateProofInternal.eo_eval_sbv_to_int_rhs_typeof_int_of_pos_run_typeof
    (x : Term) {k : native_Int}
    (hRunTy :
      __eo_typeof (__run_evaluate x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k))
    (hkpos : 0 < k)
    (hNe : EvaluateProofInternal.eo_eval_sbv_to_int_rhs x ≠ Term.Stuck) :
    __eo_typeof (EvaluateProofInternal.eo_eval_sbv_to_int_rhs x) =
      Term.UOp UserOp.Int := by
  have hGuard :
      __eo_eq (__bv_bitwidth (__eo_typeof (__run_evaluate x)))
          (Term.Numeral 0) =
        Term.Boolean false := by
    rw [hRunTy]
    have hkz : ¬ k = 0 := by
      intro h
      subst k
      exact (by native_decide : ¬ (0 : native_Int) < 0) hkpos
    have h0k : ¬ (0 : native_Int) = k := by
      intro h
      exact hkz h.symm
    simp [__bv_bitwidth, __eo_eq, native_teq, h0k]
  cases x
  case Binary w n =>
    have hwpos : 0 < w := by
      change
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k) at hRunTy
      cases hRunTy
      exact hkpos
    have hNeg : native_zlt w 0 = false := by
      rw [show native_zlt w 0 = decide (w < 0) by rfl]
      exact decide_eq_false (Int.not_lt.mpr (Int.le_of_lt hwpos))
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    rw [hGuard, eo_ite_false]
    cases hSign :
        __eo_eq
            (__eo_extract (Term.Binary w n)
              (__eo_add (__bv_bitwidth (__eo_typeof (Term.Binary w n)))
                (Term.Numeral (-1 : native_Int)))
              (__eo_add (__bv_bitwidth (__eo_typeof (Term.Binary w n)))
                (Term.Numeral (-1 : native_Int))))
            (Term.Binary 1 0)
    case Boolean b =>
      cases b
      · change
          __eo_typeof
              (__eo_add (Term.Numeral n)
                (__eo_neg
                  (__eo_ite (__eo_is_z (Term.Numeral w))
                    (__eo_ite (__eo_is_neg (Term.Numeral w))
                      (Term.Numeral 0)
                      (__eo_pow (Term.Numeral 2) (Term.Numeral w)))
                    (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                      (Term.Numeral w))))) =
            Term.UOp UserOp.Int
        simp [__eo_ite, native_ite, native_teq, __eo_is_z,
          __eo_is_z_internal, __eo_is_neg, __eo_neg, __eo_add,
          __eo_pow, __eo_mk_apply, native_and, native_not, hNeg]
        change __eo_lit_type_Numeral (Term.Numeral _) =
          Term.UOp UserOp.Int
        rfl
      · change __eo_typeof (Term.Numeral n) = Term.UOp UserOp.Int
        rfl
    all_goals
      exfalso
      apply hNe
      dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
      rw [hGuard, eo_ite_false]
      simp [__eo_ite, hSign, native_ite, native_teq]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral k) at hRunTy
    cases hRunTy
  all_goals
    exfalso
    apply hNe
    dsimp [EvaluateProofInternal.eo_eval_sbv_to_int_rhs]
    rw [hGuard, eo_ite_false]
    simp [__eo_extract, __eo_eq, __eo_ite, native_ite, native_teq]

