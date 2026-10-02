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

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def EvaluateProofInternal.eo_eval_sign_extend_rhs (x n : Term) : Term :=
  let bw := __bv_bitwidth (__eo_typeof x)
  let low := __eo_to_z (__eo_extract x (Term.Numeral 0)
    (__eo_add bw (Term.Numeral (-2 : native_Int))))
  let msb := __eo_add bw (Term.Numeral (-1 : native_Int))
  __eo_to_bin (__eo_add bw n)
    (__eo_ite (__eo_eq (__eo_extract x msb msb) (Term.Binary 1 1))
      (__eo_add
        (__eo_neg
          (__eo_ite (__eo_is_z msb)
            (__eo_ite (__eo_is_neg msb) (Term.Numeral 0)
              (__eo_pow (Term.Numeral 2) msb))
            (__eo_mk_apply (Term.UOp UserOp.int_pow2) msb)))
        low)
      low)

def EvaluateProofInternal.eo_signed_bv_value (x : Term) : Term :=
  let bw := __bv_bitwidth (__eo_typeof x)
  let low := __eo_to_z (__eo_extract x (Term.Numeral 0)
    (__eo_add bw (Term.Numeral (-2 : native_Int))))
  let msb := __eo_add bw (Term.Numeral (-1 : native_Int))
  __eo_ite (__eo_eq (__eo_extract x msb msb) (Term.Binary 1 1))
    (__eo_add
      (__eo_neg
        (__eo_ite (__eo_is_z msb)
          (__eo_ite (__eo_is_neg msb) (Term.Numeral 0)
            (__eo_pow (Term.Numeral 2) msb))
          (__eo_mk_apply (Term.UOp UserOp.int_pow2) msb)))
      low)
    low

def EvaluateProofInternal.eo_sign_extend_low_payload
    (w n : native_Int) : native_Int :=
  if native_zlt (native_zplus w (native_zneg 2)) 0 then
    0
  else
    native_mod_total n
      (native_int_pow2 (native_zplus w (native_zneg 1)))

def EvaluateProofInternal.eo_sign_extend_msb_set
    (w n : native_Int) : native_Bool :=
  if native_zlt (native_zplus w (native_zneg 1)) 0 then
    false
  else
    native_zeq
      (native_mod_total
        (native_div_total n
          (native_int_pow2 (native_zplus w (native_zneg 1))))
        2) 1

def EvaluateProofInternal.eo_sign_extend_payload (w n : native_Int) : native_Int :=
  if EvaluateProofInternal.eo_sign_extend_msb_set w n then
    native_zplus
      (native_zneg
        (native_int_pow2 (native_zplus w (native_zneg 1))))
      (EvaluateProofInternal.eo_sign_extend_low_payload w n)
  else
    EvaluateProofInternal.eo_sign_extend_low_payload w n

theorem EvaluateProofInternal.eo_to_bin_literal_width_of_typeof_bitvec
    (y : Term) (wi w : native_Int) :
    __eo_typeof (__eo_to_bin (Term.Numeral wi) y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    w = wi := by
  cases y <;> intro h <;>
    simp [__eo_to_bin, __eo_mk_binary, native_ite] at h
  case Numeral n =>
    cases hLe : native_zleq wi 4294967296 <;> simp [hLe] at h
    · change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · cases hNonneg : native_zleq 0 wi <;> simp [hNonneg] at h
      · change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · cases h
        rfl
  case Binary wb nb =>
    cases hLe : native_zleq wi 4294967296 <;> simp [hLe] at h
    · change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · cases hNonneg : native_zleq 0 wi <;> simp [hNonneg] at h
      · change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · cases h
        rfl
  all_goals
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_to_bin_numeral_eq_of_typeof_bitvec
    (p wi w : native_Int) :
    __eo_typeof (__eo_to_bin (Term.Numeral wi) (Term.Numeral p)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_to_bin (Term.Numeral wi) (Term.Numeral p) =
      Term.Binary wi
        (native_mod_total p (native_int_pow2 wi)) := by
  intro h
  change
    __eo_typeof
        (native_ite (native_zleq wi 4294967296)
          (__eo_mk_binary wi p) Term.Stuck) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
  cases hLe : native_zleq wi 4294967296
  · simp [hLe, native_ite] at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  · simp [hLe, native_ite, __eo_mk_binary] at h
    cases hNonneg : native_zleq 0 wi
    · simp [hNonneg] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    · simp [hNonneg] at h
      simp [__eo_to_bin, __eo_mk_binary, hLe, hNonneg, native_ite]

theorem EvaluateProofInternal.eo_eval_sign_extend_rhs_binary_of_typeof_bitvec
    (x : Term) (i w : native_Int) :
    __eo_typeof (EvaluateProofInternal.eo_eval_sign_extend_rhs x (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧ w = native_zplus wx i := by
  cases x <;> intro h
  case Binary wx nx =>
    change
      __eo_typeof
          (__eo_to_bin (Term.Numeral (native_zplus wx i)) _) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    have hW :=
      EvaluateProofInternal.eo_to_bin_literal_width_of_typeof_bitvec _
        (native_zplus wx i) w h
    exact ⟨wx, nx, rfl, hW⟩
  all_goals
    dsimp [EvaluateProofInternal.eo_eval_sign_extend_rhs] at h
    simp only [__eo_extract, __eo_eq, __eo_ite, __eo_to_bin,
      __eo_to_z] at h
    first
    | change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    | have hTrue :
          native_teq Term.Stuck (Term.Boolean true) = false := by
        native_decide
      have hFalse :
          native_teq Term.Stuck (Term.Boolean false) = false := by
        native_decide
      rw [hTrue, hFalse] at h
      simp [native_ite] at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h

theorem EvaluateProofInternal.eo_extract_literal_arg_binary_of_typeof_bitvec
    (x : Term) (i j w : native_Int)
    (hj0 : native_zleq 0 j = true)
    (hWidth : native_zlt 0
      (native_zplus (native_zplus i 1) (native_zneg j)) = true) :
    __eo_typeof (__eo_extract x (Term.Numeral j) (Term.Numeral i)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ wx : native_Int, ∃ nx : native_Int,
      x = Term.Binary wx nx ∧
        w = native_zplus (native_zplus i (native_zneg j)) 1 ∧
        __eo_extract x (Term.Numeral j) (Term.Numeral i) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1))) := by
  cases x <;> intro h
  case Binary wx nx =>
    have hjNonneg : 0 <= j := by
      simpa [native_zleq, SmtEval.native_zleq] using hj0
    have hjNotNeg : native_zlt j 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using
        Int.not_lt_of_ge hjNonneg
    have hWidthAssoc :
        native_zplus (native_zplus i 1) (native_zneg j) =
          native_zplus (native_zplus i (native_zneg j)) 1 := by
      simp [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg, Int.add_assoc, Int.add_comm,
        Int.add_left_comm]
    have hWidthPosNative :
        native_zlt 0
          (native_zplus (native_zplus i (native_zneg j)) 1) = true := by
      simpa [hWidthAssoc] using hWidth
    have hWidthNonnegNative :
        native_zleq 0
          (native_zplus (native_zplus i (native_zneg j)) 1) = true := by
      have hPos :
          (0 : native_Int) <
            native_zplus (native_zplus i (native_zneg j)) 1 := by
        simpa [native_zlt, SmtEval.native_zlt] using hWidthPosNative
      simpa [native_zleq, SmtEval.native_zleq] using Int.le_of_lt hPos
    change
      __eo_typeof
          (native_ite
            (native_or (native_zlt j 0) (native_zlt (i + -j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + -j) 1)
              (native_binary_extract wx nx i j))) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases hDeltaNeg :
        native_zlt (native_zplus i (native_zneg j)) 0
    · have hDeltaNotLt : ¬ i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact Int.not_lt.mp (of_decide_eq_false hsimpa)
      have hDeltaNonneg : 0 <= i + -j :=
        Int.le_of_not_gt hDeltaNotLt
      have hWidthNonneg : native_zleq 0 (i + -j + 1) = true := by
        have hNonneg : 0 <= i + -j + 1 :=
          Int.add_nonneg hDeltaNonneg (by decide)
        simpa [native_zleq, SmtEval.native_zleq] using hNonneg
      have hDeltaNotNegNative : native_zlt (i + -j) 0 = false := by
        simpa [native_zlt, SmtEval.native_zlt] using
          Int.not_lt_of_ge hDeltaNonneg
      simp [hjNotNeg, hDeltaNotNegNative, native_zneg, SmtEval.native_zneg,
        native_or, native_ite, __eo_mk_binary, hWidthNonneg,
        native_zplus, SmtEval.native_zplus] at h
      have hW : w = native_zplus (native_zplus i (native_zneg j)) 1 :=
        (Term.Numeral.inj ((Term.Apply.inj h).2)).symm
      refine ⟨wx, nx, rfl, hW, ?_⟩
      change
        native_ite
            (native_or (native_zlt j 0)
              (native_zlt (i + native_zneg j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + native_zneg j) 1)
              (native_binary_extract wx nx i j)) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))
      simp [hjNotNeg, hDeltaNotNegNative, hWidthNonneg,
        __eo_mk_binary, native_or, native_ite, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
    · have hDeltaLt : i + -j < 0 := by
        have hsimpa := hDeltaNeg
        try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
        exact of_decide_eq_true hsimpa
      have hWidthGe : 0 <= i + -j + 1 := by
        simpa [native_zleq, SmtEval.native_zleq, native_zplus,
          SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
          Int.add_assoc] using hWidthNonnegNative
      have hWidthZeroInt : i + -j + 1 = 0 :=
        Int.le_antisymm (Int.add_one_le_iff.mpr hDeltaLt) hWidthGe
      have hWidthZero :
          native_zplus (native_zplus i (native_zneg j)) 1 = 0 := by
        simpa [native_zplus, SmtEval.native_zplus, native_zneg,
          SmtEval.native_zneg, Int.add_assoc] using hWidthZeroInt
      have hDeltaNegNative : native_zlt (i + -j) 0 = true := by
        simpa [native_zlt, SmtEval.native_zlt] using hDeltaLt
      simp [hjNotNeg, hDeltaNegNative, native_zneg, SmtEval.native_zneg,
        native_or, native_ite, __eo_lit_type_Binary, __eo_len,
        __eo_mk_apply] at h
      have hW : w = 0 :=
        (Term.Numeral.inj ((Term.Apply.inj h).2)).symm
      refine ⟨wx, nx, rfl, hW.trans hWidthZero.symm, ?_⟩
      change
        native_ite
            (native_or (native_zlt j 0)
              (native_zlt (i + native_zneg j) 0))
            (Term.Binary 0 0)
            (__eo_mk_binary (native_zplus (i + native_zneg j) 1)
              (native_binary_extract wx nx i j)) =
          Term.Binary (native_zplus (native_zplus i (native_zneg j)) 1)
            (native_mod_total (native_binary_extract wx nx i j)
              (native_int_pow2
                (native_zplus (native_zplus i (native_zneg j)) 1)))
      simp [hjNotNeg, hDeltaNegNative, hWidthZero, native_or, native_ite,
        native_mod_total, native_int_pow2, native_zexp_total, native_zplus,
        SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
      constructor
      · exact hWidthZeroInt.symm
      · -- `rw` cannot abstract a term the `Decidable` instance depends on
        simp only [hWidthZeroInt]
        simp [native_mod_total, native_int_pow2, native_zexp_total]
  case String s =>
    change
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

theorem EvaluateProofInternal.eo_sign_extend_low_payload_eq
    (w n : native_Int) :
    __eo_to_z
        (__eo_extract (Term.Binary w n) (Term.Numeral 0)
          (Term.Numeral (native_zplus w (native_zneg 2)))) =
      Term.Numeral (EvaluateProofInternal.eo_sign_extend_low_payload w n) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 2)) 0 = true
  · have hNegPrime : native_zlt (w + -2) 0 = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNeg
    simp [__eo_extract, __eo_to_z, EvaluateProofInternal.eo_sign_extend_low_payload,
      hNegPrime, native_ite, native_or, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 2)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 2)) 0 <;>
        simp [h] at hNeg ⊢
    have hNegPrime : native_zlt (w + -2) 0 = false := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNegFalse
    have hGe : 0 <= w + -2 := by
      simpa [native_zlt, SmtEval.native_zlt] using hNegPrime
    have hNonnegPred : 0 <= w + -2 + 1 :=
      Int.add_nonneg hGe (by decide)
    have hPowArg : w + -2 + 1 = w + -1 := by
      rw [Int.add_assoc]
      have hConst : (-2 : native_Int) + 1 = -1 := by
        native_decide
      rw [hConst]
    have hLe : native_zleq 0 (w + -1) = true := by
      have hTmp : native_zleq 0 (w + -2 + 1) = true := by
        simpa [native_zleq, SmtEval.native_zleq] using hNonnegPred
      simpa [hPowArg] using hTmp
    have hDiv : native_div_total n (native_int_pow2 0) = n := by
      simp [native_div_total, native_int_pow2, native_zexp_total]
    have hZlt00 : native_zlt 0 0 = false := by
      native_decide
    simp [__eo_extract, __eo_to_z, __eo_mk_binary,
      EvaluateProofInternal.eo_sign_extend_low_payload, hNegPrime, hLe, hDiv, hPowArg,
      hZlt00, native_binary_extract, native_ite, native_or,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]

theorem EvaluateProofInternal.eo_sign_extend_msb_eq
    (w n : native_Int) :
    __eo_eq
        (__eo_extract (Term.Binary w n)
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus w (native_zneg 1))))
        (Term.Binary 1 1) =
      Term.Boolean (EvaluateProofInternal.eo_sign_extend_msb_set w n) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 1)) 0 = true
  · have hNegPrime : native_zlt (w + -1) 0 = true := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNeg
    simp [__eo_extract, __eo_eq, EvaluateProofInternal.eo_sign_extend_msb_set,
      hNegPrime, native_ite, native_or, native_teq,
      native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 1)) 0 <;>
        simp [h] at hNeg ⊢
    have hNegPrime : native_zlt (w + -1) 0 = false := by
      simpa [native_zplus, SmtEval.native_zplus, native_zneg,
        SmtEval.native_zneg] using hNegFalse
    have hDelta : w + -1 + -(w + -1) = 0 :=
      Int.add_right_neg (w + -1)
    have hWidth : w + -1 + -(w + -1) + 1 = 1 := by
      rw [hDelta]
      rfl
    have hLe1 : native_zleq 0 (1 : native_Int) = true := by
      native_decide
    have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by
      native_decide
    have hZlt00 : native_zlt 0 0 = false := by
      native_decide
    simp [__eo_extract, __eo_eq, __eo_mk_binary,
      EvaluateProofInternal.eo_sign_extend_msb_set, hNegPrime, hDelta,
      hLe1, hPow1, hZlt00, native_binary_extract,
      native_ite, native_or, native_teq, native_zeq,
      SmtEval.native_zeq, native_zplus, SmtEval.native_zplus,
      native_zneg, SmtEval.native_zneg]
    -- simp now leaves the goal as `decide _ = decide _` rather than an `Iff`
    exact decide_eq_decide.mpr ⟨fun h => h.symm, fun h => h.symm⟩

theorem EvaluateProofInternal.eo_sbv_to_int_msb_zero_eq_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    __eo_eq
        (__eo_extract (Term.Binary w n)
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus w (native_zneg 1))))
        (Term.Binary 1 0) =
      Term.Boolean
        (native_zeq
          (native_mod_total
            (native_div_total n
              (native_int_pow2 (w - 1))) 2)
          0) := by
  have hNegPrime : native_zlt (w + -1) 0 = false := by
    have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
    have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
    simpa [native_zlt, SmtEval.native_zlt, Int.sub_eq_add_neg] using
      Int.not_lt_of_ge hwp0
  have hNeg :
      native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
    simpa [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg] using hNegPrime
  have hDelta : w + -1 + -(w + -1) = 0 :=
    Int.add_right_neg (w + -1)
  have hWidth : w + -1 + -(w + -1) + 1 = 1 := by
    rw [hDelta]
    rfl
  have hLe1 : native_zleq 0 (1 : native_Int) = true := by
    native_decide
  have hPow1 : native_int_pow2 (1 : native_Int) = 2 := by
    native_decide
  have hZlt00 : native_zlt 0 0 = false := by
    native_decide
  simp [__eo_extract, __eo_eq, __eo_mk_binary, hNegPrime,
    hDelta, hLe1, hPow1, hZlt00, native_binary_extract,
    native_ite, native_or, native_teq, native_zeq,
    SmtEval.native_zeq, native_zplus, SmtEval.native_zplus,
    native_zneg, SmtEval.native_zneg, Int.sub_eq_add_neg]
  constructor <;> intro h <;> exact h.symm

theorem EvaluateProofInternal.eo_int_pow2_literal_eq (k : native_Int) :
    __eo_ite (__eo_is_z (Term.Numeral k))
      (__eo_ite (__eo_is_neg (Term.Numeral k)) (Term.Numeral 0)
        (__eo_pow (Term.Numeral 2) (Term.Numeral k)))
      (__eo_mk_apply (Term.UOp UserOp.int_pow2) (Term.Numeral k)) =
    Term.Numeral (native_int_pow2 k) := by
  by_cases hk : k < 0
  · have hlt : native_zlt k 0 = true := by
      simpa [native_zlt, SmtEval.native_zlt] using hk
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      native_ite, native_teq, native_and, native_not,
      hlt, native_int_pow2, native_zexp_total, hk]
  · have hlt : native_zlt k 0 = false := by
      simpa [native_zlt, SmtEval.native_zlt] using hk
    simp [__eo_ite, __eo_is_z, __eo_is_z_internal, __eo_is_neg,
      __eo_pow, native_ite, native_teq, native_and, native_not,
      hlt, native_int_pow2, native_zexp_total, hk]

theorem EvaluateProofInternal.eo_eval_sign_extend_rhs_binary_to_bin
    (w n i : native_Int) :
    EvaluateProofInternal.eo_eval_sign_extend_rhs (Term.Binary w n) (Term.Numeral i) =
      __eo_to_bin (Term.Numeral (native_zplus w i))
        (Term.Numeral (EvaluateProofInternal.eo_sign_extend_payload w n)) := by
  dsimp [EvaluateProofInternal.eo_eval_sign_extend_rhs]
  change
    __eo_to_bin (Term.Numeral (native_zplus w i))
      (__eo_ite
        (__eo_eq
          (__eo_extract (Term.Binary w n)
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral (native_zplus w (native_zneg 1))))
          (Term.Binary 1 1))
        (__eo_add
          (__eo_neg
            (__eo_ite
              (__eo_is_z
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (__eo_ite
                (__eo_is_neg
                  (Term.Numeral (native_zplus w (native_zneg 1))))
                (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2)
                  (Term.Numeral (native_zplus w (native_zneg 1)))))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (Term.Numeral (native_zplus w (native_zneg 1))))))
          (__eo_to_z
            (__eo_extract (Term.Binary w n) (Term.Numeral 0)
              (Term.Numeral (native_zplus w (native_zneg 2))))))
        (__eo_to_z
          (__eo_extract (Term.Binary w n) (Term.Numeral 0)
            (Term.Numeral (native_zplus w (native_zneg 2)))))) =
      _
  rw [EvaluateProofInternal.eo_sign_extend_msb_eq, EvaluateProofInternal.eo_sign_extend_low_payload_eq,
    EvaluateProofInternal.eo_int_pow2_literal_eq]
  cases hMsb : EvaluateProofInternal.eo_sign_extend_msb_set w n
  · simp [EvaluateProofInternal.eo_sign_extend_payload, hMsb, __eo_ite, native_ite,
      native_teq]
  · simp [EvaluateProofInternal.eo_sign_extend_payload, hMsb, __eo_ite, __eo_add,
      __eo_neg, native_ite, native_teq]

theorem EvaluateProofInternal.native_int_pow2_succ_pred
    {w : native_Int} (hwpos : 0 < w) :
    native_int_pow2 w = 2 * native_int_pow2 (w - 1) := by
  have hw0 : 0 <= w := Int.le_of_lt hwpos
  have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
  have hwp0 : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw0
  have hnotP : ¬ w - 1 < 0 := Int.not_lt_of_ge hwp0
  have hNat : w.toNat = (w - 1).toNat + 1 := by
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_one]
    rw [Int.toNat_of_nonneg hw0, Int.toNat_of_nonneg hwp0]
    omega
  rw [native_int_pow2, native_int_pow2, native_zexp_total,
    native_zexp_total]
  simp [hnotW, hnotP]
  rw [hNat]
  have hSub : (w - 1).toNat + 1 - 1 = (w - 1).toNat :=
    Nat.add_sub_cancel (w - 1).toNat 1
  rw [hSub]
  rw [← Nat.succ_eq_add_one]
  rw [Int.pow_succ]
  rw [Int.mul_comm]

theorem EvaluateProofInternal.native_int_pow2_add_of_nonneg
    {a b : native_Int} (ha : 0 <= a) (hb : 0 <= b) :
    native_int_pow2 (a + b) = native_int_pow2 a * native_int_pow2 b := by
  have hna : ¬ a < 0 := Int.not_lt_of_ge ha
  have hnb : ¬ b < 0 := Int.not_lt_of_ge hb
  have hab : ¬ a + b < 0 := Int.not_lt_of_ge (Int.add_nonneg ha hb)
  have hto : Int.toNat (a + b) = Int.toNat a + Int.toNat b :=
    Int.toNat_add ha hb
  rw [native_int_pow2, native_int_pow2, native_int_pow2,
    native_zexp_total, native_zexp_total, native_zexp_total]
  simp [hna, hnb, hab, hto]
  exact Int.pow_add 2 (Int.toNat a) (Int.toNat b)

theorem EvaluateProofInternal.native_int_pow2_pos_of_nonneg
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

theorem EvaluateProofInternal.native_int_pow2_lt_of_lt_nonneg
    {w k : native_Int} (hw : 0 <= w) (hlt : w < k) :
    native_int_pow2 w < native_int_pow2 k := by
  let d : native_Int := k - w
  have hdpos : 0 < d := by
    dsimp [d]
    exact Int.sub_pos.mpr hlt
  have hd : 0 <= d := Int.le_of_lt hdpos
  have hkEq : k = w + d := by
    dsimp [d]
    symm
    calc
      w + (k - w) = w + k - w := by
        rw [Int.add_sub_assoc]
      _ = k + w - w := by
        rw [Int.add_comm w k]
      _ = k := by
        rw [Int.add_sub_cancel]
  have hPow : native_int_pow2 k = native_int_pow2 w * native_int_pow2 d := by
    rw [hkEq]
    exact EvaluateProofInternal.native_int_pow2_add_of_nonneg hw hd
  have hWPos : 0 < native_int_pow2 w :=
    EvaluateProofInternal.native_int_pow2_pos_of_nonneg hw
  have hDOne : 1 < native_int_pow2 d := by
    have hnot : ¬ d < 0 := Int.not_lt_of_ge hd
    have hdNatNe : Int.toNat d ≠ 0 := by
      intro hZero
      have hdle : d <= 0 := Int.toNat_eq_zero.mp hZero
      exact (Int.not_le_of_gt hdpos) hdle
    have hNat : 1 < (2 : Nat) ^ Int.toNat d :=
      Nat.one_lt_pow hdNatNe (by decide : 1 < (2 : Nat))
    rw [native_int_pow2, native_zexp_total]
    simp [hnot]
    exact_mod_cast hNat
  rw [hPow]
  have hMul := Int.mul_lt_mul_of_pos_left hDOne hWPos
  simpa using hMul

theorem EvaluateProofInternal.native_mod_zmult_pow2_eq_zero_of_lt
    {w k x : native_Int} (hw : 0 <= w) (hlt : w < k) :
    native_mod_total (native_zmult x (native_int_pow2 k))
        (native_int_pow2 w) =
      0 := by
  let d : native_Int := k - w
  have hd : 0 <= d := by
    dsimp [d]
    exact Int.sub_nonneg.mpr (Int.le_of_lt hlt)
  have hkEq : k = w + d := by
    dsimp [d]
    symm
    calc
      w + (k - w) = w + k - w := by
        rw [Int.add_sub_assoc]
      _ = k + w - w := by
        rw [Int.add_comm w k]
      _ = k := by
        rw [Int.add_sub_cancel]
  have hPow : native_int_pow2 k = native_int_pow2 w * native_int_pow2 d := by
    rw [hkEq]
    exact EvaluateProofInternal.native_int_pow2_add_of_nonneg hw hd
  rw [hPow]
  simp [native_mod_total, native_zmult]
  have hAssoc :
      x * (native_int_pow2 w * native_int_pow2 d) =
        native_int_pow2 w * (x * native_int_pow2 d) := by
    calc
      x * (native_int_pow2 w * native_int_pow2 d) =
          (x * native_int_pow2 w) * native_int_pow2 d := by
        rw [← Int.mul_assoc]
      _ = (native_int_pow2 w * x) * native_int_pow2 d := by
        rw [Int.mul_comm x (native_int_pow2 w)]
      _ = native_int_pow2 w * (x * native_int_pow2 d) := by
        rw [Int.mul_assoc]
  rw [hAssoc]
  exact Int.mul_emod_right (native_int_pow2 w) (x * native_int_pow2 d)

theorem EvaluateProofInternal.native_mod_div_pow2_eq_zero_of_lt
    {w k x : native_Int} (hw : 0 <= w) (hlt : w < k)
    (hx0 : 0 <= x) (hxlt : x < native_int_pow2 w) :
    native_mod_total (native_div_total x (native_int_pow2 k))
        (native_int_pow2 w) =
      0 := by
  have hPowLt : native_int_pow2 w < native_int_pow2 k :=
    EvaluateProofInternal.native_int_pow2_lt_of_lt_nonneg hw hlt
  have hDivZero : native_div_total x (native_int_pow2 k) = 0 := by
    rw [native_div_total]
    exact Int.ediv_eq_zero_of_lt hx0 (Int.lt_trans hxlt hPowLt)
  rw [hDivZero]
  simp [native_mod_total]

theorem EvaluateProofInternal.eo_sign_extend_low_payload_eq_mod_of_pos
    {w n : native_Int} (hwpos : 0 < w) :
    EvaluateProofInternal.eo_sign_extend_low_payload w n =
      native_mod_total n
        (native_int_pow2 (native_zplus w (native_zneg 1))) := by
  by_cases hNeg :
      native_zlt (native_zplus w (native_zneg 2)) 0 = true
  · have hlt : w + -2 < 0 := by
      have hsimpa :=
        hNeg
      try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
      exact of_decide_eq_true hsimpa
    have hwEq : w = 1 := by
      have hlt2 : w < 2 := by
        have h := Int.add_lt_add_right hlt 2
        have hLeft : w + -2 + 2 = w := by
          rw [Int.add_assoc]
          have hc : (-2 : Int) + 2 = 0 := by
            native_decide
          rw [hc, Int.add_zero]
        have hRight : (0 : Int) + 2 = 2 := by
          rfl
        simpa [hLeft, hRight] using h
      have hle1 : w <= 1 := Int.le_of_lt_add_one hlt2
      have hge1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      exact Int.le_antisymm hle1 hge1
    subst w
    simp [EvaluateProofInternal.eo_sign_extend_low_payload, native_zplus,
      SmtEval.native_zplus, native_zneg, SmtEval.native_zneg,
      native_zlt, SmtEval.native_zlt, native_int_pow2,
      native_zexp_total, native_mod_total]
  · have hNegFalse :
        native_zlt (native_zplus w (native_zneg 2)) 0 = false := by
      cases h : native_zlt (native_zplus w (native_zneg 2)) 0 <;>
        simp [h] at hNeg ⊢
    simp [EvaluateProofInternal.eo_sign_extend_low_payload, hNegFalse]

theorem EvaluateProofInternal.sign_payload_eq_uts_core
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    (if native_zeq
          (native_mod_total
            (native_div_total n (native_int_pow2 (w - 1))) 2)
          1 then
        native_zplus (native_zneg (native_int_pow2 (w - 1)))
          (native_mod_total n (native_int_pow2 (w - 1)))
      else
        native_mod_total n (native_int_pow2 (w - 1))) =
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
    · have hSign : native_zeq (native_mod_total q 2) 1 = false := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              1 =
            false := by
        simpa [q, p] using hSign
      rw [hCond]
      change native_mod_total n p = native_binary_uts w n
      rw [native_binary_uts]
      change native_mod_total n p =
        native_zplus (native_zmult 2 (native_mod_total n p))
          (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.add_assoc]
      rw [Int.add_right_neg]
      rw [Int.add_zero]
    · have hSign : native_zeq (native_mod_total q 2) 1 = true := by
        simp [hq, native_zeq, native_mod_total]
      have hnEq : n = p + r := by
        rw [hq] at hDivMod
        simp at hDivMod
        exact hDivMod.symm
      have hCond :
          native_zeq
              (native_mod_total
                (native_div_total n (native_int_pow2 (w - 1))) 2)
              1 =
            true := by
        simpa [q, p] using hSign
      rw [hCond]
      change
        native_zplus (native_zneg p) (native_mod_total n p) =
          native_binary_uts w n
      rw [native_binary_uts]
      change
        native_zplus (native_zneg p) (native_mod_total n p) =
          native_zplus (native_zmult 2 (native_mod_total n p))
            (native_zneg n)
      rw [hnEq] at hNMod
      rw [hnEq, hNMod]
      simp [native_zplus, native_zmult, native_zneg]
      rw [Int.two_mul]
      rw [Int.neg_add]
      rw [Int.add_assoc]
      rw [show r + (-p + -r) = -p by
        calc
          r + (-p + -r) = r + (-r + -p) := by
            rw [Int.add_comm (-p) (-r)]
          _ = r + -r + -p := by
            rw [← Int.add_assoc]
          _ = 0 + -p := by
            rw [Int.add_right_neg]
          _ = -p := by
            rw [Int.zero_add]]
      rw [Int.add_comm]
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

theorem EvaluateProofInternal.eo_sign_extend_payload_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    EvaluateProofInternal.eo_sign_extend_payload w n = native_binary_uts w n := by
  by_cases hwpos : 0 < w
  · have hLow :=
      EvaluateProofInternal.eo_sign_extend_low_payload_eq_mod_of_pos
        (w := w) (n := n) hwpos
    have hMsbNeg :
        native_zlt (native_zplus w (native_zneg 1)) 0 = false := by
      have hw1 : 1 <= w := (Int.add_one_le_iff).mpr hwpos
      have hwp0Sub : 0 <= w - 1 := Int.sub_nonneg.mpr hw1
      have hwp0 : 0 <= w + -1 := by
        simpa [Int.sub_eq_add_neg] using hwp0Sub
      have hsimpa :=
        Int.not_lt_of_ge hwp0
      try simp [native_zlt, SmtEval.native_zlt, native_zplus, SmtEval.native_zplus, native_zneg, SmtEval.native_zneg] at hsimpa ⊢
      exact decide_eq_false (Int.not_lt.mpr hsimpa)
    rw [EvaluateProofInternal.eo_sign_extend_payload, EvaluateProofInternal.eo_sign_extend_msb_set, hMsbNeg,
      hLow]
    simpa [native_zplus, SmtEval.native_zplus, native_zneg,
      SmtEval.native_zneg, Int.sub_eq_add_neg] using
      EvaluateProofInternal.sign_payload_eq_uts_core (w := w) (n := n) hw0 hCanon
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

theorem EvaluateProofInternal.eo_signed_bv_value_binary_eq_uts
    {w n : native_Int}
    (hw0 : native_zleq 0 w = true)
    (hCanon :
      native_zeq n
          (native_mod_total n (native_int_pow2 w)) =
        true) :
    EvaluateProofInternal.eo_signed_bv_value (Term.Binary w n) =
      Term.Numeral (native_binary_uts w n) := by
  dsimp [EvaluateProofInternal.eo_signed_bv_value]
  change
    __eo_ite
        (__eo_eq
          (__eo_extract (Term.Binary w n)
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral (native_zplus w (native_zneg 1))))
          (Term.Binary 1 1))
        (__eo_add
          (__eo_neg
            (__eo_ite
              (__eo_is_z
                (Term.Numeral (native_zplus w (native_zneg 1))))
              (__eo_ite
                (__eo_is_neg
                  (Term.Numeral (native_zplus w (native_zneg 1))))
                (Term.Numeral 0)
                (__eo_pow (Term.Numeral 2)
                  (Term.Numeral (native_zplus w (native_zneg 1)))))
              (__eo_mk_apply (Term.UOp UserOp.int_pow2)
                (Term.Numeral (native_zplus w (native_zneg 1))))))
          (__eo_to_z
            (__eo_extract (Term.Binary w n) (Term.Numeral 0)
              (Term.Numeral (native_zplus w (native_zneg 2))))))
        (__eo_to_z
          (__eo_extract (Term.Binary w n) (Term.Numeral 0)
            (Term.Numeral (native_zplus w (native_zneg 2))))) =
      Term.Numeral (native_binary_uts w n)
  rw [EvaluateProofInternal.eo_sign_extend_msb_eq, EvaluateProofInternal.eo_sign_extend_low_payload_eq,
    EvaluateProofInternal.eo_int_pow2_literal_eq]
  cases hMsb : EvaluateProofInternal.eo_sign_extend_msb_set w n
  · rw [eo_ite_false]
    exact congrArg Term.Numeral
      (by
        simpa [EvaluateProofInternal.eo_sign_extend_payload, hMsb] using
          EvaluateProofInternal.eo_sign_extend_payload_eq_uts
            (w := w) (n := n) hw0 hCanon)
  · rw [eo_ite_true]
    simp [__eo_add, __eo_neg]
    simpa [EvaluateProofInternal.eo_sign_extend_payload, hMsb] using
      EvaluateProofInternal.eo_sign_extend_payload_eq_uts
        (w := w) (n := n) hw0 hCanon

theorem EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary
    (x : Term)
    (hNotBinary : ¬ ∃ w n : native_Int, x = Term.Binary w n)
    (hNotString : ¬ ∃ s : native_String, x = Term.String s) :
    EvaluateProofInternal.eo_signed_bv_value x = Term.Stuck := by
  cases x
  case String s =>
    exact False.elim (hNotString ⟨s, rfl⟩)
  case Binary w n =>
    exact False.elim (hNotBinary ⟨w, n, rfl⟩)
  all_goals
    simp [EvaluateProofInternal.eo_signed_bv_value, __eo_extract, __eo_eq, __eo_ite,
      native_ite, native_teq] at hNotBinary ⊢

theorem EvaluateProofInternal.eo_signed_bv_value_arg_ne_stuck {x : Term} :
    EvaluateProofInternal.eo_signed_bv_value x ≠ Term.Stuck -> x ≠ Term.Stuck := by
  intro h hx
  have hNotBinary : ¬ ∃ w n : native_Int, x = Term.Binary w n := by
    intro hBin
    rcases hBin with ⟨w, n, hEq⟩
    rw [hEq] at hx
    cases hx
  have hNotString : ¬ ∃ s : native_String, x = Term.String s := by
    intro hStr
    rcases hStr with ⟨s, hEq⟩
    rw [hEq] at hx
    cases hx
  exact h (EvaluateProofInternal.eo_signed_bv_value_eq_stuck_of_not_binary x hNotBinary hNotString)

