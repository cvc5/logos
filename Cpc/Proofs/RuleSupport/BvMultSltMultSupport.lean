module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport
public import Cpc.Proofs.Rules.Evaluate
import all Cpc.Proofs.Rules.Evaluate

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

/-! Shared support for the two multiplication/comparison rewrites. -/

private theorem mul_lt_mul_characterization (x y a : Int) :
    y * a < x * a ↔
      y ≠ x ∧ a ≠ 0 ∧ ((y < x) ↔ (a > 0)) := by
  constructor
  · intro h
    rcases Int.lt_trichotomy a 0 with haNeg | haZero | haPos
    · have hxy : x < y := (Int.mul_lt_mul_right_of_neg haNeg).mp h
      exact ⟨by omega, by omega, by simp [show ¬y < x by omega,
        show ¬a > 0 by omega]⟩
    · subst a
      simp at h
    · have hyx : y < x := (Int.mul_lt_mul_right haPos).mp h
      exact ⟨by omega, by omega, by simp [hyx, haPos]⟩
  · rintro ⟨hyx, ha, hSigns⟩
    by_cases hy : y < x
    · have haPos : a > 0 := by
        simpa [hy] using hSigns.symm
      exact (Int.mul_lt_mul_right haPos).mpr hy
    · have hxy : x < y := by omega
      have haNotPos : ¬a > 0 := by
        simpa [hy] using hSigns.symm
      have haNeg : a < 0 := by omega
      exact (Int.mul_lt_mul_right_of_neg haNeg).mpr hxy

private theorem int_mul_bounds_of_natAbs
    {x y : Int} {s t : Nat} (hx : x.natAbs ≤ s) (hy : y.natAbs ≤ t) :
    -((s * t : Nat) : Int) ≤ x * y ∧ x * y ≤ ((s * t : Nat) : Int) := by
  have hUpper := Int.mul_le_mul_of_natAbs_le hx hy
  have hLower := Int.mul_le_mul_of_natAbs_le
    (x := -x) (y := y) (s := s) (t := t) (by simpa) hy
  have hLower' : -(x * y) ≤ ((s * t : Nat) : Int) := by
    simpa [Int.neg_mul] using hLower
  exact ⟨by omega, hUpper⟩

private theorem signed_product_fits
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x : BitVec T) (a : BitVec U) :
    -(2 : Int) ^ (W - 1) ≤ x.toInt * a.toInt ∧
      x.toInt * a.toInt < (2 : Int) ^ (W - 1) := by
  rcases T with _ | t
  · simp only [BitVec.of_length_zero, BitVec.toInt_zero, Int.zero_mul]
    exact ⟨Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide)),
      Int.pow_pos (by decide)⟩
  rcases U with _ | u
  · simp only [BitVec.of_length_zero, BitVec.toInt_zero, Int.mul_zero]
    exact ⟨Int.neg_nonpos_of_nonneg (Int.pow_nonneg (by decide)),
      Int.pow_pos (by decide)⟩
  have hxLo := BitVec.le_two_mul_toInt (x := x)
  have hxHi := BitVec.two_mul_toInt_lt (x := x)
  have haLo := BitVec.le_two_mul_toInt (x := a)
  have haHi := BitVec.two_mul_toInt_lt (x := a)
  have hPowT : (2 : Int) ^ (t + 1) = 2 * (2 : Int) ^ t := by
    rw [Int.pow_succ]
    omega
  have hPowU : (2 : Int) ^ (u + 1) = 2 * (2 : Int) ^ u := by
    rw [Int.pow_succ]
    omega
  rw [hPowT] at hxLo hxHi
  rw [hPowU] at haLo haHi
  have hPowCastT : ((2 ^ t : Nat) : Int) = (2 : Int) ^ t := by norm_cast
  have hPowCastU : ((2 ^ u : Nat) : Int) = (2 : Int) ^ u := by norm_cast
  have hxAbs : x.toInt.natAbs ≤ 2 ^ t := by
    apply Int.ofNat_le.1
    rw [hPowCastT]
    by_cases hx : 0 ≤ x.toInt
    · rw [Int.natAbs_of_nonneg hx]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  have haAbs : a.toInt.natAbs ≤ 2 ^ u := by
    apply Int.ofNat_le.1
    rw [hPowCastU]
    by_cases ha : 0 ≤ a.toInt
    · rw [Int.natAbs_of_nonneg ha]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  have hMulBounds := int_mul_bounds_of_natAbs hxAbs haAbs
  have hPowMul : (2 ^ t * 2 ^ u : Nat) = 2 ^ (t + u) := by
    rw [← Nat.pow_add]
  rw [hPowMul] at hMulBounds
  have hAbsMul : -(2 : Int) ^ (t + u) ≤ x.toInt * a.toInt ∧
      x.toInt * a.toInt ≤ (2 : Int) ^ (t + u) := by
    exact_mod_cast hMulBounds
  have hPowLt : (2 : Int) ^ (t + u) < (2 : Int) ^ (W - 1) := by
    have hPowLtNat : (2 : Nat) ^ (t + u) < 2 ^ (W - 1) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    exact_mod_cast hPowLtNat
  exact ⟨Int.le_trans (Int.neg_le_neg (Int.le_of_lt hPowLt)) hAbsMul.1,
    Int.lt_of_le_of_lt hAbsMul.2 hPowLt⟩

private theorem unsigned_signed_product_fits
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x : BitVec T) (a : BitVec U) :
    -(2 : Int) ^ (W - 1) ≤ (x.toNat : Int) * a.toInt ∧
      (x.toNat : Int) * a.toInt < (2 : Int) ^ (W - 1) := by
  rcases T with _ | t
  · simp [BitVec.of_length_zero]
    have hNonneg : 0 ≤ (2 : Int) ^ (W - 1) := Int.pow_nonneg (by decide)
    have hPos : 0 < (2 : Int) ^ (W - 1) := Int.pow_pos (by decide)
    exact ⟨hNonneg, hPos⟩
  rcases U with _ | u
  · simp [BitVec.of_length_zero]
    have hNonneg : 0 ≤ (2 : Int) ^ (W - 1) := Int.pow_nonneg (by decide)
    have hPos : 0 < (2 : Int) ^ (W - 1) := Int.pow_pos (by decide)
    exact ⟨hNonneg, hPos⟩
  have hx0 : (0 : Int) ≤ x.toNat := Int.natCast_nonneg _
  have hxHiNat := x.isLt
  have hxHi : (x.toNat : Int) < (2 : Int) ^ (t + 1) := by exact_mod_cast hxHiNat
  have haLo := BitVec.le_two_mul_toInt (x := a)
  have haHi := BitVec.two_mul_toInt_lt (x := a)
  have hPowU : (2 : Int) ^ (u + 1) = 2 * (2 : Int) ^ u := by
    rw [Int.pow_succ]
    omega
  rw [hPowU] at haLo haHi
  have hPowCastU : ((2 ^ u : Nat) : Int) = (2 : Int) ^ u := by norm_cast
  have haAbs : a.toInt.natAbs ≤ 2 ^ u := by
    apply Int.ofNat_le.1
    rw [hPowCastU]
    by_cases ha : 0 ≤ a.toInt
    · rw [Int.natAbs_of_nonneg ha]
      omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega)]
      omega
  have hxAbs : ((x.toNat : Int).natAbs) < 2 ^ (t + 1) := by
    simpa using hxHiNat
  have hMulAbs : ((x.toNat : Int) * a.toInt).natAbs <
      2 ^ (t + u + 1) := by
    rw [Int.natAbs_mul]
    by_cases ha0 : a.toInt.natAbs = 0
    · simp [ha0, Nat.two_pow_pos]
    · have h1 := Nat.mul_lt_mul_of_pos_right hxAbs (Nat.pos_of_ne_zero ha0)
      have h2 := Nat.mul_le_mul_left (2 ^ (t + 1)) haAbs
      have hPow : 2 ^ (t + 1) * 2 ^ u = 2 ^ (t + u + 1) := by
        rw [← Nat.pow_add]
        rw [show t + 1 + u = t + u + 1 by omega]
      rw [hPow] at h2
      exact Nat.lt_of_lt_of_le h1 h2
  have hTargetNat : 2 ^ (t + u + 1) ≤ 2 ^ (W - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hMulAbsTarget : ((x.toNat : Int) * a.toInt).natAbs < 2 ^ (W - 1) :=
    Nat.lt_of_lt_of_le hMulAbs hTargetNat
  have hAbsCast :
      (((((x.toNat : Int) * a.toInt).natAbs) : Nat) : Int) <
        (2 : Int) ^ (W - 1) := by
    exact_mod_cast hMulAbsTarget
  have hNatAbsBounds := Int.natAbs_eq ((x.toNat : Int) * a.toInt)
  rcases hNatAbsBounds with hPos | hNeg
  · rw [hPos]
    constructor <;> omega
  · rw [hNeg]
    constructor <;> omega

private theorem bitvec_sub_ne_zero_iff {W : Nat} (x y : BitVec W) :
    y - x ≠ 0#W ↔ y ≠ x := by
  constructor
  · intro hSub hEq
    subst y
    exact hSub (by simp)
  · intro hNe hSub
    have hEq : y = x := by
      have h := (BitVec.sub_eq_iff_eq_add).mp hSub
      simpa using h
    exact hNe hEq

private theorem bitvec_toInt_ne_iff {W : Nat} (x y : BitVec W) :
    x.toInt ≠ y.toInt ↔ x ≠ y :=
  not_congr BitVec.toInt_inj

private theorem bitvec_toInt_ne_zero_iff {W : Nat} (x : BitVec W) :
    x.toInt ≠ 0 ↔ x ≠ 0#W := by
  simpa only [BitVec.toInt_zero] using bitvec_toInt_ne_iff x 0#W

private theorem bitvec_natcast_ne_iff {W : Nat} (x y : BitVec W) :
    (x.toNat : Int) ≠ (y.toNat : Int) ↔ x ≠ y := by
  constructor
  · intro hxy hEq
    subst y
    exact hxy rfl
  · intro hxy hNat
    apply hxy
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast hNat

private theorem signed_bitvec_mult_slt_iff
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    (y.signExtend W * a.signExtend W).slt
        (x.signExtend W * a.signExtend W) ↔
      y ≠ x ∧ a ≠ 0#U ∧
        ((y.slt x) = ((0#U).slt a)) := by
  have hyFit := signed_product_fits hWPos hWidth y a
  have hxFit := signed_product_fits hWPos hWidth x a
  have hyProd :
      (y.signExtend W * a.signExtend W).toInt = y.toInt * a.toInt := by
    change (BitVec.ofInt W y.toInt * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hyFit.1 hyFit.2
  have hxProd :
      (x.signExtend W * a.signExtend W).toInt = x.toInt * a.toInt := by
    change (BitVec.ofInt W x.toInt * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hxFit.1 hxFit.2
  rw [BitVec.slt_iff_toInt_lt, hyProd, hxProd,
    mul_lt_mul_characterization]
  simp only [BitVec.slt_eq_decide, BitVec.toInt_zero, decide_eq_decide,
    bitvec_toInt_ne_iff, bitvec_toInt_ne_zero_iff]

private theorem unsigned_bitvec_mult_slt_iff
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    (y.zeroExtend W * a.signExtend W).slt
        (x.zeroExtend W * a.signExtend W) ↔
      y ≠ x ∧ a ≠ 0#U ∧
        ((y.ult x) = ((0#U).slt a)) := by
  have hyFit := unsigned_signed_product_fits hWPos hWidth y a
  have hxFit := unsigned_signed_product_fits hWPos hWidth x a
  have hyProd :
      (y.zeroExtend W * a.signExtend W).toInt = (y.toNat : Int) * a.toInt := by
    have hyZero : y.zeroExtend W = BitVec.ofInt W (y.toNat : Int) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend_eq_setWidth,
        BitVec.toNat_setWidth_of_le (b := y) (w' := W) (by omega)]
      have hPow : (2 : Nat) ^ T ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      rw [ofInt_toNat_canonical W (y.toNat : Int)
        (Int.natCast_nonneg _)
        (by exact_mod_cast Nat.lt_of_lt_of_le y.isLt hPow)]
      simp
    rw [hyZero]
    change (BitVec.ofInt W (y.toNat : Int) * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hyFit.1 hyFit.2
  have hxProd :
      (x.zeroExtend W * a.signExtend W).toInt = (x.toNat : Int) * a.toInt := by
    have hxZero : x.zeroExtend W = BitVec.ofInt W (x.toNat : Int) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.zeroExtend_eq_setWidth,
        BitVec.toNat_setWidth_of_le (b := x) (w' := W) (by omega)]
      have hPow : (2 : Nat) ^ T ≤ 2 ^ W :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      rw [ofInt_toNat_canonical W (x.toNat : Int)
        (Int.natCast_nonneg _)
        (by exact_mod_cast Nat.lt_of_lt_of_le x.isLt hPow)]
      simp
    rw [hxZero]
    change (BitVec.ofInt W (x.toNat : Int) * BitVec.ofInt W a.toInt).toInt = _
    rw [← BitVec.ofInt_mul]
    exact BitVec.toInt_ofInt_eq_self hWPos hxFit.1 hxFit.2
  rw [BitVec.slt_iff_toInt_lt, hyProd, hxProd,
    mul_lt_mul_characterization]
  simp only [BitVec.ult_eq_decide, BitVec.slt_eq_decide,
    BitVec.toInt_zero, decide_eq_decide]
  have hCastLt : ((y.toNat : Int) < x.toNat) = (y.toNat < x.toNat) := by
    exact propext Int.ofNat_lt
  rw [hCastLt]
  simp only [bitvec_natcast_ne_iff, bitvec_toInt_ne_zero_iff]

private theorem bvslt_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvslt
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.slt y) := by
  have hW0 : native_zleq 0 (W : Int) = true := by
    simpa [SmtEval.native_zleq] using Int.natCast_nonneg W
  have hWCast : (W : Int) = native_nat_to_int W := by
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  have hXCanon : native_zeq (x.toNat : Int)
      (native_mod_total (x.toNat : Int) (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_nat W]
    have hMod : (x.toNat : Int) % (2 ^ W : Nat) = x.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast x.isLt)
    have hsimpa := hMod.symm
    try simp [SmtEval.native_zeq, SmtEval.native_mod_total] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hYCanon : native_zeq (y.toNat : Int)
      (native_mod_total (y.toNat : Int) (native_int_pow2 (W : Int))) = true := by
    rw [hWCast]
    rw [native_int_pow2_nat W]
    have hMod : (y.toNat : Int) % (2 ^ W : Nat) = y.toNat := by
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
        (by exact_mod_cast y.isLt)
    have hsimpa := hMod.symm
    try simp [SmtEval.native_zeq, SmtEval.native_mod_total] at hsimpa ⊢
    exact decide_eq_true hsimpa
  unfold __smtx_model_eval_bvslt
  rw [smtx_model_eval_bvsgt_binary_eq_uts_public hW0 hYCanon hXCanon]
  rw [native_binary_uts_eq_bitvec_toInt W (x.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt),
    native_binary_uts_eq_bitvec_toInt W (y.toNat : Int)
      (Int.natCast_nonneg _)
      (by exact_mod_cast y.isLt)]
  rw [bitvec_ofInt_natCast_toNat, bitvec_ofInt_natCast_toNat]
  rfl

private theorem bvult_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvult
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (x.ult y) := by
  change SmtValue.Boolean (decide ((x.toNat : Int) < y.toNat)) = _
  congr 2
  exact propext Int.ofNat_lt

private theorem bvsub_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvsub
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Binary (W : Int) ((x - y).toNat : Int) := by
  change SmtValue.Binary (W : Int)
      (native_mod_total
        (native_zplus (x.toNat : Int)
          (native_mod_total (native_zneg (y.toNat : Int))
            (native_int_pow2 (W : Int))))
        (native_int_pow2 (W : Int))) = _
  congr 2
  have hWCast : (W : Int) = native_nat_to_int W := by
    simp [native_nat_to_int, Smtm.native_nat_to_int]
  rw [hWCast]
  rw [native_int_pow2_nat W]
  simp only [SmtEval.native_zplus, SmtEval.native_zneg,
    SmtEval.native_mod_total]
  rw [Int.add_emod_emod]
  have hSub : x - y =
      BitVec.ofInt W ((x.toNat : Int) - (y.toNat : Int)) := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      bitvec_ofInt_natCast_toNat, bitvec_ofInt_natCast_toNat,
      BitVec.sub_eq_add_neg]
  rw [hSub, BitVec.toNat_ofInt]
  have hPowPos : (0 : Int) < (2 ^ W : Nat) := by
    exact_mod_cast Nat.two_pow_pos W
  have hNonneg : 0 ≤ ((x.toNat : Int) + -(y.toNat : Int)) % (2 ^ W : Nat) :=
    Int.emod_nonneg _ (Int.ne_of_gt hPowPos)
  rw [Int.sub_eq_add_neg]
  rw [Int.toNat_of_nonneg hNonneg]
  norm_cast

private theorem zero_extend_val_bitvec_local
    (W K : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_model_eval_zero_extend (SmtValue.Numeral (K : Int))
        (SmtValue.Binary (W : Int) p) =
      SmtValue.Binary ((K + W : Nat) : Int)
        ((BitVec.ofInt W p).zeroExtend (K + W) |>.toNat : Int) := by
  have hWidth : (K : Int) + W = ((K + W : Nat) : Int) := by norm_cast
  have hPayload : (BitVec.ofInt W p).toNat = p.toNat :=
    ofInt_toNat_canonical W p hp0 hp1
  simp only [__smtx_model_eval_zero_extend, SmtEval.native_zplus,
    SmtEval.native_mod_total]
  rw [hWidth]
  congr 2
  rw [BitVec.zeroExtend_eq_setWidth,
    BitVec.toNat_setWidth_of_le (by omega), hPayload]
  exact (Int.toNat_of_nonneg hp0).symm

private theorem bvsgt_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvsgt
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Boolean (y.slt x) := by
  simpa [__smtx_model_eval_bvslt] using bvslt_bitvec_values y x

private theorem bvmul_bitvec_values_local {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvmul
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Binary (W : Int) ((x * y).toNat : Int) := by
  change SmtValue.Binary (W : Int)
      (native_mod_total
        (native_zmult (x.toNat : Int) (y.toNat : Int))
        (native_int_pow2 (W : Int))) = _
  congr 2

theorem bvMultSlt_bvmul_bitvec_values {W : Nat} (x y : BitVec W) :
    __smtx_model_eval_bvmul
        (SmtValue.Binary (W : Int) (x.toNat : Int))
        (SmtValue.Binary (W : Int) (y.toNat : Int)) =
      SmtValue.Binary (W : Int) ((x * y).toNat : Int) :=
  bvmul_bitvec_values_local x y

private theorem signed_mult_smt_values
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    __smtx_model_eval_eq
        (__smtx_model_eval_bvslt
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((y.signExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int))))
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((x.signExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int)))))
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval_eq
              (__smtx_model_eval_bvsub
                (SmtValue.Binary (T : Int) (y.toNat : Int))
                (SmtValue.Binary (T : Int) (x.toNat : Int)))
              (SmtValue.Binary (T : Int) ((0#T).toNat : Int))))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval_eq
                (SmtValue.Binary (U : Int) (a.toNat : Int))
                (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
            (__smtx_model_eval_and
              (__smtx_model_eval_eq
                (__smtx_model_eval_bvslt
                  (SmtValue.Binary (T : Int) (y.toNat : Int))
                  (SmtValue.Binary (T : Int) (x.toNat : Int)))
                (__smtx_model_eval_bvsgt
                  (SmtValue.Binary (U : Int) (a.toNat : Int))
                  (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
              (SmtValue.Boolean true)))) =
      SmtValue.Boolean true := by
  rw [bvmul_bitvec_values_local (a.signExtend W) 1#W]
  simp only [BitVec.mul_one]
  rw [bvmul_bitvec_values_local (y.signExtend W) (a.signExtend W)]
  rw [bvmul_bitvec_values_local (x.signExtend W) (a.signExtend W),
    bvslt_bitvec_values]
  rw [bvsub_bitvec_values, bvslt_bitvec_values, bvsgt_bitvec_values]
  simp [-BitVec.toNat_sub, __smtx_model_eval_eq, native_veq, __smtx_model_eval_not,
    __smtx_model_eval_and, native_and, native_not,
    bitvec_sub_ne_zero_iff,
    signed_bitvec_mult_slt_iff hWPos hWidth x y a]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq]
  have hSubNat : (y - x).toNat ≠ 0 ↔ y - x ≠ 0#T := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := y - x) (y := 0#T)))
  have hANat : a.toNat ≠ 0 ↔ a ≠ 0#U := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := a) (y := 0#U)))
  change
    (y.signExtend W * a.signExtend W).slt
        (x.signExtend W * a.signExtend W) = true ↔
      (y - x).toNat ≠ 0 ∧ a.toNat ≠ 0 ∧
        y.slt x = (0#U).slt a
  rw [hSubNat, hANat, bitvec_sub_ne_zero_iff]
  exact signed_bitvec_mult_slt_iff hWPos hWidth x y a

private theorem unsigned_mult_smt_values
    {T U W : Nat} (hWPos : 0 < W) (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    __smtx_model_eval_eq
        (__smtx_model_eval_bvslt
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((y.zeroExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int))))
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((x.zeroExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int)))))
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval_eq
              (__smtx_model_eval_bvsub
                (SmtValue.Binary (T : Int) (y.toNat : Int))
                (SmtValue.Binary (T : Int) (x.toNat : Int)))
              (SmtValue.Binary (T : Int) ((0#T).toNat : Int))))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval_eq
                (SmtValue.Binary (U : Int) (a.toNat : Int))
                (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
            (__smtx_model_eval_and
              (__smtx_model_eval_eq
                (__smtx_model_eval_bvult
                  (SmtValue.Binary (T : Int) (y.toNat : Int))
                  (SmtValue.Binary (T : Int) (x.toNat : Int)))
                (__smtx_model_eval_bvsgt
                  (SmtValue.Binary (U : Int) (a.toNat : Int))
                  (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
              (SmtValue.Boolean true)))) =
      SmtValue.Boolean true := by
  rw [bvmul_bitvec_values_local (a.signExtend W) 1#W]
  simp only [BitVec.mul_one]
  rw [bvmul_bitvec_values_local (y.zeroExtend W) (a.signExtend W)]
  rw [bvmul_bitvec_values_local (x.zeroExtend W) (a.signExtend W),
    bvslt_bitvec_values]
  rw [bvsub_bitvec_values, bvult_bitvec_values, bvsgt_bitvec_values]
  simp [-BitVec.toNat_sub, __smtx_model_eval_eq, native_veq,
    __smtx_model_eval_not, __smtx_model_eval_and, native_and, native_not,
    bitvec_sub_ne_zero_iff,
    unsigned_bitvec_mult_slt_iff hWPos hWidth x y a]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, not_decide_eq_true, decide_eq_true_eq]
  have hSubNat : (y - x).toNat ≠ 0 ↔ y - x ≠ 0#T := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := y - x) (y := 0#T)))
  have hANat : a.toNat ≠ 0 ↔ a ≠ 0#U := by
    exact not_congr (by simpa using
      (BitVec.toNat_inj (x := a) (y := 0#U)))
  change
    (y.zeroExtend W * a.signExtend W).slt
        (x.zeroExtend W * a.signExtend W) = true ↔
      (y - x).toNat ≠ 0 ∧ a.toNat ≠ 0 ∧
        y.ult x = (0#U).slt a
  rw [hSubNat, hANat, bitvec_sub_ne_zero_iff]
  exact unsigned_bitvec_mult_slt_iff hWPos hWidth x y a

def bvMultSltSizePrem (size source : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) size)
    (Term.Apply (Term.UOp UserOp._at_bvsize) source)

def bvMultSltGePrem (amount size : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) amount) size))
    (Term.Boolean true)

def bvMultSltExt (unsigned : Bool) (amount x : Term) : Term :=
  Term.Apply
    (Term.UOp1 (if unsigned then UserOp1.zero_extend else UserOp1.sign_extend)
      amount) x

private def bvMultSltApp1 (op x : Term) : Term := Term.Apply op x
private def bvMultSltApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

def bvMultSltRhs (unsigned : Bool) (x y a tn an : Term) : Term :=
  let zeroT := bvMultSltApp1 (Term.UOp1 UserOp1.int_to_bv tn) (Term.Numeral 0)
  let zeroA := bvMultSltApp1 (Term.UOp1 UserOp1.int_to_bv an) (Term.Numeral 0)
  let order := if unsigned then UserOp.bvult else UserOp.bvslt
  bvMultSltApp2 (Term.UOp UserOp.and)
    (bvMultSltApp1 (Term.UOp UserOp.not)
      (bvMultSltApp2 (Term.UOp UserOp.eq)
        (bvMultSltApp2 (Term.UOp UserOp.bvsub) y x) zeroT))
    (bvMultSltApp2 (Term.UOp UserOp.and)
      (bvMultSltApp1 (Term.UOp UserOp.not)
        (bvMultSltApp2 (Term.UOp UserOp.eq) a zeroA))
      (bvMultSltApp2 (Term.UOp UserOp.and)
        (bvMultSltApp2 (Term.UOp UserOp.eq)
          (bvMultSltApp2 (Term.UOp order) y x)
          (bvMultSltApp2 (Term.UOp UserOp.bvsgt) a zeroA))
        (Term.Boolean true)))

def bvMultSltRawTerm
    (unsigned : Bool) (x y a n m tn an : Term) : Term :=
  let xExt := bvMultSltExt unsigned n x
  let yExt := bvMultSltExt unsigned n y
  let aExt := Term.Apply (Term.UOp1 UserOp1.sign_extend m) a
  let aTimesOneX := __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.bvmul) aExt)
    (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof xExt))
  let aTimesOneY := __eo_mk_apply
    (Term.Apply (Term.UOp UserOp.bvmul) aExt)
    (__eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof yExt))
  let lhs := __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.bvslt)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) yExt) aTimesOneY))
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) xExt) aTimesOneX)
  __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) lhs)
    (bvMultSltRhs unsigned x y a tn an)

def bvMultSltProgram
    (unsigned : Bool) (x y a n m tn an P1 P2 P3 P4 : Term) : Term :=
  if unsigned then
    __eo_prog_bv_mult_slt_mult_2 x y a n m tn an
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
  else
    __eo_prog_bv_mult_slt_mult_1 x y a n m tn an
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)

private theorem bv_mult_slt_program_canonical
    (unsigned : Bool) (x y a n m tn an : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> a ≠ Term.Stuck ->
    n ≠ Term.Stuck -> m ≠ Term.Stuck -> tn ≠ Term.Stuck -> an ≠ Term.Stuck ->
    bvMultSltProgram unsigned x y a n m tn an
        (bvMultSltSizePrem tn x) (bvMultSltSizePrem an a)
        (bvMultSltGePrem n tn) (bvMultSltGePrem m an) =
      bvMultSltRawTerm unsigned x y a n m tn an := by
  intro hX hY hA hN hM hTn hAn
  cases unsigned with
  | false =>
      unfold bvMultSltProgram bvMultSltSizePrem bvMultSltGePrem
      rw [__eo_prog_bv_mult_slt_mult_1.eq_8 x y a n m tn an
        tn x an a n tn m an hX hY hA hN hM hTn hAn]
      simp [bvMultSltRawTerm, bvMultSltRhs, bvMultSltApp1,
        bvMultSltApp2, bvMultSltExt, __eo_requires, __eo_and,
        __eo_eq, native_ite, native_teq, native_not, native_and,
        hX, hY, hA, hN, hM, hTn, hAn]
  | true =>
      unfold bvMultSltProgram bvMultSltSizePrem bvMultSltGePrem
      rw [__eo_prog_bv_mult_slt_mult_2.eq_8 x y a n m tn an
        tn x an a n tn m an hX hY hA hN hM hTn hAn]
      simp [bvMultSltRawTerm, bvMultSltRhs, bvMultSltApp1,
        bvMultSltApp2, bvMultSltExt, __eo_requires, __eo_and,
        __eo_eq, native_ite, native_teq, native_not, native_and,
        hX, hY, hA, hN, hM, hTn, hAn]

private theorem mult_and_true {A B : Term} :
    __eo_and A B = Term.Boolean true ->
      A = Term.Boolean true ∧ B = Term.Boolean true := by
  intro h
  cases A <;> cases B <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

private def bvMultSltGuard
    (x a n m tn an tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq tn tnRef1) (__eo_eq x xRef))
              (__eo_eq an anRef1))
            (__eo_eq a aRef))
          (__eo_eq n nRef))
        (__eo_eq tn tnRef2))
      (__eo_eq m mRef))
    (__eo_eq an anRef2)

private theorem bv_mult_slt_guard_refs
    {x a n m tn an tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2 body : Term} :
    __eo_requires
        (bvMultSltGuard x a n m tn an tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    tnRef1 = tn ∧ xRef = x ∧ anRef1 = an ∧ aRef = a ∧ nRef = n ∧
      tnRef2 = tn ∧ mRef = m ∧ anRef2 = an := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvMultSltGuard at hGuard
  rcases mult_and_true hGuard with ⟨hG7, hAn2⟩
  rcases mult_and_true hG7 with ⟨hG6, hM⟩
  rcases mult_and_true hG6 with ⟨hG5, hTn2⟩
  rcases mult_and_true hG5 with ⟨hG4, hN⟩
  rcases mult_and_true hG4 with ⟨hG3, hA⟩
  rcases mult_and_true hG3 with ⟨hG2, hAn1⟩
  rcases mult_and_true hG2 with ⟨hTn1, hX⟩
  exact ⟨support_eq_of_eo_eq_true tn tnRef1 hTn1,
    support_eq_of_eo_eq_true x xRef hX,
    support_eq_of_eo_eq_true an anRef1 hAn1,
    support_eq_of_eo_eq_true a aRef hA,
    support_eq_of_eo_eq_true n nRef hN,
    support_eq_of_eo_eq_true tn tnRef2 hTn2,
    support_eq_of_eo_eq_true m mRef hM,
    support_eq_of_eo_eq_true an anRef2 hAn2⟩

private theorem bv_mult_slt_premise_shape
    (unsigned : Bool) (x y a n m tn an P1 P2 P3 P4 : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> a ≠ Term.Stuck ->
    n ≠ Term.Stuck -> m ≠ Term.Stuck -> tn ≠ Term.Stuck -> an ≠ Term.Stuck ->
    bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4 ≠ Term.Stuck ->
    ∃ tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2,
      P1 = bvMultSltSizePrem tnRef1 xRef ∧
      P2 = bvMultSltSizePrem anRef1 aRef ∧
      P3 = bvMultSltGePrem nRef tnRef2 ∧
      P4 = bvMultSltGePrem mRef anRef2 := by
  intro hX hY hA hN hM hTn hAn hProg
  by_cases hShape :
      ∃ tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2,
        P1 = bvMultSltSizePrem tnRef1 xRef ∧
        P2 = bvMultSltSizePrem anRef1 aRef ∧
        P3 = bvMultSltGePrem nRef tnRef2 ∧
        P4 = bvMultSltGePrem mRef anRef2
  · exact hShape
  · exfalso
    apply hProg
    cases unsigned with
    | false =>
        unfold bvMultSltProgram
        exact __eo_prog_bv_mult_slt_mult_1.eq_9 x y a n m tn an
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
          hX hY hA hN hM hTn hAn (by
            intro tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2
              hP1 hP2 hP3 hP4
            cases hP1; cases hP2; cases hP3; cases hP4
            exact hShape ⟨tnRef1, xRef, anRef1, aRef, nRef, tnRef2,
              mRef, anRef2, rfl, rfl, rfl, rfl⟩)
    | true =>
        unfold bvMultSltProgram
        exact __eo_prog_bv_mult_slt_mult_2.eq_9 x y a n m tn an
          (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
          hX hY hA hN hM hTn hAn (by
            intro tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2
              hP1 hP2 hP3 hP4
            cases hP1; cases hP2; cases hP3; cases hP4
            exact hShape ⟨tnRef1, xRef, anRef1, aRef, nRef, tnRef2,
              mRef, anRef2, rfl, rfl, rfl, rfl⟩)

private theorem bvMultSltProgram_normalize
    (unsigned : Bool) (x y a n m tn an P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x -> RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a -> RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation m -> RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4 ≠ Term.Stuck ->
    P1 = bvMultSltSizePrem tn x ∧ P2 = bvMultSltSizePrem an a ∧
      P3 = bvMultSltGePrem n tn ∧ P4 = bvMultSltGePrem m an ∧
      bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4 =
        bvMultSltRawTerm unsigned x y a n m tn an := by
  intro hXTrans hYTrans hATrans hNTrans hMTrans hTnTrans hAnTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hA := RuleProofs.term_ne_stuck_of_has_smt_translation a hATrans
  have hN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hTn := RuleProofs.term_ne_stuck_of_has_smt_translation tn hTnTrans
  have hAn := RuleProofs.term_ne_stuck_of_has_smt_translation an hAnTrans
  rcases bv_mult_slt_premise_shape unsigned x y a n m tn an P1 P2 P3 P4
      hX hY hA hN hM hTn hAn hProg with
    ⟨tnRef1, xRef, anRef1, aRef, nRef, tnRef2, mRef, anRef2,
      hP1, hP2, hP3, hP4⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4] at hReq
  cases unsigned with
  | false =>
      unfold bvMultSltProgram bvMultSltSizePrem bvMultSltGePrem at hReq
      rw [__eo_prog_bv_mult_slt_mult_1.eq_8 x y a n m tn an
        tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2
        hX hY hA hN hM hTn hAn] at hReq
      have hRefs := bv_mult_slt_guard_refs
        (x := x) (a := a) (n := n) (m := m) (tn := tn) (an := an)
        (tnRef1 := tnRef1) (xRef := xRef) (anRef1 := anRef1)
        (aRef := aRef) (nRef := nRef) (tnRef2 := tnRef2)
        (mRef := mRef) (anRef2 := anRef2)
        (by simpa [bvMultSltGuard] using hReq)
      rcases hRefs with
        ⟨hTn1, hXRef, hAn1, hARef, hNRef, hTn2, hMRef, hAn2⟩
      subst tnRef1
      subst xRef
      subst anRef1
      subst aRef
      subst nRef
      subst tnRef2
      subst mRef
      subst anRef2
      refine ⟨hP1, hP2, hP3, hP4, ?_⟩
      simpa only [hP1, hP2, hP3, hP4] using
        bv_mult_slt_program_canonical false x y a n m tn an
          hX hY hA hN hM hTn hAn
  | true =>
      unfold bvMultSltProgram bvMultSltSizePrem bvMultSltGePrem at hReq
      rw [__eo_prog_bv_mult_slt_mult_2.eq_8 x y a n m tn an
        tnRef1 xRef anRef1 aRef nRef tnRef2 mRef anRef2
        hX hY hA hN hM hTn hAn] at hReq
      have hRefs := bv_mult_slt_guard_refs
        (x := x) (a := a) (n := n) (m := m) (tn := tn) (an := an)
        (tnRef1 := tnRef1) (xRef := xRef) (anRef1 := anRef1)
        (aRef := aRef) (nRef := nRef) (tnRef2 := tnRef2)
        (mRef := mRef) (anRef2 := anRef2)
        (by simpa [bvMultSltGuard] using hReq)
      rcases hRefs with
        ⟨hTn1, hXRef, hAn1, hARef, hNRef, hTn2, hMRef, hAn2⟩
      subst tnRef1
      subst xRef
      subst anRef1
      subst aRef
      subst nRef
      subst tnRef2
      subst mRef
      subst anRef2
      refine ⟨hP1, hP2, hP3, hP4, ?_⟩
      simpa only [hP1, hP2, hP3, hP4] using
        bv_mult_slt_program_canonical true x y a n m tn an
          hX hY hA hN hM hTn hAn

def bvMultSltNil (unsigned : Bool) (n z : Term) : Term :=
  __eo_nil (Term.UOp UserOp.bvmul)
    (__eo_typeof (bvMultSltExt unsigned n z))

def bvMultSltTimesOne
    (unsigned : Bool) (z a n m : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvmul)
      (Term.Apply (Term.UOp1 UserOp1.sign_extend m) a))
    (bvMultSltNil unsigned n z)

def bvMultSltProduct
    (unsigned : Bool) (z a n m : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvmul) (bvMultSltExt unsigned n z))
    (bvMultSltTimesOne unsigned z a n m)

def bvMultSltLhs
    (unsigned : Bool) (x y a n m : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvslt)
      (bvMultSltProduct unsigned y a n m))
    (bvMultSltProduct unsigned x a n m)

def bvMultSltDirectTerm
    (unsigned : Bool) (x y a n m tn an : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvMultSltLhs unsigned x y a n m))
    (bvMultSltRhs unsigned x y a tn an)

private theorem mult_mk_apply_arg_stuck (f : Term) :
    __eo_mk_apply f Term.Stuck = Term.Stuck := by
  cases f <;> rfl

private theorem mult_mk_apply_fun_stuck (x : Term) :
    __eo_mk_apply Term.Stuck x = Term.Stuck := by
  rfl

private theorem bv_mult_slt_nils_ne
    (unsigned : Bool) (x y a n m tn an : Term) :
    __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) = Term.Bool ->
    __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (bvMultSltExt unsigned n x)) ≠ Term.Stuck ∧
      __eo_nil (Term.UOp UserOp.bvmul)
        (__eo_typeof (bvMultSltExt unsigned n y)) ≠ Term.Stuck := by
  intro hTy
  constructor
  · intro hNil
    apply term_ne_stuck_of_typeof_bool hTy
    unfold bvMultSltRawTerm
    dsimp only
    rw [hNil]
    simp only [mult_mk_apply_arg_stuck, mult_mk_apply_fun_stuck]
  · intro hNil
    apply term_ne_stuck_of_typeof_bool hTy
    unfold bvMultSltRawTerm
    dsimp only
    rw [hNil]
    simp only [mult_mk_apply_arg_stuck, mult_mk_apply_fun_stuck]

private theorem bv_mult_slt_raw_eq_direct
    (unsigned : Bool) (x y a n m tn an : Term)
    (hTy : __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) =
      Term.Bool) :
    bvMultSltRawTerm unsigned x y a n m tn an =
      bvMultSltDirectTerm unsigned x y a n m tn an := by
  rcases bv_mult_slt_nils_ne unsigned x y a n m tn an hTy with
    ⟨hNilX, hNilY⟩
  unfold bvMultSltRawTerm bvMultSltDirectTerm bvMultSltLhs
    bvMultSltProduct bvMultSltTimesOne bvMultSltNil
  dsimp only
  simp [bvMultSltRhs, bvMultSltApp1, bvMultSltApp2, __eo_mk_apply,
    hNilX, hNilY]

private theorem mult_typeof_and_inv {p q : Term} :
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.and) p) q) =
      Term.Bool ->
    __eo_typeof p = Term.Bool ∧ __eo_typeof q = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_or_bool_args (__eo_typeof p) (__eo_typeof q)
    (by have hsimpa := h; (try simp at hsimpa ⊢); exact hsimpa)

private theorem mult_typeof_not_inv {p : Term} :
    __eo_typeof (Term.Apply (Term.UOp UserOp.not) p) = Term.Bool ->
    __eo_typeof p = Term.Bool := by
  intro h
  change __eo_typeof_not (__eo_typeof p) = Term.Bool at h
  cases hp : __eo_typeof p <;>
    simp [__eo_typeof_not, hp] at h ⊢

private theorem mult_int_to_bv_context
    (w width : Term) :
    w ≠ Term.Stuck ->
    __eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv w) (Term.Numeral 0)) =
      Term.Apply (Term.UOp UserOp.BitVec) width ->
    ∃ W : native_Int,
      w = Term.Numeral W ∧ width = Term.Numeral W ∧
      native_zleq 0 W = true := by
  intro hWNe hTy
  change __eo_typeof_int_to_bv (__eo_typeof w) w (Term.UOp UserOp.Int) =
    Term.Apply (Term.UOp UserOp.BitVec) width at hTy
  have hWTy : __eo_typeof w = Term.UOp UserOp.Int := by
    cases hw : __eo_typeof w <;>
      simp [__eo_typeof_int_to_bv, hw, hWNe] at hTy ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_int_to_bv, hw, hWNe] at hTy ⊢
  have hReqTy :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
    simpa [__eo_typeof_int_to_bv, hWTy, hWNe] using hTy
  have hReqNe :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReqTy]
    intro h
    cases h
  have hGuard : __eo_gt w (Term.Numeral (-1 : native_Int)) =
      Term.Boolean true := support_eo_requires_cond_eq_of_non_stuck hReqNe
  have hReqEq :
      __eo_requires (__eo_gt w (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    simp [__eo_requires, hGuard, native_ite, native_teq, native_not]
  rw [hReqEq] at hReqTy
  have hWidth : width = w := by
    injection hReqTy with _ h
    exact h.symm
  cases w <;> simp [__eo_gt] at hGuard
  case Numeral W =>
    have hW0 : native_zleq 0 W = true := by
      have hsimpa := hGuard
      try simp [SmtEval.native_zlt, SmtEval.native_zleq] at hsimpa ⊢
      exact hsimpa
    exact ⟨W, rfl, hWidth, hW0⟩

private theorem mult_smt_type_of_eo_bv
    (z : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation z ->
    __eo_typeof z =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt z) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hTrans hTy hW0
  have hExpected :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      z (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
      (__eo_to_smt z) rfl hTrans hTy
  simpa [__eo_to_smt_type, hW0, native_ite] using hExpected

private theorem bv_mult_slt_rhs_context
    (unsigned : Bool) (x y a tn an : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof (bvMultSltRhs unsigned x y a tn an) = Term.Bool ->
    ∃ T U : native_Int,
      tn = Term.Numeral T ∧ an = Term.Numeral U ∧
      native_zleq 0 T = true ∧ native_zleq 0 U = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral T) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral T) ∧
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral U) ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat T) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat T) ∧
      __smtx_typeof (__eo_to_smt a) =
        SmtType.BitVec (native_int_to_nat U) := by
  intro hXTrans hYTrans hATrans hTnTrans hAnTrans hRhsTy
  unfold bvMultSltRhs bvMultSltApp1 bvMultSltApp2 at hRhsTy
  dsimp only at hRhsTy
  rcases mult_typeof_and_inv hRhsTy with ⟨hNotSubTy, hTailTy⟩
  rcases mult_typeof_and_inv hTailTy with ⟨_hNotATy, hOrderTailTy⟩
  rcases mult_typeof_and_inv hOrderTailTy with ⟨hOrderEqTy, _hTrueTy⟩
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hOrderEqTy with
    ⟨hOrderNe, hSgtNe⟩
  have hOrderNe' :
      __eo_typeof_bvult (__eo_typeof y) (__eo_typeof x) ≠ Term.Stuck := by
    cases unsigned <;>
      (have hsimpa := hOrderNe
       try simp at hsimpa ⊢
       exact hsimpa)
  rcases RuleProofs.eo_typeof_bvult_args_of_ne_stuck _ _
      hOrderNe' with ⟨tWidth, hYTy, hXTy, _hTWidthNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x tWidth
      hXTrans hXTy with ⟨T, hTWidth, hT0, hXSmtTy⟩
  subst tWidth
  have hYSmtTy := mult_smt_type_of_eo_bv y T hYTrans hYTy hT0
  rcases RuleProofs.eo_typeof_bvult_args_of_ne_stuck _ _
      (by have hsimpa := hSgtNe; (try simp at hsimpa ⊢); exact hsimpa) with ⟨uWidth, hATy, hZeroATy, _hUWidthNe⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width a uWidth
      hATrans hATy with ⟨U, hUWidth, hU0, hASmtTy⟩
  subst uWidth
  have hAnNe := RuleProofs.term_ne_stuck_of_has_smt_translation an hAnTrans
  rcases mult_int_to_bv_context an (Term.Numeral U) hAnNe
      (by simpa using hZeroATy) with ⟨U', hAn, hUU', hU'0⟩
  injection hUU' with hUEq
  subst U'
  have hSubEqTy := mult_typeof_not_inv hNotSubTy
  have hSubTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hSubEqTy
  have hSubTy :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral T) := by
    change __eo_typeof_bvand (__eo_typeof y) (__eo_typeof x) = _
    rw [hYTy, hXTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  rw [hSubTy] at hSubTypes
  have hTnNe := RuleProofs.term_ne_stuck_of_has_smt_translation tn hTnTrans
  rcases mult_int_to_bv_context tn (Term.Numeral T) hTnNe
      (by simpa using hSubTypes.symm) with ⟨T', hTn, hTT', hT'0⟩
  injection hTT' with hTEq
  subst T'
  exact ⟨T, U, hTn, hAn, hT0, hU0, hXTy, hYTy, hATy,
    hXSmtTy, hYSmtTy, hASmtTy⟩

private theorem mult_extend_full_context
    (unsigned : Bool) (z k : Term) (w : native_Int) :
    __eo_typeof z =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_typeof (bvMultSltExt unsigned k z) ≠ Term.Stuck ->
    ∃ K : native_Int,
      k = Term.Numeral K ∧ native_zleq 0 K = true ∧
      __eo_typeof (bvMultSltExt unsigned k z) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus w K)) := by
  intro hZTy hExtNe
  have hCore :
      __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof z) ≠
        Term.Stuck := by
    cases unsigned <;>
      (have hsimpa := hExtNe
       try simp [bvMultSltExt] at hsimpa ⊢
       exact hsimpa)
  rw [hZTy] at hCore
  have hParts :
      __eo_typeof k = Term.UOp UserOp.Int ∧
      __eo_requires (__eo_gt k (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec)
            (__eo_add (Term.Numeral w) k)) ≠ Term.Stuck := by
    unfold __eo_typeof_zero_extend at hCore
    split at hCore <;> simp_all
  have hGuard :
      __eo_gt k (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hParts.2
  rcases sign_numeral_nonneg_of_gt_neg_one k hGuard with ⟨K, hK, hK0⟩
  subst k
  have hLt : native_zlt (-1 : native_Int) K = true := by
    have hNonneg : (0 : Int) ≤ K := by
      simpa [SmtEval.native_zleq] using hK0
    have : (-1 : Int) < K := by omega
    simpa [SmtEval.native_zlt] using this
  refine ⟨K, rfl, hK0, ?_⟩
  cases unsigned <;>
    change __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral K)
      (__eo_typeof z) = _ <;>
    rw [hZTy] <;>
    simp [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
      __eo_mk_apply, hLt, native_ite, native_teq, native_not]

private theorem bv_mult_slt_context
    (unsigned : Bool) (x y a n m tn an : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) = Term.Bool ->
    ∃ T U N M : native_Int,
      tn = Term.Numeral T ∧ an = Term.Numeral U ∧
      n = Term.Numeral N ∧ m = Term.Numeral M ∧
      native_zleq 0 T = true ∧ native_zleq 0 U = true ∧
      native_zleq 0 N = true ∧ native_zleq 0 M = true ∧
      native_zplus T N = native_zplus U M ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral T) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral T) ∧
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral U) ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat T) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat T) ∧
      __smtx_typeof (__eo_to_smt a) =
        SmtType.BitVec (native_int_to_nat U) := by
  intro hXTrans hYTrans hATrans hTnTrans hAnTrans hRawTy
  have hDirectEq := bv_mult_slt_raw_eq_direct unsigned x y a n m tn an hRawTy
  have hDirectTy :
      __eo_typeof (bvMultSltDirectTerm unsigned x y a n m tn an) =
        Term.Bool := by
    rw [← hDirectEq]
    exact hRawTy
  change __eo_typeof_eq
      (__eo_typeof (bvMultSltLhs unsigned x y a n m))
      (__eo_typeof (bvMultSltRhs unsigned x y a tn an)) =
    Term.Bool at hDirectTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hDirectTy with
    ⟨hLhsNe, _hRhsNe⟩
  have hLhsCore :
      __eo_typeof_bvult
          (__eo_typeof (bvMultSltProduct unsigned y a n m))
          (__eo_typeof (bvMultSltProduct unsigned x a n m)) ≠
        Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvMultSltLhs] at hsimpa ⊢
    exact hsimpa
  rcases RuleProofs.eo_typeof_bvult_args_of_ne_stuck _ _ hLhsCore with
    ⟨prodWidth, hProdYTy, hProdXTy, _hProdWidthNe⟩
  have hLhsTy : __eo_typeof (bvMultSltLhs unsigned x y a n m) =
      Term.Bool := by
    change __eo_typeof_bvult
      (__eo_typeof (bvMultSltProduct unsigned y a n m))
      (__eo_typeof (bvMultSltProduct unsigned x a n m)) = Term.Bool
    rw [hProdYTy, hProdXTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hTopTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hDirectTy
  rw [hLhsTy] at hTopTypes
  have hRhsTy : __eo_typeof (bvMultSltRhs unsigned x y a tn an) =
      Term.Bool := hTopTypes.symm
  rcases bv_mult_slt_rhs_context unsigned x y a tn an hXTrans hYTrans
      hATrans hTnTrans hAnTrans hRhsTy with
    ⟨T, U, hTn, hAn, hT0, hU0, hXTy, hYTy, hATy,
      hXSmtTy, hYSmtTy, hASmtTy⟩
  have hProdYNe : __eo_typeof (bvMultSltProduct unsigned y a n m) ≠
      Term.Stuck := by
    rw [hProdYTy]
    intro h
    cases h
  have hProdYCore :
      __eo_typeof_bvand (__eo_typeof (bvMultSltExt unsigned n y))
          (__eo_typeof (bvMultSltTimesOne unsigned y a n m)) ≠
        Term.Stuck := by
    have hsimpa := hProdYNe
    try simp [bvMultSltProduct] at hsimpa ⊢
    exact hsimpa
  rcases RuleProofs.eo_typeof_bvand_args_of_ne_stuck _ _ hProdYCore with
    ⟨wide, hYExtTy, hTimesYTy, _hWideNe⟩
  have hTimesYNe : __eo_typeof (bvMultSltTimesOne unsigned y a n m) ≠
      Term.Stuck := by
    rw [hTimesYTy]
    intro h
    cases h
  have hTimesYCore :
      __eo_typeof_bvand
          (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend m) a))
          (__eo_typeof (bvMultSltNil unsigned n y)) ≠ Term.Stuck := by
    have hsimpa := hTimesYNe
    try simp [bvMultSltTimesOne] at hsimpa ⊢
    exact hsimpa
  rcases RuleProofs.eo_typeof_bvand_args_of_ne_stuck _ _ hTimesYCore with
    ⟨wideA, hAExtTy, _hNilYTy, _hWideANe⟩
  have hWideEq : wideA = wide := by
    have hTimesYTy' :
        __eo_typeof (bvMultSltTimesOne unsigned y a n m) =
          Term.Apply (Term.UOp UserOp.BitVec) wideA := by
      change __eo_typeof_bvand
        (__eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend m) a))
        (__eo_typeof (bvMultSltNil unsigned n y)) = _
      rw [hAExtTy, _hNilYTy]
      simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not]
    rw [hTimesYTy] at hTimesYTy'
    injection hTimesYTy' with _ hWidth
    exact hWidth.symm
  subst wideA
  have hYExtNe : __eo_typeof (bvMultSltExt unsigned n y) ≠ Term.Stuck := by
    rw [hYExtTy]
    intro h
    cases h
  rcases mult_extend_full_context unsigned y n T hYTy hYExtNe with
    ⟨N, hN, hN0, hYExtTy'⟩
  subst n
  have hWideTN : wide = Term.Numeral (native_zplus T N) := by
    rw [hYExtTy] at hYExtTy'
    injection hYExtTy'
  subst wide
  have hAExtNe :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend m) a) ≠
        Term.Stuck := by
    rw [hAExtTy]
    intro h
    cases h
  rcases mult_extend_full_context false a m U hATy hAExtNe with
    ⟨M, hM, hM0, hAExtTy'⟩
  subst m
  have hWidths : native_zplus T N = native_zplus U M := by
    change __eo_typeof
        (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral M)) a) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus U M)) at hAExtTy'
    rw [hAExtTy] at hAExtTy'
    injection hAExtTy' with _ hNum
    injection hNum
  exact ⟨T, U, N, M, hTn, hAn, rfl, rfl, hT0, hU0, hN0, hM0,
    hWidths, hXTy, hYTy, hATy, hXSmtTy, hYSmtTy, hASmtTy⟩

private theorem mult_model_eval_eq_true
    (M : SmtModel) (p q : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) p) q) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt p))
        (__smtx_model_eval M (__eo_to_smt q)) =
      SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem bv_mult_slt_ge_of_premise
    (M : SmtModel) (amount width : native_Int) :
    eo_interprets M
        (bvMultSltGePrem (Term.Numeral amount) (Term.Numeral width)) true ->
    native_zleq width amount = true := by
  intro hPrem
  have hEval := mult_model_eval_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral amount))
      (Term.Numeral width)) (Term.Boolean true) hPrem
  simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval] at hEval
  change __smtx_model_eval M
      (SmtTerm.geq (SmtTerm.Numeral amount) (SmtTerm.Numeral width)) =
    SmtValue.Boolean true at hEval
  rw [__smtx_model_eval.eq_def] at hEval
  simpa [__smtx_model_eval, __smtx_model_eval_geq,
    __smtx_model_eval_leq] using hEval

private theorem bv_mult_slt_nat_width_bound
    (T U N M : native_Int) :
    native_zleq 0 T = true -> native_zleq 0 U = true ->
    native_zleq 0 N = true -> native_zleq 0 M = true ->
    native_zplus T N = native_zplus U M ->
    native_zleq T N = true -> native_zleq U M = true ->
    native_int_to_nat T + native_int_to_nat U ≤
      native_int_to_nat T + native_int_to_nat N := by
  intro hT0 hU0 hN0 hM0 hWidths hTN hUM
  have hT : (0 : Int) ≤ T := by
    simpa [SmtEval.native_zleq] using hT0
  have hU : (0 : Int) ≤ U := by
    simpa [SmtEval.native_zleq] using hU0
  have hN : (0 : Int) ≤ N := by
    simpa [SmtEval.native_zleq] using hN0
  have hM : (0 : Int) ≤ M := by
    simpa [SmtEval.native_zleq] using hM0
  have hTN' : T ≤ N := by
    simpa [SmtEval.native_zleq] using hTN
  have hUM' : U ≤ M := by
    simpa [SmtEval.native_zleq] using hUM
  have hWidths' : T + N = U + M := by
    simpa [SmtEval.native_zplus] using hWidths
  have hToNatT : native_int_to_nat T = T.toNat := rfl
  have hToNatU : native_int_to_nat U = U.toNat := rfl
  have hToNatN : native_int_to_nat N = N.toNat := rfl
  rw [hToNatT, hToNatU, hToNatN]
  have hCastT : ((T.toNat : Nat) : Int) = T := Int.toNat_of_nonneg hT
  have hCastU : ((U.toNat : Nat) : Int) = U := Int.toNat_of_nonneg hU
  have hCastN : ((N.toNat : Nat) : Int) = N := Int.toNat_of_nonneg hN
  have hLow : U + U ≤ T + N := by
    rw [hWidths']
    exact Int.add_le_add_left hUM' U
  have hHigh : T + N ≤ N + N := Int.add_le_add_right hTN' N
  have hUU : U + U ≤ N + N := Int.le_trans hLow hHigh
  have hTwice : (2 : Int) * U ≤ 2 * N := by
    rw [Int.two_mul, Int.two_mul]
    exact hUU
  have hUN : U ≤ N :=
    Int.le_of_mul_le_mul_left hTwice (by decide)
  have hUNNat : U.toNat ≤ N.toNat := Int.toNat_le_toNat hUN
  exact Nat.add_le_add_left hUNNat T.toNat

private theorem mult_extend_type_of_context
    (unsigned : Bool) (z : Term) (K W : native_Int) :
    __eo_typeof z =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 K = true ->
    __eo_typeof (bvMultSltExt unsigned (Term.Numeral K) z) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_zplus W K)) := by
  intro hZTy hK0
  have hLt : native_zlt (-1 : native_Int) K = true := by
    have hNonneg : (0 : Int) ≤ K := by
      simpa [SmtEval.native_zleq] using hK0
    have : (-1 : Int) < K := by omega
    simpa [SmtEval.native_zlt] using this
  cases unsigned <;>
    change __eo_typeof_zero_extend (Term.UOp UserOp.Int) (Term.Numeral K)
      (__eo_typeof z) = _ <;>
    rw [hZTy] <;>
    simp [__eo_typeof_zero_extend, __eo_requires, __eo_gt, __eo_add,
      __eo_mk_apply, hLt, native_ite, native_teq, native_not]

private theorem mult_nil_bvmul_bitvec
    (W : Nat)
    (hNe :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int W))) ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int W))) =
      Term.Binary (native_nat_to_int W) ((1#W).toNat : Int) := by
  cases W with
  | zero => native_decide
  | succ w =>
      simpa [Nat.succ_eq_add_one] using
        nil_bvmul_bitvec_succ_of_ne_stuck w (by
          simpa [Nat.succ_eq_add_one] using hNe)

theorem bvMultSlt_nil_bvmul_bitvec
    (W : Nat)
    (hNe :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int W))) ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp.bvmul)
        (Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int W))) =
      Term.Binary (native_nat_to_int W) ((1#W).toNat : Int) :=
  mult_nil_bvmul_bitvec W hNe

private theorem mult_eval_zero_extend_term
    (M : SmtModel) (z : Term) (K : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral K)) z)) =
      __smtx_model_eval_zero_extend (SmtValue.Numeral K)
        (__smtx_model_eval M (__eo_to_smt z)) := by
  change __smtx_model_eval M
      (SmtTerm.zero_extend (SmtTerm.Numeral K) (__eo_to_smt z)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval]

private theorem mult_eval_bvslt_term (M : SmtModel) (p q : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvslt p q) =
      __smtx_model_eval_bvslt
        (__smtx_model_eval M p) (__smtx_model_eval M q) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem mult_eval_bvult_term (M : SmtModel) (p q : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvult p q) =
      __smtx_model_eval_bvult
        (__smtx_model_eval M p) (__smtx_model_eval M q) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem mult_eval_bvsgt_term (M : SmtModel) (p q : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsgt p q) =
      __smtx_model_eval_bvsgt
        (__smtx_model_eval M p) (__smtx_model_eval M q) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem mult_eval_bvsub_term (M : SmtModel) (p q : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsub p q) =
      __smtx_model_eval_bvsub
        (__smtx_model_eval M p) (__smtx_model_eval M q) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem signed_mult_smt_values_all
    {T U W : Nat} (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    __smtx_model_eval_eq
        (__smtx_model_eval_bvslt
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((y.signExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int))))
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((x.signExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int)))))
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval_eq
              (__smtx_model_eval_bvsub
                (SmtValue.Binary (T : Int) (y.toNat : Int))
                (SmtValue.Binary (T : Int) (x.toNat : Int)))
              (SmtValue.Binary (T : Int) ((0#T).toNat : Int))))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval_eq
                (SmtValue.Binary (U : Int) (a.toNat : Int))
                (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
            (__smtx_model_eval_and
              (__smtx_model_eval_eq
                (__smtx_model_eval_bvslt
                  (SmtValue.Binary (T : Int) (y.toNat : Int))
                  (SmtValue.Binary (T : Int) (x.toNat : Int)))
                (__smtx_model_eval_bvsgt
                  (SmtValue.Binary (U : Int) (a.toNat : Int))
                  (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
              (SmtValue.Boolean true)))) = SmtValue.Boolean true := by
  by_cases hW : W = 0
  · subst W
    have hT : T = 0 := by omega
    have hU : U = 0 := by omega
    subst T
    subst U
    have hx : x = 0#0 := Subsingleton.elim _ _
    have hy : y = 0#0 := Subsingleton.elim _ _
    have ha : a = 0#0 := Subsingleton.elim _ _
    subst x
    subst y
    subst a
    rw [bvmul_bitvec_values_local ((0#0).signExtend 0) 1#0]
    simp only [BitVec.mul_one]
    rw [bvmul_bitvec_values_local ((0#0).signExtend 0)
      ((0#0).signExtend 0)]
    rw [bvslt_bitvec_values]
    rw [bvsub_bitvec_values, bvslt_bitvec_values, bvsgt_bitvec_values]
    simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval_not,
      __smtx_model_eval_and, native_and, native_not]
  · exact signed_mult_smt_values (Nat.pos_of_ne_zero hW) hWidth x y a

private theorem unsigned_mult_smt_values_all
    {T U W : Nat} (hWidth : T + U ≤ W)
    (x y : BitVec T) (a : BitVec U) :
    __smtx_model_eval_eq
        (__smtx_model_eval_bvslt
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((y.zeroExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int))))
          (__smtx_model_eval_bvmul
            (SmtValue.Binary (W : Int) ((x.zeroExtend W).toNat : Int))
            (__smtx_model_eval_bvmul
              (SmtValue.Binary (W : Int) ((a.signExtend W).toNat : Int))
              (SmtValue.Binary (W : Int) ((1#W).toNat : Int)))))
        (__smtx_model_eval_and
          (__smtx_model_eval_not
            (__smtx_model_eval_eq
              (__smtx_model_eval_bvsub
                (SmtValue.Binary (T : Int) (y.toNat : Int))
                (SmtValue.Binary (T : Int) (x.toNat : Int)))
              (SmtValue.Binary (T : Int) ((0#T).toNat : Int))))
          (__smtx_model_eval_and
            (__smtx_model_eval_not
              (__smtx_model_eval_eq
                (SmtValue.Binary (U : Int) (a.toNat : Int))
                (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
            (__smtx_model_eval_and
              (__smtx_model_eval_eq
                (__smtx_model_eval_bvult
                  (SmtValue.Binary (T : Int) (y.toNat : Int))
                  (SmtValue.Binary (T : Int) (x.toNat : Int)))
                (__smtx_model_eval_bvsgt
                  (SmtValue.Binary (U : Int) (a.toNat : Int))
                  (SmtValue.Binary (U : Int) ((0#U).toNat : Int))))
              (SmtValue.Boolean true)))) = SmtValue.Boolean true := by
  by_cases hW : W = 0
  · subst W
    have hT : T = 0 := by omega
    have hU : U = 0 := by omega
    subst T
    subst U
    have hx : x = 0#0 := Subsingleton.elim _ _
    have hy : y = 0#0 := Subsingleton.elim _ _
    have ha : a = 0#0 := Subsingleton.elim _ _
    subst x
    subst y
    subst a
    rw [bvmul_bitvec_values_local ((0#0).signExtend 0) 1#0]
    simp only [BitVec.mul_one]
    rw [bvmul_bitvec_values_local ((0#0).zeroExtend 0)
      ((0#0).signExtend 0)]
    rw [bvslt_bitvec_values]
    rw [bvsub_bitvec_values, bvult_bitvec_values, bvsgt_bitvec_values]
    simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval_not,
      __smtx_model_eval_and, native_and, native_not]
  · exact unsigned_mult_smt_values (Nat.pos_of_ne_zero hW) hWidth x y a

private theorem mult_smt_typeof_extend
    (unsigned : Bool) (z : Term) (W K : native_Int) :
    __smtx_typeof (__eo_to_smt z) =
      SmtType.BitVec (native_int_to_nat W) ->
    native_zleq 0 W = true -> native_zleq 0 K = true ->
    __smtx_typeof
        (__eo_to_smt (bvMultSltExt unsigned (Term.Numeral K) z)) =
      SmtType.BitVec (native_int_to_nat (native_zplus W K)) := by
  intro hZTy hW0 hK0
  have hRound := native_int_to_nat_roundtrip W hW0
  cases unsigned with
  | false =>
      simpa [bvMultSltExt, SmtEval.native_zplus, Int.add_comm] using
        smt_typeof_sign_extend_of_context z W K hZTy hW0 hK0
  | true =>
      change __smtx_typeof
          (SmtTerm.zero_extend (SmtTerm.Numeral K) (__eo_to_smt z)) = _
      rw [typeof_zero_extend_eq, hZTy]
      simp [__smtx_typeof_zero_extend, native_ite, hK0, hRound,
        SmtEval.native_zplus, Int.add_comm]

private theorem mult_smt_typeof_bvmul
    (p q : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt p) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt q) = SmtType.BitVec W ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) p) q)) =
      SmtType.BitVec W := by
  intro hp hq
  change __smtx_typeof (SmtTerm.bvmul (__eo_to_smt p) (__eo_to_smt q)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hp, hq, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem mult_smt_typeof_bvsub
    (p q : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt p) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt q) = SmtType.BitVec W ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) p) q)) =
      SmtType.BitVec W := by
  intro hp hq
  change __smtx_typeof (SmtTerm.bvsub (__eo_to_smt p) (__eo_to_smt q)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hp, hq, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem mult_smt_typeof_bvslt
    (p q : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt p) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt q) = SmtType.BitVec W ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) p) q) := by
  intro hp hq
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.bvslt (__eo_to_smt p) (__eo_to_smt q)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hp, hq, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem mult_smt_typeof_bvult
    (p q : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt p) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt q) = SmtType.BitVec W ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) p) q) := by
  intro hp hq
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.bvult (__eo_to_smt p) (__eo_to_smt q)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hp, hq, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem mult_smt_typeof_bvsgt
    (p q : Term) (W : Nat) :
    __smtx_typeof (__eo_to_smt p) = SmtType.BitVec W ->
    __smtx_typeof (__eo_to_smt q) = SmtType.BitVec W ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) p) q) := by
  intro hp hq
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.bvsgt (__eo_to_smt p) (__eo_to_smt q)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hp, hq, native_ite,
    native_nateq, Smtm.native_nateq]

private theorem mult_smt_typeof_bitvec_payload (v : BitVec W) :
    __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int W) (v.toNat : Int)) =
      SmtType.BitVec W := by
  have hW0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hMod :
      native_mod_total (v.toNat : Int)
          (native_int_pow2 (native_nat_to_int W)) = (v.toNat : Int) := by
    rw [native_int_pow2_nat W]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
      (by exact_mod_cast v.isLt)
  have hW0' : native_zleq 0 (W : Int) = true := by
    simp [SmtEval.native_zleq]
  have hMod' :
      (v.toNat : Int) =
        native_mod_total (v.toNat : Int) (native_int_pow2 (W : Int)) := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hMod.symm
  have hCanon :
      native_zeq (v.toNat : Int)
          (native_mod_total (v.toNat : Int) (native_int_pow2 (W : Int))) =
        true := by
    simpa [SmtEval.native_zeq] using hMod'
  have hCanon0 :
      native_zeq (v.toNat : Int)
          (native_mod_total (v.toNat : Int)
            (native_int_pow2 (native_nat_to_int W))) = true := by
    simpa [SmtEval.native_zeq] using hMod.symm
  have hAnd :
      native_and (native_zleq 0 (native_nat_to_int W))
          (native_zeq (v.toNat : Int)
            (native_mod_total (v.toNat : Int)
              (native_int_pow2 (native_nat_to_int W)))) = true := by
    simp [SmtEval.native_and, hW0, hCanon0]
  rw [__smtx_typeof.eq_def] <;> simp only
  rw [hAnd]
  simp [native_ite, native_int_to_nat, native_nat_to_int,
    SmtEval.native_int_to_nat, Smtm.native_nat_to_int]

private theorem typed_bv_mult_slt_raw
    (unsigned : Bool) (x y a n m tn an : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvMultSltRawTerm unsigned x y a n m tn an) := by
  intro hXTrans hYTrans hATrans hTnTrans hAnTrans hRawTy
  rcases bv_mult_slt_context unsigned x y a n m tn an hXTrans hYTrans
      hATrans hTnTrans hAnTrans hRawTy with
    ⟨T, U, N, M, rfl, rfl, rfl, rfl, hT0, hU0, hN0, hM0,
      hWidths, hXTy, hYTy, hATy, hXSmtTy, hYSmtTy, hASmtTy⟩
  let TN := native_int_to_nat T
  let UN := native_int_to_nat U
  let NN := native_int_to_nat N
  let WN := TN + NN
  have hTRound : native_nat_to_int TN = T := by
    simpa [TN] using native_int_to_nat_roundtrip T hT0
  have hURound : native_nat_to_int UN = U := by
    simpa [UN] using native_int_to_nat_roundtrip U hU0
  have hNRound : native_nat_to_int NN = N := by
    simpa [NN] using native_int_to_nat_roundtrip N hN0
  have hWideRound : native_nat_to_int WN = native_zplus T N := by
    calc
      native_nat_to_int WN =
          native_nat_to_int TN + native_nat_to_int NN := by
        simp [WN, native_nat_to_int, Smtm.native_nat_to_int]
      _ = T + N := by rw [hTRound, hNRound]
      _ = native_zplus T N := rfl
  have hXExtTy := mult_extend_type_of_context unsigned x N T hXTy hN0
  have hYExtTy := mult_extend_type_of_context unsigned y N T hYTy hN0
  have hAExtTy := mult_extend_type_of_context false a M U hATy hM0
  have hAExtTyW :
      __eo_typeof (bvMultSltExt false (Term.Numeral M) a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus T N)) := by
    rw [hAExtTy, hWidths]
  rcases bv_mult_slt_nils_ne unsigned x y a (Term.Numeral N)
      (Term.Numeral M) (Term.Numeral T) (Term.Numeral U) hRawTy with
    ⟨hNilXNe, hNilYNe⟩
  have hNilXNe' :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int WN))) ≠ Term.Stuck := by
    rw [hWideRound]
    simpa [hXExtTy] using hNilXNe
  have hNilYNe' :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int WN))) ≠ Term.Stuck := by
    rw [hWideRound]
    simpa [hYExtTy] using hNilYNe
  have hNilXEq :
      bvMultSltNil unsigned (Term.Numeral N) x =
        Term.Binary (native_nat_to_int WN) ((1#WN).toNat : Int) := by
    unfold bvMultSltNil
    rw [hXExtTy, ← hWideRound]
    exact mult_nil_bvmul_bitvec WN hNilXNe'
  have hNilYEq :
      bvMultSltNil unsigned (Term.Numeral N) y =
        Term.Binary (native_nat_to_int WN) ((1#WN).toNat : Int) := by
    unfold bvMultSltNil
    rw [hYExtTy, ← hWideRound]
    exact mult_nil_bvmul_bitvec WN hNilYNe'
  have hRawEq := bv_mult_slt_raw_eq_direct unsigned x y a
    (Term.Numeral N) (Term.Numeral M) (Term.Numeral T) (Term.Numeral U)
    hRawTy
  rw [hRawEq]
  have hXExtSmt := mult_smt_typeof_extend unsigned x T N
    hXSmtTy hT0 hN0
  have hYExtSmt := mult_smt_typeof_extend unsigned y T N
    hYSmtTy hT0 hN0
  have hAExtSmt := mult_smt_typeof_extend false a U M
    hASmtTy hU0 hM0
  rw [← hWidths] at hAExtSmt
  let Wide := native_int_to_nat (native_zplus T N)
  have hXExtSmt' :
      __smtx_typeof
          (__eo_to_smt (bvMultSltExt unsigned (Term.Numeral N) x)) =
        SmtType.BitVec Wide := by simpa [Wide] using hXExtSmt
  have hYExtSmt' :
      __smtx_typeof
          (__eo_to_smt (bvMultSltExt unsigned (Term.Numeral N) y)) =
        SmtType.BitVec Wide := by simpa [Wide] using hYExtSmt
  have hAExtSmt' :
      __smtx_typeof
          (__eo_to_smt (bvMultSltExt false (Term.Numeral M) a)) =
        SmtType.BitVec Wide := by simpa [Wide] using hAExtSmt
  have hWideNat : Wide = WN := by
    unfold Wide
    rw [← hWideRound]
    simp [native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hNilXSmt :
      __smtx_typeof
          (__eo_to_smt (bvMultSltNil unsigned (Term.Numeral N) x)) =
        SmtType.BitVec Wide := by
    rw [hNilXEq]
    change __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int WN) ((1#WN).toNat : Int)) = _
    rw [hWideNat]
    exact mult_smt_typeof_bitvec_payload 1#WN
  have hNilYSmt :
      __smtx_typeof
          (__eo_to_smt (bvMultSltNil unsigned (Term.Numeral N) y)) =
        SmtType.BitVec Wide := by
    rw [hNilYEq]
    change __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int WN) ((1#WN).toNat : Int)) = _
    rw [hWideNat]
    exact mult_smt_typeof_bitvec_payload 1#WN
  have hTimesXSmt := mult_smt_typeof_bvmul
    (bvMultSltExt false (Term.Numeral M) a)
    (bvMultSltNil unsigned (Term.Numeral N) x) Wide
    hAExtSmt' hNilXSmt
  have hTimesYSmt := mult_smt_typeof_bvmul
    (bvMultSltExt false (Term.Numeral M) a)
    (bvMultSltNil unsigned (Term.Numeral N) y) Wide
    hAExtSmt' hNilYSmt
  have hProdXSmt := mult_smt_typeof_bvmul
    (bvMultSltExt unsigned (Term.Numeral N) x)
    (bvMultSltTimesOne unsigned x a (Term.Numeral N) (Term.Numeral M))
    Wide hXExtSmt' (by have hsimpa := hTimesXSmt; (try simp [bvMultSltTimesOne] at hsimpa ⊢); exact hsimpa)
  have hProdYSmt := mult_smt_typeof_bvmul
    (bvMultSltExt unsigned (Term.Numeral N) y)
    (bvMultSltTimesOne unsigned y a (Term.Numeral N) (Term.Numeral M))
    Wide hYExtSmt' (by have hsimpa := hTimesYSmt; (try simp [bvMultSltTimesOne] at hsimpa ⊢); exact hsimpa)
  have hLhsBool := mult_smt_typeof_bvslt
    (bvMultSltProduct unsigned y a (Term.Numeral N) (Term.Numeral M))
    (bvMultSltProduct unsigned x a (Term.Numeral N) (Term.Numeral M))
    Wide (by simpa [bvMultSltProduct] using hProdYSmt)
    (by simpa [bvMultSltProduct] using hProdXSmt)
  let zeroT := Term.Apply
    (Term.UOp1 UserOp1.int_to_bv (Term.Numeral T)) (Term.Numeral 0)
  let zeroU := Term.Apply
    (Term.UOp1 UserOp1.int_to_bv (Term.Numeral U)) (Term.Numeral 0)
  have hZeroTSmt : __smtx_typeof (__eo_to_smt zeroT) =
      SmtType.BitVec (native_int_to_nat T) := by
    have hsimpa := smtx_typeof_int_to_bv_numerals T 0 hT0
    try simp [zeroT] at hsimpa ⊢
    exact hsimpa
  have hZeroUSmt : __smtx_typeof (__eo_to_smt zeroU) =
      SmtType.BitVec (native_int_to_nat U) := by
    have hsimpa := smtx_typeof_int_to_bv_numerals U 0 hU0
    try simp [zeroU] at hsimpa ⊢
    exact hsimpa
  let sub := Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x
  have hSubSmt := mult_smt_typeof_bvsub y x (native_int_to_nat T)
    hYSmtTy hXSmtTy
  have hSubEqBool := RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    sub zeroT (by simpa [sub] using hSubSmt.trans hZeroTSmt.symm)
    (by rw [hSubSmt]; simp)
  have hNotSubBool := RuleProofs.eo_has_bool_type_not_of_bool_arg _ hSubEqBool
  have hAEqBool := RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    a zeroU (hASmtTy.trans hZeroUSmt.symm) (by rw [hASmtTy]; simp)
  have hNotABool := RuleProofs.eo_has_bool_type_not_of_bool_arg _ hAEqBool
  have hOrderBool : RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp (if unsigned then UserOp.bvult else UserOp.bvslt)) y)
        x) := by
    cases unsigned with
    | false => exact mult_smt_typeof_bvslt y x _ hYSmtTy hXSmtTy
    | true => exact mult_smt_typeof_bvult y x _ hYSmtTy hXSmtTy
  have hSgtBool := mult_smt_typeof_bvsgt a zeroU _ hASmtTy hZeroUSmt
  have hOrderEqBool := RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by
      unfold RuleProofs.eo_has_bool_type at hOrderBool hSgtBool
      exact hOrderBool.trans hSgtBool.symm)
    (by
      unfold RuleProofs.eo_has_bool_type at hOrderBool
      rw [hOrderBool]
      simp)
  have hTrueBool := RuleProofs.eo_has_bool_type_true
  have hOrderTail := RuleProofs.eo_has_bool_type_and_of_bool_args _ _
    hOrderEqBool hTrueBool
  have hATail := RuleProofs.eo_has_bool_type_and_of_bool_args _ _
    hNotABool hOrderTail
  have hRhsBool := RuleProofs.eo_has_bool_type_and_of_bool_args _ _
    hNotSubBool hATail
  have hLhsSmtBool :
      __smtx_typeof
          (__eo_to_smt
            (bvMultSltLhs unsigned x y a (Term.Numeral N)
              (Term.Numeral M))) = SmtType.Bool := by
    unfold RuleProofs.eo_has_bool_type at hLhsBool
    exact hLhsBool
  have hRhsSmtBool :
      __smtx_typeof
          (__eo_to_smt
            (bvMultSltRhs unsigned x y a (Term.Numeral T)
              (Term.Numeral U))) = SmtType.Bool := by
    unfold RuleProofs.eo_has_bool_type at hRhsBool
    exact hRhsBool
  have hDirectBool := RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (bvMultSltLhs unsigned x y a (Term.Numeral N) (Term.Numeral M))
    (bvMultSltRhs unsigned x y a (Term.Numeral T) (Term.Numeral U))
    (hLhsSmtBool.trans hRhsSmtBool.symm)
    (by rw [hLhsSmtBool]; simp)
  exact hDirectBool

private theorem eval_bv_mult_slt_raw
    (Mdl : SmtModel) (hMdl : model_wf Mdl)
    (unsigned : Bool) (x y a n m tn an : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) = Term.Bool ->
    eo_interprets Mdl (bvMultSltGePrem n tn) true ->
    eo_interprets Mdl (bvMultSltGePrem m an) true ->
    __smtx_model_eval Mdl
        (__eo_to_smt (bvMultSltRawTerm unsigned x y a n m tn an)) =
      SmtValue.Boolean true := by
  intro hXTrans hYTrans hATrans hTnTrans hAnTrans hRawTy hNPrem hMPrem
  rcases bv_mult_slt_context unsigned x y a n m tn an hXTrans hYTrans
      hATrans hTnTrans hAnTrans hRawTy with
    ⟨T, U, N, K, rfl, rfl, rfl, rfl, hT0, hU0, hN0, hK0,
      hWidths, _hXTy, _hYTy, _hATy, hXSmtTy, hYSmtTy, hASmtTy⟩
  have hTN := bv_mult_slt_ge_of_premise Mdl N T hNPrem
  have hUK := bv_mult_slt_ge_of_premise Mdl K U hMPrem
  let TW := native_int_to_nat T
  let UW := native_int_to_nat U
  let NW := native_int_to_nat N
  let KW := native_int_to_nat K
  let WW := TW + NW
  have hTRound : native_nat_to_int TW = T := by
    simpa [TW] using native_int_to_nat_roundtrip T hT0
  have hURound : native_nat_to_int UW = U := by
    simpa [UW] using native_int_to_nat_roundtrip U hU0
  have hNRound : native_nat_to_int NW = N := by
    simpa [NW] using native_int_to_nat_roundtrip N hN0
  have hKRound : native_nat_to_int KW = K := by
    simpa [KW] using native_int_to_nat_roundtrip K hK0
  have hWideRound : native_nat_to_int WW = native_zplus T N := by
    calc
      native_nat_to_int WW =
          native_nat_to_int TW + native_nat_to_int NW := by
        simp [WW, native_nat_to_int, Smtm.native_nat_to_int]
      _ = T + N := by rw [hTRound, hNRound]
      _ = native_zplus T N := rfl
  have hNatWidths : WW = UW + KW := by
    have hNatWidthsInt :
        native_nat_to_int WW = native_nat_to_int (UW + KW) := by
      calc
        native_nat_to_int WW = native_zplus T N := hWideRound
        _ = native_zplus U K := hWidths
        _ = native_nat_to_int UW + native_nat_to_int KW := by
          rw [hURound, hKRound]
          rfl
        _ = native_nat_to_int (UW + KW) := by
          simp [native_nat_to_int, Smtm.native_nat_to_int]
    change Int.ofNat WW = Int.ofNat (UW + KW) at hNatWidthsInt
    exact Int.ofNat_inj.mp hNatWidthsInt
  have hWidthBound : TW + UW ≤ WW :=
    bv_mult_slt_nat_width_bound T U N K hT0 hU0 hN0 hK0
      hWidths hTN hUK
  rcases bitvec_eval_nat_payload Mdl hMdl x TW
      (by simpa [TW] using hXSmtTy) with ⟨X, hXEval, hXBound⟩
  rcases bitvec_eval_nat_payload Mdl hMdl y TW
      (by simpa [TW] using hYSmtTy) with ⟨Y, hYEval, hYBound⟩
  rcases bitvec_eval_nat_payload Mdl hMdl a UW
      (by simpa [UW] using hASmtTy) with ⟨A, hAEval, hABound⟩
  let xv : BitVec TW := ⟨X, hXBound⟩
  let yv : BitVec TW := ⟨Y, hYBound⟩
  let av : BitVec UW := ⟨A, hABound⟩
  have hXEval' :
      __smtx_model_eval Mdl (__eo_to_smt x) =
        SmtValue.Binary (TW : Int) (xv.toNat : Int) := by
    simpa [xv, native_nat_to_int, Smtm.native_nat_to_int] using hXEval
  have hYEval' :
      __smtx_model_eval Mdl (__eo_to_smt y) =
        SmtValue.Binary (TW : Int) (yv.toNat : Int) := by
    simpa [yv, native_nat_to_int, Smtm.native_nat_to_int] using hYEval
  have hAEval' :
      __smtx_model_eval Mdl (__eo_to_smt a) =
        SmtValue.Binary (UW : Int) (av.toNat : Int) := by
    simpa [av, native_nat_to_int, Smtm.native_nat_to_int] using hAEval
  have hXExtEval :
      __smtx_model_eval Mdl
          (__eo_to_smt (bvMultSltExt unsigned (Term.Numeral N) x)) =
        SmtValue.Binary (WW : Int)
          ((if unsigned then xv.zeroExtend WW else xv.signExtend WW).toNat : Int) := by
    cases unsigned with
    | false =>
        unfold bvMultSltExt
        simp only [Bool.false_eq_true, if_false]
        rw [eval_sign_extend_term, hXEval']
        have hVal := sign_extend_val_bitvec TW NW (xv.toNat : Int)
          (Int.natCast_nonneg _) (by exact_mod_cast xv.isLt)
        rw [Nat.add_comm NW TW] at hVal
        rw [← hNRound]
        simpa [WW, Nat.add_comm, native_nat_to_int,
          Smtm.native_nat_to_int, bitvec_ofInt_natCast_toNat] using hVal
    | true =>
        unfold bvMultSltExt
        simp only [if_true]
        rw [mult_eval_zero_extend_term, hXEval']
        have hVal := zero_extend_val_bitvec_local TW NW (xv.toNat : Int)
          (Int.natCast_nonneg _) (by exact_mod_cast xv.isLt)
        rw [← hNRound]
        simpa [WW, Nat.add_comm, native_nat_to_int,
          Smtm.native_nat_to_int, bitvec_ofInt_natCast_toNat] using hVal
  have hYExtEval :
      __smtx_model_eval Mdl
          (__eo_to_smt (bvMultSltExt unsigned (Term.Numeral N) y)) =
        SmtValue.Binary (WW : Int)
          ((if unsigned then yv.zeroExtend WW else yv.signExtend WW).toNat : Int) := by
    cases unsigned with
    | false =>
        unfold bvMultSltExt
        simp only [Bool.false_eq_true, if_false]
        rw [eval_sign_extend_term, hYEval']
        have hVal := sign_extend_val_bitvec TW NW (yv.toNat : Int)
          (Int.natCast_nonneg _) (by exact_mod_cast yv.isLt)
        rw [Nat.add_comm NW TW] at hVal
        rw [← hNRound]
        simpa [WW, Nat.add_comm, native_nat_to_int,
          Smtm.native_nat_to_int, bitvec_ofInt_natCast_toNat] using hVal
    | true =>
        unfold bvMultSltExt
        simp only [if_true]
        rw [mult_eval_zero_extend_term, hYEval']
        have hVal := zero_extend_val_bitvec_local TW NW (yv.toNat : Int)
          (Int.natCast_nonneg _) (by exact_mod_cast yv.isLt)
        rw [← hNRound]
        simpa [WW, Nat.add_comm, native_nat_to_int,
          Smtm.native_nat_to_int, bitvec_ofInt_natCast_toNat] using hVal
  have hAExtEval :
      __smtx_model_eval Mdl
          (__eo_to_smt (bvMultSltExt false (Term.Numeral K) a)) =
        SmtValue.Binary (WW : Int) ((av.signExtend WW).toNat : Int) := by
    unfold bvMultSltExt
    simp only [Bool.false_eq_true, if_false]
    rw [eval_sign_extend_term, hAEval']
    have hVal := sign_extend_val_bitvec UW KW (av.toNat : Int)
      (Int.natCast_nonneg _) (by exact_mod_cast av.isLt)
    rw [← hKRound]
    have hAWidth : KW + UW = WW := by
      simpa [Nat.add_comm] using hNatWidths.symm
    rw [hAWidth] at hVal
    simpa [hAWidth, native_nat_to_int, Smtm.native_nat_to_int,
      bitvec_ofInt_natCast_toNat] using hVal
  rcases bv_mult_slt_nils_ne unsigned x y a (Term.Numeral N)
      (Term.Numeral K) (Term.Numeral T) (Term.Numeral U) hRawTy with
    ⟨hNilXNe, hNilYNe⟩
  have hXExtTy := mult_extend_type_of_context unsigned x N T _hXTy hN0
  have hYExtTy := mult_extend_type_of_context unsigned y N T _hYTy hN0
  have hNilXNe' :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int WW))) ≠ Term.Stuck := by
    rw [hWideRound]
    simpa [hXExtTy] using hNilXNe
  have hNilYNe' :
      __eo_nil (Term.UOp UserOp.bvmul)
          (Term.Apply (Term.UOp UserOp.BitVec)
            (Term.Numeral (native_nat_to_int WW))) ≠ Term.Stuck := by
    rw [hWideRound]
    simpa [hYExtTy] using hNilYNe
  have hNilXEq :
      bvMultSltNil unsigned (Term.Numeral N) x =
        Term.Binary (native_nat_to_int WW) ((1#WW).toNat : Int) := by
    unfold bvMultSltNil
    rw [hXExtTy, ← hWideRound]
    exact mult_nil_bvmul_bitvec WW hNilXNe'
  have hNilYEq :
      bvMultSltNil unsigned (Term.Numeral N) y =
        Term.Binary (native_nat_to_int WW) ((1#WW).toNat : Int) := by
    unfold bvMultSltNil
    rw [hYExtTy, ← hWideRound]
    exact mult_nil_bvmul_bitvec WW hNilYNe'
  have hNilXEval :
      __smtx_model_eval Mdl
          (__eo_to_smt (bvMultSltNil unsigned (Term.Numeral N) x)) =
        SmtValue.Binary (WW : Int) ((1#WW).toNat : Int) := by
    rw [hNilXEq]
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using
      eval_binary Mdl (native_nat_to_int WW) ((1#WW).toNat : Int)
  have hNilYEval :
      __smtx_model_eval Mdl
          (__eo_to_smt (bvMultSltNil unsigned (Term.Numeral N) y)) =
        SmtValue.Binary (WW : Int) ((1#WW).toNat : Int) := by
    rw [hNilYEq]
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using
      eval_binary Mdl (native_nat_to_int WW) ((1#WW).toNat : Int)
  have hZeroTEval :
      __smtx_model_eval Mdl
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral T))
              (Term.Numeral 0))) =
        SmtValue.Binary (TW : Int) ((0#TW).toNat : Int) := by
    change __smtx_model_eval Mdl
        (SmtTerm.int_to_bv (SmtTerm.Numeral T) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_numerals]
    simp [native_nat_to_int, Smtm.native_nat_to_int,
      SmtEval.native_mod_total, ← hTRound]
  have hZeroUEval :
      __smtx_model_eval Mdl
          (__eo_to_smt
            (Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral U))
              (Term.Numeral 0))) =
        SmtValue.Binary (UW : Int) ((0#UW).toNat : Int) := by
    change __smtx_model_eval Mdl
        (SmtTerm.int_to_bv (SmtTerm.Numeral U) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_numerals]
    simp [native_nat_to_int, Smtm.native_nat_to_int,
      SmtEval.native_mod_total, ← hURound]
  have hRawEq := bv_mult_slt_raw_eq_direct unsigned x y a
    (Term.Numeral N) (Term.Numeral K) (Term.Numeral T) (Term.Numeral U)
    hRawTy
  rw [hRawEq]
  cases unsigned with
  | false =>
      change __smtx_model_eval Mdl
        (SmtTerm.eq
          (SmtTerm.bvslt
            (SmtTerm.bvmul
              (__eo_to_smt (bvMultSltExt false (Term.Numeral N) y))
              (SmtTerm.bvmul
                (__eo_to_smt (bvMultSltExt false (Term.Numeral K) a))
                (__eo_to_smt
                  (bvMultSltNil false (Term.Numeral N) y))))
            (SmtTerm.bvmul
              (__eo_to_smt (bvMultSltExt false (Term.Numeral N) x))
              (SmtTerm.bvmul
                (__eo_to_smt (bvMultSltExt false (Term.Numeral K) a))
                (__eo_to_smt
                  (bvMultSltNil false (Term.Numeral N) x)))))
          (SmtTerm.and
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x))
                (__eo_to_smt
                  (Term.Apply
                    (Term.UOp1 UserOp1.int_to_bv (Term.Numeral T))
                    (Term.Numeral 0)))))
            (SmtTerm.and
              (SmtTerm.not
                (SmtTerm.eq (__eo_to_smt a)
                  (__eo_to_smt
                    (Term.Apply
                      (Term.UOp1 UserOp1.int_to_bv (Term.Numeral U))
                      (Term.Numeral 0)))))
              (SmtTerm.and
                (SmtTerm.eq
                  (SmtTerm.bvslt (__eo_to_smt y) (__eo_to_smt x))
                  (SmtTerm.bvsgt (__eo_to_smt a)
                    (__eo_to_smt
                      (Term.Apply
                        (Term.UOp1 UserOp1.int_to_bv (Term.Numeral U))
                        (Term.Numeral 0)))))
                (SmtTerm.Boolean true))))) = SmtValue.Boolean true
      simp only [smtx_eval_eq_term_eq, smtx_eval_and_term_eq,
        smtx_eval_not_term_eq, smtx_eval_bvmul_term_eq,
        mult_eval_bvslt_term, mult_eval_bvsgt_term, mult_eval_bvsub_term,
        hXEval', hYEval', hAEval', hXExtEval, hYExtEval, hAExtEval,
        hNilXEval, hNilYEval, hZeroTEval, hZeroUEval,
        __smtx_model_eval]
      exact signed_mult_smt_values_all hWidthBound xv yv av
  | true =>
      change __smtx_model_eval Mdl
        (SmtTerm.eq
          (SmtTerm.bvslt
            (SmtTerm.bvmul
              (__eo_to_smt (bvMultSltExt true (Term.Numeral N) y))
              (SmtTerm.bvmul
                (__eo_to_smt (bvMultSltExt false (Term.Numeral K) a))
                (__eo_to_smt
                  (bvMultSltNil true (Term.Numeral N) y))))
            (SmtTerm.bvmul
              (__eo_to_smt (bvMultSltExt true (Term.Numeral N) x))
              (SmtTerm.bvmul
                (__eo_to_smt (bvMultSltExt false (Term.Numeral K) a))
                (__eo_to_smt
                  (bvMultSltNil true (Term.Numeral N) x)))))
          (SmtTerm.and
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.bvsub (__eo_to_smt y) (__eo_to_smt x))
                (__eo_to_smt
                  (Term.Apply
                    (Term.UOp1 UserOp1.int_to_bv (Term.Numeral T))
                    (Term.Numeral 0)))))
            (SmtTerm.and
              (SmtTerm.not
                (SmtTerm.eq (__eo_to_smt a)
                  (__eo_to_smt
                    (Term.Apply
                      (Term.UOp1 UserOp1.int_to_bv (Term.Numeral U))
                      (Term.Numeral 0)))))
              (SmtTerm.and
                (SmtTerm.eq
                  (SmtTerm.bvult (__eo_to_smt y) (__eo_to_smt x))
                  (SmtTerm.bvsgt (__eo_to_smt a)
                    (__eo_to_smt
                      (Term.Apply
                        (Term.UOp1 UserOp1.int_to_bv (Term.Numeral U))
                        (Term.Numeral 0)))))
                (SmtTerm.Boolean true))))) = SmtValue.Boolean true
      simp only [smtx_eval_eq_term_eq, smtx_eval_and_term_eq,
        smtx_eval_not_term_eq, smtx_eval_bvmul_term_eq,
        mult_eval_bvslt_term, mult_eval_bvult_term, mult_eval_bvsgt_term,
        mult_eval_bvsub_term, hXEval', hYEval', hAEval', hXExtEval,
        hYExtEval, hAExtEval, hNilXEval, hNilYEval, hZeroTEval,
        hZeroUEval, __smtx_model_eval]
      exact unsigned_mult_smt_values_all hWidthBound xv yv av

private theorem facts_bv_mult_slt_raw
    (Mdl : SmtModel) (hMdl : model_wf Mdl)
    (unsigned : Bool) (x y a n m tn an : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) = Term.Bool ->
    eo_interprets Mdl (bvMultSltGePrem n tn) true ->
    eo_interprets Mdl (bvMultSltGePrem m an) true ->
    eo_interprets Mdl (bvMultSltRawTerm unsigned x y a n m tn an) true := by
  intro hXTrans hYTrans hATrans hTnTrans hAnTrans hRawTy hNPrem hMPrem
  exact RuleProofs.eo_interprets_of_bool_eval Mdl _ true
    (typed_bv_mult_slt_raw unsigned x y a n m tn an hXTrans hYTrans
      hATrans hTnTrans hAnTrans hRawTy)
    (eval_bv_mult_slt_raw Mdl hMdl unsigned x y a n m tn an hXTrans
      hYTrans hATrans hTnTrans hAnTrans hRawTy hNPrem hMPrem)

theorem typed_bv_mult_slt_program
    (unsigned : Bool) (x y a n m tn an P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof
        (bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4) := by
  intro hXTrans hYTrans hATrans hNTrans hMTrans hTnTrans hAnTrans
    hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvMultSltProgram_normalize unsigned x y a n m tn an P1 P2 P3 P4
      hXTrans hYTrans hATrans hNTrans hMTrans hTnTrans hAnTrans hProg with
    ⟨_hP1, _hP2, _hP3, _hP4, hProgramEq⟩
  have hRawTy :
      __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_mult_slt_raw unsigned x y a n m tn an hXTrans hYTrans
    hATrans hTnTrans hAnTrans hRawTy

theorem facts_bv_mult_slt_program
    (Mdl : SmtModel) (hMdl : model_wf Mdl)
    (unsigned : Bool) (x y a n m tn an P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation tn ->
    RuleProofs.eo_has_smt_translation an ->
    __eo_typeof
        (bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4) =
      Term.Bool ->
    eo_interprets Mdl P1 true -> eo_interprets Mdl P2 true ->
    eo_interprets Mdl P3 true -> eo_interprets Mdl P4 true ->
    eo_interprets Mdl
      (bvMultSltProgram unsigned x y a n m tn an P1 P2 P3 P4) true := by
  intro hXTrans hYTrans hATrans hNTrans hMTrans hTnTrans hAnTrans
    hResultTy _hP1True _hP2True hP3True hP4True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvMultSltProgram_normalize unsigned x y a n m tn an P1 P2 P3 P4
      hXTrans hYTrans hATrans hNTrans hMTrans hTnTrans hAnTrans hProg with
    ⟨_hP1, _hP2, hP3, hP4, hProgramEq⟩
  have hRawTy :
      __eo_typeof (bvMultSltRawTerm unsigned x y a n m tn an) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hNPrem : eo_interprets Mdl (bvMultSltGePrem n tn) true := by
    simpa [hP3] using hP3True
  have hMPrem : eo_interprets Mdl (bvMultSltGePrem m an) true := by
    simpa [hP4] using hP4True
  rw [hProgramEq]
  exact facts_bv_mult_slt_raw Mdl hMdl unsigned x y a n m tn an
    hXTrans hYTrans hATrans hTnTrans hAnTrans hRawTy hNPrem hMPrem
