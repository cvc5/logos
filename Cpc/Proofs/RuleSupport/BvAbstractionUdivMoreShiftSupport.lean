module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace UdivMoreShiftCases

theorem succ_le_two_pow_of_pos (n : Nat) (hn : 0 < n) : n + 1 ≤ 2 ^ n := by
  exact Nat.lt_two_pow_self

theorem nat_udiv_shift_lt (x s : Nat) (hs : 0 < s) :
    x / 2 ^ (x / s) < s := by
  let q := x / s
  have hxlt : x < s * (q + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self (x / s))
    simpa [q, Nat.mul_comm] using h
  by_cases hq : q = 0
  · rw [hq] at hxlt
    simp only [Nat.zero_add, Nat.mul_one] at hxlt
    have hq' : x / s = 0 := by simpa [q] using hq
    simp only [hq', Nat.pow_zero, Nat.div_one]
    exact hxlt
  · have hpow : q + 1 ≤ 2 ^ q :=
      succ_le_two_pow_of_pos q (Nat.pos_of_ne_zero hq)
    have hmul := Nat.mul_le_mul_left s hpow
    have hxb : x < s * 2 ^ q := Nat.lt_of_lt_of_le hxlt hmul
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).mpr
      (by simpa [Nat.mul_comm] using hxb)

theorem udiv19 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x >>> (x.smtUDiv s).toNat ≠ s ||| x.smtUDiv s := by
  intro h
  by_cases hs : s = 0#w
  · subst s
    have hq : x.smtUDiv 0#w = BitVec.allOnes w := udiv3 x (0#w) rfl
    rw [hq, BitVec.zero_or] at h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_allOnes,
      Nat.shiftRight_eq_div_pow] at hn
    have hshift : x.toNat / 2 ^ (2 ^ w - 1) = 0 := by
      rw [Nat.div_eq_of_lt]
      exact Nat.lt_of_lt_of_le x.isLt
        (Nat.pow_le_pow_right (by decide) (by
          have hp : w ≤ 2 ^ w - 1 := by
            have hself : w < 2 ^ w := Nat.lt_two_pow_self
            omega
          exact hp))
    rw [hshift] at hn
    have hp := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega
  · have hsPos : 0 < s.toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
    have hlt := nat_udiv_shift_lt x.toNat s.toNat hsPos
    have hsLe : s.toNat ≤ (s ||| x.smtUDiv s).toNat := by
      simp only [BitVec.toNat_or]
      exact nat_le_or_left _ _
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hn
    have hqNat : (x.smtUDiv s).toNat = x.toNat / s.toNat := by
      rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
    rw [hqNat] at hn
    omega

theorem nat_udiv31 (x s : Nat) (hs : 0 < s) :
    (x + x / s) / 2 ^ (x / s) ≤ s := by
  let q := x / s
  have hxlt : x < s * (q + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self (x / s))
    simpa [q, Nat.mul_comm] using h
  by_cases hq : q = 0
  · rw [hq] at hxlt
    simp only [Nat.zero_add, Nat.mul_one] at hxlt
    have hq' : x / s = 0 := by simpa [q] using hq
    simp only [hq', Nat.add_zero, Nat.pow_zero, Nat.div_one]
    exact Nat.le_of_lt hxlt
  · have hpow : q + 1 ≤ 2 ^ q :=
      succ_le_two_pow_of_pos q (Nat.pos_of_ne_zero hq)
    have hmul := Nat.mul_le_mul_left (s + 1) hpow
    have hbound : x + q < (s + 1) * 2 ^ q := by
      have hsq : s * (q + 1) + q ≤ (s + 1) * (q + 1) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
        omega
      have hmid : x + q < (s + 1) * (q + 1) := by omega
      exact Nat.lt_of_lt_of_le hmid hmul
    have hdiv : (x + q) / 2 ^ q < s + 1 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).mpr
        (by simpa [Nat.mul_comm] using hbound)
    have hle : (x + q) / 2 ^ q ≤ s := by omega
    simpa only [q] using hle

theorem udiv31 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (x + x.smtUDiv s) >>> (x.smtUDiv s).toNat ≤ s := by
  by_cases hs : s = 0#w
  · subst s
    have hq : x.smtUDiv 0#w = BitVec.allOnes w := udiv3 x (0#w) rfl
    rw [hq]
    have hzero : (x + BitVec.allOnes w) >>> (BitVec.allOnes w).toNat = 0#w := by
      apply BitVec.ushiftRight_eq_zero
      rw [BitVec.toNat_allOnes]
      have hself : w < 2 ^ w := Nat.lt_two_pow_self
      omega
    rw [hzero]
    simp [BitVec.le_def]
  · simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    have hqNat : (x.smtUDiv s).toNat = x.toNat / s.toNat := by
      rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
    rw [hqNat]
    have hadd : (x + x.smtUDiv s).toNat ≤ x.toNat + x.toNat / s.toNat := by
      simp only [BitVec.toNat_add, hqNat]
      exact Nat.mod_le _ _
    exact Nat.le_trans (Nat.div_le_div_right hadd)
      (nat_udiv31 x.toNat s.toNat
        (Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)))

end UdivMoreShiftCases
end BvAbstraction

