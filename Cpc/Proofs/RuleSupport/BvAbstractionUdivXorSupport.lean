module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace UdivXorCases

theorem zero_le_bv {w : Nat} (x : BitVec w) : 0#w ≤ x := by
  simp [BitVec.le_def]

theorem nat_xor_le_add (a b : Nat) : a ^^^ b ≤ a + b := by
  have hmask : (a ^^^ b) &&& (a ||| b) = a ^^^ b := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  calc
    a ^^^ b = (a ^^^ b) &&& (a ||| b) := hmask.symm
    _ ≤ a ||| b := Nat.and_le_right
    _ ≤ a + b := nat_or_le_add a b

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

theorem udiv25 {w : Nat} (x s : BitVec w) :
    (x.smtUDiv s ^^^
      (x.smtUDiv s >>> (s >>> 1).toNat)) ≤ x := by
  by_cases hs0 : s = 0#w
  · subst s
    have hz : (0#w >>> 1) = 0#w := by simp
    rw [hz]
    simp [BitVec.smtUDiv]
    exact zero_le_bv _
  · have hsPos : 0 < s.toNat :=
      Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs0)
    by_cases hs1n : s.toNat = 1
    · have hs1 : s = 1#w := by
        apply BitVec.eq_of_toNat_eq
        rw [hs1n]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt]
        exact Nat.one_lt_two_pow (by
          intro hw
          subst w
          exact hs0 (BitVec.eq_nil s))
      rw [hs1]
      have hw0 : w ≠ 0 := by
        intro hw
        subst w
        exact hs0 (BitVec.eq_nil s)
      have hone0 : (1#w) ≠ 0#w := by simp [hw0]
      have hshift : (1#w >>> 1) = 0#w := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight]
        have hone : (1#w).toNat = 1 := by
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw0)]
        rw [hone]
        simp
      rw [BitVec.smtUDiv_eq, if_neg hone0, BitVec.udiv_one, hshift]
      simp
      exact zero_le_bv _
    · have hsTwo : 2 ≤ s.toNat := by omega
      simp only [BitVec.le_def, BitVec.toNat_xor,
        BitVec.toNat_ushiftRight]
      have hshift :
          (x.smtUDiv s).toNat >>> (s >>> 1).toNat ≤
            (x.smtUDiv s).toNat := Nat.shiftRight_le _ _
      have hxor := nat_xor_le_add (x.smtUDiv s).toNat
        ((x.smtUDiv s).toNat >>> (s >>> 1).toNat)
      have hprod := smtUDiv_mul_le x s hs0
      have hsum : (x.smtUDiv s).toNat +
          ((x.smtUDiv s).toNat >>> (s >>> 1).toNat) ≤
          2 * (x.smtUDiv s).toNat := by omega
      have htwo := Nat.mul_le_mul_right (x.smtUDiv s).toNat hsTwo
      have htwo' : 2 * (x.smtUDiv s).toNat ≤
          s.toNat * (x.smtUDiv s).toNat := by
        simpa [Nat.mul_comm] using htwo
      simpa only [BitVec.toNat_ushiftRight] using
        (Nat.le_trans hxor (Nat.le_trans hsum
          (Nat.le_trans htwo' hprod)))

theorem udiv26 {w : Nat} (x s : BitVec w) :
    (s ^^^ (s >>> (x.smtUDiv s >>> 1).toNat)) ≤ x := by
  let t := x.smtUDiv s
  by_cases hs0 : s = 0#w
  · subst s
    simp
    exact zero_le_bv _
  have hw0 : w ≠ 0 := by
    intro hw
    subst w
    exact hs0 (BitVec.eq_nil s)
  have hOneShift : (1#w >>> 1) = 0#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight]
    have hone : (1#w).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw0)]
    rw [hone]
    simp
  by_cases htSmall : t.toNat < 2
  · have htCases : t = 0#w ∨ t = 1#w := by
      by_cases ht0 : t.toNat = 0
      · left
        apply BitVec.eq_of_toNat_eq
        simp [ht0]
      · have ht1 : t.toNat = 1 := by omega
        right
        apply BitVec.eq_of_toNat_eq
        simp only [ht1, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw0)]
    rcases htCases with ht | ht
    · rw [show x.smtUDiv s = t by rfl, ht]
      simp
      exact zero_le_bv _
    · rw [show x.smtUDiv s = t by rfl, ht, hOneShift]
      simp
      exact zero_le_bv _
  · have htTwo : 2 ≤ t.toNat := by omega
    simp only [BitVec.le_def, BitVec.toNat_xor,
      BitVec.toNat_ushiftRight]
    have hshift : s.toNat >>> (t >>> 1).toNat ≤ s.toNat :=
      Nat.shiftRight_le _ _
    have hxor := nat_xor_le_add s.toNat (s.toNat >>> (t >>> 1).toNat)
    have hprod := smtUDiv_mul_le x s hs0
    change s.toNat * t.toNat ≤ x.toNat at hprod
    have hsum : s.toNat + (s.toNat >>> (t >>> 1).toNat) ≤
        2 * s.toNat := by omega
    have htwo := Nat.mul_le_mul_left s.toNat htTwo
    have htwo' : 2 * s.toNat ≤ s.toNat * t.toNat := by
      simpa [Nat.mul_comm] using htwo
    simpa only [BitVec.toNat_ushiftRight] using
      (Nat.le_trans hxor (Nat.le_trans hsum
        (Nat.le_trans htwo' hprod)))

end UdivXorCases
end BvAbstraction

