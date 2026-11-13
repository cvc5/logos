module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace UdivMaskCases

theorem zero_le_bv {w : Nat} (x : BitVec w) : 0#w ≤ x := by
  simp [BitVec.le_def]

theorem le_allOnes {w : Nat} (x : BitVec w) : x ≤ BitVec.allOnes w := by
  simp only [BitVec.le_def, BitVec.toNat_allOnes]
  have hx := x.isLt
  omega

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

theorem shiftLeft_one_lsb_false {w : Nat} (x : BitVec w) :
    (x <<< 1).getLsbD 0 = false := by
  simp [BitVec.getLsbD]

theorem and_shiftLeft_one_even {w : Nat} (a b : BitVec w) :
    (a &&& (b <<< 1)).toNat % 2 = 0 := by
  apply mod_two_zero_of_lsb_false
  rw [BitVec.getLsbD_and, shiftLeft_one_lsb_false]
  simp

theorem bitvec_eq_zero_or_one_of_toNat_lt_two {w : Nat} (hw : 0 < w)
    (x : BitVec w) (h : x.toNat < 2) : x = 0#w ∨ x = 1#w := by
  by_cases hx : x.toNat = 0
  · left
    apply BitVec.eq_of_toNat_eq
    simp [hx]
  · have hx1 : x.toNat = 1 := by omega
    right
    apply BitVec.eq_of_toNat_eq
    simp only [hx1, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hw))]

theorem udiv17 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    ((x ||| x.smtUDiv s) &&& (s <<< 1)) ≤ x := by
  let t := x.smtUDiv s
  by_cases hs0 : s = 0#w
  · subst s
    simp
    exact zero_le_bv _
  have hwPos : 0 < w := by omega
  by_cases htSmall : t.toNat < 2
  · rcases bitvec_eq_zero_or_one_of_toNat_lt_two hwPos t htSmall with ht | ht
    · change ((x ||| t) &&& (s <<< 1)) ≤ x
      rw [ht]
      simp only [BitVec.or_zero]
      simp only [BitVec.le_def, BitVec.toNat_and]
      exact Nat.and_le_left
    · change ((x ||| t) &&& (s <<< 1)) ≤ x
      rw [ht]
      simp only [BitVec.le_def]
      have heven := and_shiftLeft_one_even (x ||| 1#w) s
      have hone : (1#w).toNat = 1 := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      have hle : ((x ||| 1#w) &&& (s <<< 1)).toNat ≤ x.toNat ||| 1 := by
        simp only [BitVec.toNat_and, BitVec.toNat_or, hone]
        exact Nat.and_le_left
      rw [nat_or_one] at hle
      split at hle
      · omega
      · omega
  · have htTwo : 2 ≤ t.toNat := by omega
    change ((x ||| t) &&& (s <<< 1)) ≤ x
    simp only [BitVec.le_def, BitVec.toNat_and, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.pow_one]
    have hand : (x.toNat ||| t.toNat) &&&
        (s.toNat * 2 % 2 ^ w) ≤ s.toNat * 2 % 2 ^ w := Nat.and_le_right
    have hmod : s.toNat * 2 % 2 ^ w ≤ s.toNat * 2 := Nat.mod_le _ _
    have htwo := Nat.mul_le_mul_left s.toNat htTwo
    have hprod := smtUDiv_mul_le x s hs0
    change s.toNat * t.toNat ≤ x.toNat at hprod
    exact Nat.le_trans hand (Nat.le_trans hmod (Nat.le_trans htwo hprod))

theorem udiv18 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    ((x ||| s) &&& (x.smtUDiv s <<< 1)) ≤ x := by
  let t := x.smtUDiv s
  by_cases hsSmall : s.toNat < 2
  · rcases bitvec_eq_zero_or_one_of_toNat_lt_two (by omega) s hsSmall with hs | hs
    · rw [hs]
      rw [BitVec.or_zero]
      simp only [BitVec.le_def, BitVec.toNat_and]
      exact Nat.and_le_left
    · rw [hs]
      have hone0 : (1#w) ≠ 0#w := by simp [show w ≠ 0 by omega]
      rw [BitVec.smtUDiv_eq, if_neg hone0, BitVec.udiv_one]
      simp only [BitVec.le_def]
      have heven := and_shiftLeft_one_even (x ||| 1#w) x
      have hone : (1#w).toNat = 1 := by
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      have hle : ((x ||| 1#w) &&& (x <<< 1)).toNat ≤ x.toNat ||| 1 := by
        simp only [BitVec.toNat_and, BitVec.toNat_or, hone]
        exact Nat.and_le_left
      rw [nat_or_one] at hle
      split at hle
      · omega
      · omega
  · have hsTwo : 2 ≤ s.toNat := by omega
    have hs0 : s ≠ 0#w := by
      intro hs
      subst s
      simp at hsTwo
    simp only [BitVec.le_def, BitVec.toNat_and, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.pow_one]
    have hand : (x.toNat ||| s.toNat) &&&
        ((x.smtUDiv s).toNat * 2 % 2 ^ w) ≤
        (x.smtUDiv s).toNat * 2 % 2 ^ w := Nat.and_le_right
    have hmod : (x.smtUDiv s).toNat * 2 % 2 ^ w ≤
        (x.smtUDiv s).toNat * 2 := Nat.mod_le _ _
    have htwo := Nat.mul_le_mul_right (x.smtUDiv s).toNat hsTwo
    have hprod := smtUDiv_mul_le x s hs0
    have htwo' : (x.smtUDiv s).toNat * 2 ≤
        s.toNat * (x.smtUDiv s).toNat := by
      simpa [Nat.mul_comm] using htwo
    exact Nat.le_trans hand (Nat.le_trans hmod (Nat.le_trans htwo' hprod))

end UdivMaskCases
end BvAbstraction

