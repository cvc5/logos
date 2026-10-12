module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace UdivNestedShiftCases


theorem zero_le_bv {w : Nat} (x : BitVec w) : 0#w ≤ x := by
  simp [BitVec.le_def]

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

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

theorem ushiftRight_self_amount_eq_zero {w : Nat} (a : BitVec w) :
    a >>> a.toNat = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases ha : a.toNat = 0
  · simp [ha]
  · rw [Nat.div_eq_of_lt Nat.lt_two_pow_self]
    simp

theorem shiftLeft_one_ushiftRight_shiftLeft_one_le {w : Nat}
    (a : BitVec w) : (a >>> (a <<< 1).toNat) <<< 1 ≤ a := by
  simp only [BitVec.le_def, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]
  let k := a.toNat * 2 % 2 ^ w
  change ((a.toNat / 2 ^ k) * 2) % 2 ^ w ≤ a.toNat
  by_cases hk : k = 0
  · have hzero : a.toNat * 2 % 2 ^ w = 0 := by simpa [k] using hk
    rw [hk]
    simp only [Nat.pow_zero, Nat.div_one]
    rw [hzero]
    simp
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk
    have hpTwo : 2 ≤ 2 ^ k := Nat.one_lt_two_pow hk
    have hdiv := Nat.div_mul_le_self a.toNat (2 ^ k)
    have htwo : (a.toNat / 2 ^ k) * 2 ≤
        (a.toNat / 2 ^ k) * 2 ^ k :=
      Nat.mul_le_mul_left _ hpTwo
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.le_trans htwo hdiv)

theorem shiftLeft_one_ushiftRight_self_le {w : Nat} (a : BitVec w) :
    (a <<< 1) >>> (a <<< 1).toNat ≤ a := by
  simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.pow_one]
  let y := a.toNat * 2 % 2 ^ w
  change y / 2 ^ y ≤ a.toNat
  by_cases hy : y = 0
  · simp [hy]
  · have hyPos : 0 < y := Nat.pos_of_ne_zero hy
    have hpTwo : 2 ≤ 2 ^ y := Nat.one_lt_two_pow hy
    apply Nat.le_trans (Nat.div_le_div_left hpTwo (by decide : 0 < 2))
    change y / 2 ≤ a.toNat
    have hyle : y ≤ a.toNat * 2 := by
      dsimp [y]
      exact Nat.mod_le _ _
    exact (Nat.div_le_iff_le_mul (by decide : 0 < 2)).mpr (by omega)

theorem udiv14 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    ((s >>> (s <<< x.smtUDiv s).toNat) <<< 1) ≤ x := by
  let t := x.smtUDiv s
  by_cases hs0 : s = 0#w
  · subst s
    simp
    exact zero_le_bv _
  have hwPos : 0 < w := by omega
  by_cases htSmall : t.toNat < 2
  · rcases bitvec_eq_zero_or_one_of_toNat_lt_two hwPos t htSmall with ht | ht
    · change ((s >>> (s <<< t).toNat) <<< 1) ≤ x
      rw [ht]
      rw [BitVec.shiftLeft_zero']
      rw [ushiftRight_self_amount_eq_zero]
      simp
      exact zero_le_bv _
    · have hsLeX : s ≤ x := by
        simp only [BitVec.le_def]
        have hprod := smtUDiv_mul_le x s hs0
        change s.toNat * t.toNat ≤ x.toNat at hprod
        rw [ht] at hprod
        have hone : (1#w).toNat = 1 := by
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
        rw [hone] at hprod
        simpa using hprod
      have hle : ((s >>> (s <<< t).toNat) <<< 1) ≤ s := by
        rw [ht]
        rw [BitVec.shiftLeft_ofNat_eq]
        have hone : 1 % 2 ^ w = 1 :=
          Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
        rw [hone]
        exact shiftLeft_one_ushiftRight_shiftLeft_one_le s
      exact Nat.le_trans hle hsLeX
  · have htTwo : 2 ≤ t.toNat := by omega
    change ((s >>> (s <<< t).toNat) <<< 1) ≤ x
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.pow_one]
    have hmod : ((s >>> (s <<< t).toNat).toNat * 2) % 2 ^ w ≤
        (s >>> (s <<< t).toNat).toNat * 2 := Nat.mod_le _ _
    have hshift : (s >>> (s <<< t).toNat).toNat ≤ s.toNat := by
      rw [BitVec.toNat_ushiftRight]
      exact Nat.shiftRight_le _ _
    have htwo := Nat.mul_le_mul_right s.toNat htTwo
    have htwo' : s.toNat * 2 ≤ s.toNat * t.toNat := by
      simpa [Nat.mul_comm] using htwo
    have hprod := smtUDiv_mul_le x s hs0
    change s.toNat * t.toNat ≤ x.toNat at hprod
    have hshift2 := Nat.mul_le_mul_right 2 hshift
    exact Nat.le_trans hmod
      (Nat.le_trans hshift2 (Nat.le_trans htwo' hprod))

theorem udiv15 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    ((x.smtUDiv s <<< 1) >>> (x.smtUDiv s <<< s).toNat) ≤ x := by
  let t := x.smtUDiv s
  change ((t <<< 1) >>> (t <<< s).toNat) ≤ x
  by_cases hsSmall : s.toNat < 2
  · rcases bitvec_eq_zero_or_one_of_toNat_lt_two (by omega) s hsSmall with hs | hs
    · rw [hs]
      have ht0 := udiv3 x (0#w) rfl
      have ht : t = BitVec.allOnes w := by simpa [t, hs] using ht0
      rw [BitVec.shiftLeft_zero']
      have hzero : (t <<< 1) >>> t.toNat = 0#w := by
        apply BitVec.ushiftRight_eq_zero
        rw [ht, BitVec.toNat_allOnes]
        have hp : w < 2 ^ w := Nat.lt_two_pow_self
        omega
      rw [hzero]
      exact zero_le_bv _
    · rw [hs]
      have ht0 := udiv37 x (1#w) (x.smtUDiv (1#w)) rfl rfl
      have ht : t = x := by simpa [t, hs] using ht0
      rw [ht, BitVec.shiftLeft_ofNat_eq]
      have hone : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
      rw [hone]
      exact shiftLeft_one_ushiftRight_self_le x
  · have hsTwo : 2 ≤ s.toNat := by omega
    have hs0 : s ≠ 0#w := by
      intro hs
      subst s
      simp at hsTwo
    simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
    have hshift : (t <<< 1).toNat / 2 ^ (t <<< s).toNat ≤
        (t <<< 1).toNat := Nat.div_le_self _ _
    have hmod : (t <<< 1).toNat ≤ t.toNat * 2 := by
      simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]
      exact Nat.mod_le _ _
    have htwo := Nat.mul_le_mul_right t.toNat hsTwo
    have hprod := smtUDiv_mul_le x s hs0
    change s.toNat * t.toNat ≤ x.toNat at hprod
    have htwo' : t.toNat * 2 ≤ s.toNat * t.toNat := by
      simpa [Nat.mul_comm] using htwo
    exact Nat.le_trans hshift (Nat.le_trans hmod (Nat.le_trans htwo' hprod))

end UdivNestedShiftCases
end BvAbstraction

