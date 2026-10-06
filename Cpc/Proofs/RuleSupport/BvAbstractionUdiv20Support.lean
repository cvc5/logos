module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace Udiv20Case

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

theorem self_ne_not {w : Nat} (hw : 3 ≤ w) (x : BitVec w) : x ≠ ~~~x := by
  apply ne_of_low3_ne
  rw [low3_not hw]
  bv_decide

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

theorem two_pow_factor_two (w : Nat) (hw : 0 < w) :
    2 ^ w = 2 * 2 ^ (w - 1) := by
  cases w with
  | zero => omega
  | succ w =>
    rw [Nat.pow_succ]
    simp [Nat.mul_comm]

theorem udiv20 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s ≠ ~~~(s >>> (x.smtUDiv s >>> 1).toNat) := by
  let t := x.smtUDiv s
  change s ≠ ~~~(s >>> (t >>> 1).toNat)
  by_cases hs : s = 0#w
  · subst s
    intro h
    have hnot : ~~~(0#w >>> (t >>> 1).toNat) = BitVec.allOnes w := by simp
    rw [hnot] at h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.zero_mod,
      BitVec.toNat_allOnes] at hn
    have hp := Nat.one_lt_two_pow (by omega : w ≠ 0)
    omega
  by_cases htSmall : t.toNat < 2
  · rcases bitvec_eq_zero_or_one_of_toNat_lt_two (by omega) t htSmall with ht | ht
    · change s ≠ ~~~(s >>> (t >>> 1).toNat)
      rw [ht]
      simp
      exact self_ne_not hw s
    · change s ≠ ~~~(s >>> (t >>> 1).toNat)
      rw [ht]
      have hshift : (1#w >>> 1) = 0#w := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
        simp
      rw [hshift]
      simp
      exact self_ne_not hw s
  · have htTwo : 2 ≤ t.toNat := by omega
    intro heq
    have hn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_not, BitVec.toNat_ushiftRight] at hn
    have hshift : s.toNat >>> (t >>> 1).toNat ≤ s.toNat :=
      Nat.shiftRight_le _ _
    have hshift' : s.toNat >>> (t.toNat >>> 1) ≤ s.toNat := by
      simpa only [BitVec.toNat_ushiftRight] using hshift
    have hprod := smtUDiv_mul_le x s hs
    change s.toNat * t.toNat ≤ x.toNat at hprod
    have htwo := Nat.mul_le_mul_left s.toNat htTwo
    have hxlt := x.isLt
    have hpFactor := two_pow_factor_two w (by omega)
    omega

end Udiv20Case
end BvAbstraction

