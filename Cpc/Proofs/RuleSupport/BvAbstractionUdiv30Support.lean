module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace Udiv30Case

theorem width_lt_two_pow_pred (w : Nat) (hw : 3 ≤ w) :
    w < 2 ^ (w - 1) := by
  induction w with
  | zero => omega
  | succ w ih =>
      by_cases h3 : w = 2
      · subst w
        decide
      · have hw' : 3 ≤ w := by omega
        have hi := ih hw'
        have hp : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
        calc
          w + 1 ≤ 2 ^ (w - 1) := by omega
          _ < 2 ^ (w - 1) + 2 ^ (w - 1) := by omega
          _ = 2 ^ w := Nat.two_pow_pred_add_two_pow_pred (by omega)

theorem one_shift_toNat {w : Nat} (hw : 0 < w) (x : BitVec w) :
    (1#w <<< x.toNat).toNat = 2 ^ x.toNat % 2 ^ w := by
  rw [BitVec.toNat_shiftLeft]
  have hone : (1#w).toNat = 1 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hw))]
  rw [hone, Nat.one_shiftLeft]

theorem quotient_nat {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    (x.smtUDiv s).toNat = x.toNat / s.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]

theorem udiv30 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ x.smtUDiv s + (1#w + (1#w <<< x.toNat)) := by
  let q := x.smtUDiv s
  change x ≠ q + (1#w + (1#w <<< x.toNat))
  intro h
  have hp1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hone : (1#w).toNat = 1 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hp1]
  by_cases hs : s = 0#w
  · subst s
    have hq : q = BitVec.allOnes w := by
      simpa [q] using udiv3 x (0#w) rfl
    have hcancel : q + 1#w = 0#w := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, hq, BitVec.toNat_allOnes, hone,
        BitVec.toNat_ofNat, Nat.zero_mod]
      rw [show (2 ^ w - 1 + 1) = 2 ^ w by omega, Nat.mod_self]
    rw [← BitVec.add_assoc, hcancel, BitVec.zero_add] at h
    by_cases hxw : x.toNat < w
    · have hn := congrArg BitVec.toNat h
      rw [one_shift_toNat (by omega) x,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hxw)] at hn
      have hpowx : x.toNat < 2 ^ x.toNat := Nat.lt_two_pow_self
      omega
    · have hwx : w ≤ x.toNat := by omega
      rw [BitVec.shiftLeft_eq_zero hwx] at h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hn
      omega
  have hqNat : q.toNat = x.toNat / s.toNat := by
    dsimp [q]
    exact quotient_nat x s hs
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  have hqLeX : q.toNat ≤ x.toNat := by
    rw [hqNat]
    exact Nat.div_le_self _ _
  by_cases hxw : x.toNat < w
  · have hshift : (1#w <<< x.toNat).toNat = 2 ^ x.toNat := by
      rw [one_shift_toNat (by omega) x,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hxw)]
    have hxSucc : x.toNat + 1 ≤ w := by omega
    have hwBound := width_lt_two_pow_pred w hw
    have hrawLt : q.toNat + (1 + 2 ^ x.toNat) < 2 ^ w := by
      have hpowLe : 2 ^ x.toNat ≤ 2 ^ (w - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have htwice := Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w)
      omega
    have hinnerLt : 1 + 2 ^ x.toNat < 2 ^ w := by omega
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, hone, hshift] at hn
    rw [Nat.mod_eq_of_lt hinnerLt] at hn
    rw [Nat.mod_eq_of_lt hrawLt] at hn
    have hpowPos : 0 < 2 ^ x.toNat := Nat.two_pow_pos _
    have hpowX : x.toNat < 2 ^ x.toNat := Nat.lt_two_pow_self
    omega
  · have hwx : w ≤ x.toNat := by omega
    have hshift : (1#w <<< x.toNat) = 0#w :=
      BitVec.shiftLeft_eq_zero hwx
    rw [hshift] at h
    simp only [BitVec.add_zero] at h
    by_cases hsOne : s.toNat = 1
    · have hqEq : q = x := by
        apply BitVec.eq_of_toNat_eq
        rw [hqNat, hsOne]
        simp
      rw [hqEq] at h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, hone] at hn
      have hxlt := x.isLt
      by_cases hsucc : x.toNat + 1 < 2 ^ w
      · rw [Nat.mod_eq_of_lt hsucc] at hn
        omega
      · have heq : x.toNat + 1 = 2 ^ w := by omega
        rw [heq, Nat.mod_self] at hn
        omega
    · have hsTwo : 2 ≤ s.toNat := by omega
      have hqHalf : 2 * q.toNat ≤ x.toNat := by
        rw [hqNat]
        have hd : x.toNat / s.toNat ≤ x.toNat / 2 :=
          Nat.div_le_div_left hsTwo (by decide)
        have hm := Nat.mul_div_le x.toNat 2
        omega
      have hxThree : 3 ≤ x.toNat := by omega
      have hqSuccLt : q.toNat + 1 < x.toNat := by omega
      have hrawLt : q.toNat + 1 < 2 ^ w :=
        Nat.lt_trans hqSuccLt x.isLt
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, hone] at hn
      rw [Nat.mod_eq_of_lt hrawLt] at hn
      omega

end Udiv30Case
end BvAbstraction
