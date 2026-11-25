module

public import Cpc.Proofs.RuleSupport.BvAbstractionUdiv32Support
import all Cpc.Proofs.RuleSupport.BvAbstractionUdiv32Support

public section

namespace BvAbstraction
namespace Urem13Case

theorem low3_zero_ne_one {w : Nat} (hw : 3 ≤ w) : (0#w) ≠ 1#w := by
  intro h
  have hl := congrArg low3 h
  rw [low3_one hw] at hl
  simp [low3] at hl

theorem urem13_zero_divisor {w : Nat} (hw : 3 ≤ w) (x : BitVec w) :
    x ≠ -x ||| -(~~~x) := by
  intro h
  have hinc : -(~~~x) = x + 1#w := by
    rw [BitVec.neg_eq_not_add, BitVec.not_not]
  rw [hinc] at h
  have hl := congrArg low3 h
  rw [low3_or, low3_neg hw, low3_add hw, low3_one hw] at hl
  have hbad : low3 x ≠ -low3 x ||| (low3 x + 1#3) := by bv_decide
  exact hbad hl

theorem pow_and_eq_zero_of_lt (n e : Nat) (he : e < 2 ^ n) :
    (2 ^ n) &&& e = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : n = i
  · subst i
    rw [Nat.testBit_lt_two_pow he]
    simp
  · simp [hi]

theorem urem13 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ -x ||| -(~~~(x % s)) := by
  let r := x % s
  change x ≠ -x ||| -(~~~r)
  by_cases hs : s = 0#w
  · subst s
    simpa [r] using urem13_zero_divisor hw x
  intro h
  have hinc : -(~~~r) = r + 1#w := by
    rw [BitVec.neg_eq_not_add, BitVec.not_not]
  rw [hinc] at h
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  have hrlt : r.toNat < s.toNat := by
    dsimp [r]
    exact Nat.mod_lt _ hsPos
  have hrLeX : r.toNat ≤ x.toNat := by
    dsimp [r]
    exact Nat.mod_le _ _
  have hrSuccLt : r.toNat + 1 < 2 ^ w :=
    Nat.lt_of_le_of_lt (by omega) s.isLt
  have hone : (1#w).toNat = 1 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have hrInc : (r + 1#w).toNat = r.toNat + 1 := by
    simp only [BitVec.toNat_add, hone]
    rw [Nat.mod_eq_of_lt hrSuccLt]
  by_cases hx0 : x = 0#w
  · subst x
    have hr0 : r = 0#w := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      have : r.toNat = 0 := by simpa using hrLeX
      exact this
    rw [hr0] at h
    have h01 : (0#w) = 1#w := by simpa using h
    exact (low3_zero_ne_one hw) h01
  have hxPos : 0 < x.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hx0)
  have hneg : (-x).toNat = 2 ^ w - x.toNat :=
    BitVec.toNat_neg_of_pos (by simpa [BitVec.lt_def] using hxPos)
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_or, hneg, hrInc] at hn
  let P := 2 ^ w
  let H := 2 ^ (w - 1)
  have hP : P = 2 * H := by
    simpa [P, H, Nat.two_mul] using
      (Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w)).symm
  have hPLarge : 8 ≤ P := by
    change 2 ^ 3 ≤ 2 ^ w
    exact Nat.pow_le_pow_right (by decide) hw
  change x.toNat = (P - x.toNat) ||| (r.toNat + 1) at hn
  have hnegLeX : P - x.toNat ≤ x.toNat := by
    have hle := nat_le_or_left (P - x.toNat) (r.toNat + 1)
    omega
  have hHalfLeX : H ≤ x.toNat := by omega
  have hrLtX : r.toNat < x.toNat := by
    by_cases heq : r.toNat = x.toNat
    · have hxltS : x.toNat < s.toNat := by omega
      have hrEqX : r.toNat = x.toNat := by
        dsimp [r]
        rw [Nat.mod_eq_of_lt hxltS]
      have hnegLtHalf : P - x.toNat ≤ H := by omega
      have hincGtX : x.toNat < r.toNat + 1 := by omega
      have hle := nat_le_or_right (P - x.toNat) (r.toNat + 1)
      omega
    · omega
  have hxLeTwoR : x.toNat ≤ 2 * r.toNat := by
    by_cases hxAll : x.toNat = P - 1
    · have horLe := nat_or_le_add (P - x.toNat) (r.toNat + 1)
      rw [hxAll] at hn horLe
      have hnegOne : P - (P - 1) = 1 := by omega
      rw [hnegOne] at hn horLe
      omega
    · have hxLePredPred : x.toNat ≤ P - 2 := by
        have hxlt : x.toNat < P := by simpa [P] using x.isLt
        omega
      by_cases hxHalf : x.toNat = H
      · have heLe : r.toNat + 1 ≤ H := by
          have hle := nat_le_or_right (P - x.toNat) (r.toNat + 1)
          omega
        by_cases heq : r.toNat + 1 = H
        · omega
        · have heLt : r.toNat + 1 < H := by omega
          have hhand : H &&& (r.toNat + 1) = 0 :=
            pow_and_eq_zero_of_lt (w - 1) (r.toNat + 1) (by simpa [H] using heLt)
          have horAnd := Udiv32Case.nat_or_add_and H (r.toNat + 1)
          rw [hhand, Nat.add_zero] at horAnd
          rw [hxHalf, hP] at hn
          have hpSub : 2 * H - H = H := by omega
          rw [hpSub] at hn
          omega
      · have hxGtHalf : H < x.toNat := by omega
        have hnegLtHalf : P - x.toNat < H := by omega
        have heHalf : H ≤ r.toNat + 1 := by
          by_cases heLt : r.toNat + 1 < H
          · have horLt := Nat.or_lt_two_pow hnegLtHalf (by simpa [H] using heLt)
            change (P - x.toNat) ||| (r.toNat + 1) < H at horLt
            omega
          · omega
        omega
  have hdecomp := Nat.mod_add_div x.toNat s.toNat
  change r.toNat + s.toNat * (x.toNat / s.toNat) = x.toNat at hdecomp
  have hqPos : 0 < x.toNat / s.toNat := by
    apply Nat.div_pos
    · by_cases hxlt : x.toNat < s.toNat
      · have hrEq : r.toNat = x.toNat := by
          dsimp [r]
          rw [Nat.mod_eq_of_lt hxlt]
        omega
      · omega
    · exact hsPos
  have hsLeProd : s.toNat ≤ s.toNat * (x.toNat / s.toNat) := by
    have hm := Nat.mul_le_mul_left s.toNat hqPos
    simpa using hm
  omega

end Urem13Case
end BvAbstraction
