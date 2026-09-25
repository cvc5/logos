module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace Udiv36Case

theorem setWidth_one {w k : Nat} (hk : 0 < k) (hkw : k ≤ w) :
    (1#w).setWidth k = 1#k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt (by omega : 0 < w))),
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hk))]

theorem setWidth_neg {w k : Nat} (hk : 0 < k) (hkw : k ≤ w) (x : BitVec w) :
    (-x).setWidth k = -(x.setWidth k) := by
  rw [BitVec.neg_eq_not_add, BitVec.setWidth_add _ _ hkw,
    BitVec.setWidth_not hkw, setWidth_one hk hkw,
    ← BitVec.neg_eq_not_add]

theorem setWidth_sub {w k : Nat} (hk : 0 < k) (hkw : k ≤ w)
    (x y : BitVec w) :
    (x - y).setWidth k = x.setWidth k - y.setWidth k := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hkw,
    setWidth_neg hk hkw, ← BitVec.sub_eq_add_neg]

theorem low_mod_one_of_eq {w : Nat} (x : BitVec w) (k : Nat)
    (hk : 0 < k) (hkw : k ≤ w)
    (h : x = 1#w - (x <<< k)) :
    x.toNat % 2 ^ k = 1 := by
  have hl := congrArg (BitVec.setWidth k) h
  rw [setWidth_sub hk hkw, setWidth_one hk hkw,
    BitVec.setWidth_shiftLeft_of_le hkw,
    BitVec.shiftLeft_eq_zero (Nat.le_refl k)] at hl
  simp only [BitVec.sub_zero] at hl
  have hn := congrArg BitVec.toNat hl
  simpa only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt hk))] using hn

theorem twice_le_two_pow (k : Nat) (hk : 0 < k) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        decide
      · have hi := ih (Nat.pos_of_ne_zero hk0)
        rw [Nat.pow_succ]
        omega

theorem eq_one_of_le_twice_and_mod_one (x k : Nat) (hk : 0 < k)
    (hx : x ≤ 2 * k) (hmod : x % 2 ^ k = 1) : x = 1 := by
  have hb := twice_le_two_pow k hk
  by_cases hlt : x < 2 ^ k
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    exact hmod
  · have heq : x = 2 ^ k := by omega
    rw [heq, Nat.mod_self] at hmod
    omega

theorem low3_ne_zero_case {w : Nat} (hw : 3 ≤ w) :
    (0#w) ≠ 1#w - (0#w <<< 0) := by
  intro h
  have hl := congrArg low3 h
  rw [low3_sub hw, low3_one hw] at hl
  simp [low3] at hl

theorem low3_shiftLeft {w : Nat} (hw : 3 ≤ w) (x : BitVec w) (k : Nat) :
    low3 (x <<< k) = low3 x <<< k := by
  exact BitVec.setWidth_shiftLeft_of_le hw

theorem low3_ne_one_shift {w : Nat} (hw : 3 ≤ w) (k : Nat)
    (hk : k = 0 ∨ k = 1 ∨ k = 2) :
    (1#w) ≠ 1#w - (1#w <<< k) := by
  intro h
  have hl := congrArg low3 h
  rw [low3_one hw, low3_sub hw, low3_one hw,
    low3_shiftLeft hw, low3_one hw] at hl
  rcases hk with rfl | rfl | rfl
  · exact (by bv_decide : (1#3) ≠ 1#3 - (1#3 <<< 0)) hl
  · exact (by bv_decide : (1#3) ≠ 1#3 - (1#3 <<< 1)) hl
  · exact (by bv_decide : (1#3) ≠ 1#3 - (1#3 <<< 2)) hl

theorem low3_ne_allOnes_shift_zero {w : Nat} (hw : 3 ≤ w) :
    BitVec.allOnes w ≠ 1#w - (BitVec.allOnes w <<< 0) := by
  intro h
  have hl := congrArg low3 h
  rw [low3_sub hw, low3_one hw, low3_shiftLeft hw] at hl
  have hall : low3 (BitVec.allOnes w) = BitVec.allOnes 3 := by
    have hz : low3 (0#w) = 0#3 := by
      apply BitVec.eq_of_toNat_eq
      simp [low3, BitVec.toNat_setWidth]
    calc
      low3 (BitVec.allOnes w) = low3 (~~~(0#w)) := by simp
      _ = ~~~(low3 (0#w)) := low3_not hw _
      _ = BitVec.allOnes 3 := by rw [hz]; simp
  rw [hall] at hl
  have hne : BitVec.allOnes 3 ≠ 1#3 - (BitVec.allOnes 3 <<< 0) := by
    bv_decide
  exact hne hl

theorem low3_self_ne_one_sub_self {w : Nat} (hw : 3 ≤ w) (x : BitVec w) :
    x ≠ 1#w - x := by
  intro h
  have hl := congrArg low3 h
  rw [low3_sub hw, low3_one hw] at hl
  have hne : low3 x ≠ 1#3 - low3 x := by bv_decide
  exact hne hl

theorem quotient_nat {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    (x.smtUDiv s).toNat = x.toNat / s.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]

theorem udiv36 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ 1#w - (x <<< (x - x.smtUDiv s).toNat) := by
  let q := x.smtUDiv s
  let k := x - q
  change x ≠ 1#w - (x <<< k.toNat)
  intro h
  by_cases hs : s = 0#w
  · subst s
    have hq : q = BitVec.allOnes w := by
      simpa [q] using udiv3 x (0#w) rfl
    by_cases hxAll : x = BitVec.allOnes w
    · subst x
      have hk0 : k.toNat = 0 := by simp [k, hq]
      rw [hk0] at h
      exact low3_ne_allOnes_shift_zero hw h
    · have hxlt : x < BitVec.allOnes w := by
        simp only [BitVec.lt_def, BitVec.toNat_allOnes]
        have hxle := Nat.le_pred_of_lt x.isLt
        have hne : x.toNat ≠ 2 ^ w - 1 := by
          intro heq
          apply hxAll
          apply BitVec.eq_of_toNat_eq
          simpa using heq
        omega
      have hkNat : k.toNat = x.toNat + 1 := by
        change (x - q).toNat = x.toNat + 1
        rw [hq, BitVec.toNat_sub_of_lt hxlt, BitVec.toNat_allOnes]
        omega
      by_cases hkw : w ≤ k.toNat
      · rw [BitVec.shiftLeft_eq_zero hkw] at h
        have hx1 : x = 1#w := by simpa using h
        have hx1Nat : x.toNat = 1 := by
          rw [hx1]
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
        have hk2 : k.toNat = 2 := by
          omega
        omega
      · have hkLt : k.toNat < w := by omega
        have hkPos : 0 < k.toNat := by omega
        have hmod := low_mod_one_of_eq x k.toNat hkPos (by omega) h
        have hxLtPow : x.toNat < 2 ^ k.toNat := by
          rw [hkNat]
          exact Nat.lt_trans Nat.lt_two_pow_self
            (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
        rw [Nat.mod_eq_of_lt hxLtPow] at hmod
        have hx1Nat : x.toNat = 1 := hmod
        have hx1 : x = 1#w := by
          apply BitVec.eq_of_toNat_eq
          rw [hx1Nat]
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
        have hk2 : k.toNat = 2 := by omega
        rw [hx1, hk2] at h
        exact low3_ne_one_shift hw 2 (by simp) h
  have hqNat : q.toNat = x.toNat / s.toNat := by
    dsimp [q]
    exact quotient_nat x s hs
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  have hqLe : q.toNat ≤ x.toNat := by
    rw [hqNat]
    exact Nat.div_le_self _ _
  have hqBvLe : q ≤ x := by simpa [BitVec.le_def] using hqLe
  have hkNat : k.toNat = x.toNat - q.toNat := by
    dsimp [k]
    exact BitVec.toNat_sub_of_le hqBvLe
  by_cases hsOne : s.toNat = 1
  · have hqEq : q = x := by
      apply BitVec.eq_of_toNat_eq
      rw [hqNat, hsOne]
      simp
    have hk0 : k.toNat = 0 := by simp [k, hqEq]
    rw [hk0] at h
    simp only [BitVec.shiftLeft_zero] at h
    exact low3_self_ne_one_sub_self hw x h
  · have hsTwo : 2 ≤ s.toNat := by omega
    have hqHalf : 2 * q.toNat ≤ x.toNat := by
      rw [hqNat]
      have hd : x.toNat / s.toNat ≤ x.toNat / 2 :=
        Nat.div_le_div_left hsTwo (by decide)
      have hm := Nat.mul_div_le x.toNat 2
      omega
    have hxLeTwice : x.toNat ≤ 2 * k.toNat := by omega
    by_cases hk0 : k.toNat = 0
    · have hx0Nat : x.toNat = 0 := by omega
      have hx0 : x = 0#w := by
        apply BitVec.eq_of_toNat_eq
        simpa using hx0Nat
      rw [hx0, hk0] at h
      exact low3_ne_zero_case hw h
    have hkPos : 0 < k.toNat := Nat.pos_of_ne_zero hk0
    by_cases hkw : w ≤ k.toNat
    · rw [BitVec.shiftLeft_eq_zero hkw] at h
      have hx1 : x = 1#w := by simpa using h
      have hxNat : x.toNat = 1 := by
        rw [hx1]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      have hq0 : q.toNat = 0 := by omega
      have hk1 : k.toNat = 1 := by omega
      omega
    · have hkLe : k.toNat ≤ w := by omega
      have hmod := low_mod_one_of_eq x k.toNat hkPos hkLe h
      have hx1Nat := eq_one_of_le_twice_and_mod_one x.toNat k.toNat
        hkPos hxLeTwice hmod
      have hx1 : x = 1#w := by
        apply BitVec.eq_of_toNat_eq
        rw [hx1Nat]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      have hq0 : q.toNat = 0 := by omega
      have hk1 : k.toNat = 1 := by omega
      rw [hx1, hk1] at h
      exact low3_ne_one_shift hw 1 (by simp) h

end Udiv36Case
end BvAbstraction
