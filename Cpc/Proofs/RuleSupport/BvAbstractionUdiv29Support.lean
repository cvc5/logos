module

public import Cpc.Proofs.RuleSupport.BvAbstractionUrem13Support
import all Cpc.Proofs.RuleSupport.BvAbstractionUrem13Support

public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

namespace BvAbstraction
namespace Udiv29Case

theorem udiv29 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ x.smtUDiv s + (s ||| (x + s)) := by
  let q := x.smtUDiv s
  change x ≠ q + (s ||| (x + s))
  intro h
  let P := 2 ^ w
  have hPPos : 0 < P := by exact Nat.two_pow_pos _
  have hPLarge : 8 ≤ P := by
    change 2 ^ 3 ≤ 2 ^ w
    exact Nat.pow_le_pow_right (by decide) hw
  by_cases hs0 : s = 0#w
  · subst s
    have hq : q = BitVec.allOnes w := by
      simp [q, BitVec.smtUDiv]
    have hzero3 : low3 (0#w) = 0#3 := by
      apply BitVec.eq_of_toNat_eq
      simp [low3]
    have hl := congrArg low3 h
    rw [hq, low3_add hw, low3_or, low3_add hw, hzero3] at hl
    have hall3 : low3 (BitVec.allOnes w) = BitVec.allOnes 3 := by
      rw [← BitVec.not_zero, low3_not hw, hzero3, BitVec.not_zero]
    rw [hall3] at hl
    bv_decide
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs0)
  have hqNat : q.toNat = x.toNat / s.toNat := by
    dsimp [q]
    rw [BitVec.smtUDiv_eq, if_neg hs0, BitVec.toNat_udiv]
  by_cases hs1 : s.toNat = 1
  · have hsBv : s = 1#w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
      exact hs1
    have hqBv : q = x := by
      dsimp [q]
      simpa using udiv37 x s q hsBv rfl
    have hl := congrArg low3 h
    rw [hsBv, hqBv, low3_add hw, low3_or, low3_add hw,
      low3_one hw] at hl
    bv_decide
  have hsTwo : 2 ≤ s.toNat := by omega
  let y := x + s
  let a := s ||| y
  let d := s &&& ~~~y
  let A := a.toNat
  let D := d.toNat
  have hA : A < P := by simpa [A, P] using a.isLt
  have hD : D < P := by simpa [D, P] using d.isLt
  have hqLeX : q.toNat ≤ x.toNat := by
    simpa [BitVec.le_def] using udiv5 x s hs0
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add] at hn
  change x.toNat = (q.toNat + A) % P at hn
  have hrawLt : q.toNat + A < 2 * P := by
    have hqLt : q.toNat < P := by simpa [P] using q.isLt
    omega
  have hraw : q.toNat + A < P := by
    by_cases hlt : q.toNat + A < P
    · exact hlt
    · have heq : q.toNat + A = P + (q.toNat + A - P) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hn
      omega
  rw [Nat.mod_eq_of_lt hraw] at hn
  have hxEq : x.toNat = q.toNat + A := hn
  have hYNoWrapImpossible : ¬x.toNat + s.toNat < P := by
    intro hlt
    have hy : y.toNat = x.toNat + s.toNat := by
      dsimp [y]
      rw [Nat.mod_eq_of_lt (by simpa [P] using hlt)]
    have hyLeA : y.toNat ≤ A := by
      dsimp [A, a]
      exact nat_le_or_right _ _
    omega
  have hWrap : P ≤ x.toNat + s.toNat := by omega
  have hsumLt : x.toNat + s.toNat < 2 * P := by
    have hxlt : x.toNat < P := by simpa [P] using x.isLt
    have hslt : s.toNat < P := by simpa [P] using s.isLt
    omega
  have hy : y.toNat = x.toNat + s.toNat - P := by
    dsimp [y]
    have heq : x.toNat + s.toNat = P + (x.toNat + s.toNat - P) := by omega
    rw [heq, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega)]
    omega
  let c := s &&& y
  let C := c.toNat
  have horAnd := Udiv32Case.nat_or_add_and s.toNat y.toNat
  change A + C = s.toNat + y.toNat at horAnd
  have hpart := Udiv32Case.bitvec_partition_toNat y s
  change C + D = s.toNat at hpart
  have hAYD : A = y.toNat + D := by omega
  have hPRel : P = q.toNat + s.toNat + D := by omega
  have hDLeS : D ≤ s.toNat := by
    dsimp [D, d]
    exact Nat.and_le_left
  let r := x.toNat % s.toNat
  have hrlt : r < s.toNat := Nat.mod_lt _ hsPos
  have hdecomp := Nat.mod_add_div x.toNat s.toNat
  rw [← hqNat] at hdecomp
  change r + s.toNat * q.toNat = x.toNat at hdecomp
  have hxUpper : x.toNat < s.toNat * (q.toNat + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hqPos : 0 < q.toNat := by
    by_cases hq0 : q.toNat = 0
    · rw [hq0, Nat.mul_zero, Nat.add_zero] at hdecomp
      have hSLeA : s.toNat ≤ A := by
        dsimp [A, a]
        exact nat_le_or_left _ _
      omega
    · omega
  have hqSmall : q.toNat ≤ 3 := by
    have hprodLt : s.toNat * q.toNat < P := by omega
    have hPUpper : P ≤ q.toNat + 2 * s.toNat := by omega
    by_cases hq4 : 4 ≤ q.toNat
    · have hsEq : s.toNat = (s.toNat - 1) + 1 := by omega
      have hprodEq : q.toNat * s.toNat =
          q.toNat * (s.toNat - 1) + q.toNat := by
        calc
          q.toNat * s.toNat = q.toNat * ((s.toNat - 1) + 1) :=
            congrArg (fun n => q.toNat * n) hsEq
          _ = q.toNat * (s.toNat - 1) + q.toNat := by
            rw [Nat.mul_add, Nat.mul_one]
      have hmul := Nat.mul_le_mul_right (s.toNat - 1) hq4
      have hsq : s.toNat * q.toNat = q.toNat * s.toNat := Nat.mul_comm _ _
      rw [hsq, hprodEq] at hprodLt
      omega
    · omega
  have hqCases : q.toNat = 1 ∨ q.toNat = 2 ∨ q.toNat = 3 := by omega
  rcases hqCases with hq1 | hq2 | hq3
  · have hDComp : D = P - 1 - s.toNat := by omega
    have hnotNat : (~~~s).toNat = P - 1 - s.toNat := by
      simp [BitVec.toNat_not, P]
    have hdBv : d = ~~~s := by
      apply BitVec.eq_of_toNat_eq
      change D = (~~~s).toNat
      rw [hDComp, hnotNat]
    have hds : d &&& s = d := by
      dsimp [d]
      rw [BitVec.and_comm (s &&& ~~~y) s, ← BitVec.and_assoc,
        BitVec.and_self]
    rw [hdBv] at hds
    have hzero : (~~~s) &&& s = 0#w := by
      ext i hi
      simp
    have hnotZero : ~~~s = 0#w := hds.symm.trans hzero
    have hd0 : d = 0#w := by
      rw [hdBv, hnotZero]
    have hD0 : D = 0 := by simp [D, hd0]
    have hsAllNat : s.toNat = P - 1 := by omega
    have hsAll : s = BitVec.allOnes w := by
      apply BitVec.eq_of_toNat_eq
      simpa [P] using hsAllNat
    have hxNat : x.toNat = P - 1 := by
      rw [hq1] at hdecomp hxUpper
      omega
    have hxAll : x = BitVec.allOnes w := by
      apply BitVec.eq_of_toNat_eq
      simpa [P] using hxNat
    have hqOne : q = 1#w := by
      apply BitVec.eq_of_toNat_eq
      rw [hq1]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    have hl := congrArg low3 h
    rw [hxAll, hsAll, hqOne, low3_add hw, low3_or, low3_add hw,
      low3_one hw] at hl
    have hall3 : low3 (BitVec.allOnes w) = BitVec.allOnes 3 := by
      have hzero3 : low3 (0#w) = 0#3 := by
        apply BitVec.eq_of_toNat_eq
        simp [low3]
      rw [← BitVec.not_zero, low3_not hw, hzero3, BitVec.not_zero]
    rw [hall3] at hl
    bv_decide
  · let H := 2 ^ (w - 1)
    have hPH : P = 2 * H := by
      simpa [P, H, Nat.two_mul] using
        (Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w)).symm
    have hH : 4 ≤ H := by
      change 2 ^ 2 ≤ 2 ^ (w - 1)
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hprodLower : 2 * s.toNat ≤ x.toNat := by
      rw [hq2] at hdecomp
      omega
    have hsLtHalf : s.toNat < H := by omega
    have hsHalf : s.toNat = H - 1 := by
      rw [hq2] at hPRel
      omega
    have hDHalf : D = H - 1 := by
      rw [hq2, hPH, hsHalf] at hPRel
      omega
    have hDS : D = s.toNat := by omega
    have hC0 : C = 0 := by omega
    have hyLtS : y.toNat < s.toNat := by
      rw [hy]
      omega
    have hyMask : s.toNat &&& y.toNat = y.toNat := by
      rw [hsHalf]
      rw [Nat.and_comm]
      exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := w - 1)
        (by change y.toNat < H; omega)
    have hCY : C = y.toNat := by
      dsimp [C, c]
      exact hyMask
    have hy0 : y.toNat = 0 := by omega
    rw [hy0, hsHalf, hPH] at hy
    rw [hq2, hsHalf] at hdecomp
    omega
  · let H := 2 ^ (w - 1)
    have hPH : P = 2 * H := by
      simpa [P, H, Nat.two_mul] using
        (Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w)).symm
    have hH : 4 ≤ H := by
      change 2 ^ 2 ≤ 2 ^ (w - 1)
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hprodLower : 3 * s.toNat ≤ x.toNat := by
      rw [hq3] at hdecomp
      omega
    rw [hq3, hPH] at hPRel
    omega

end Udiv29Case
end BvAbstraction
