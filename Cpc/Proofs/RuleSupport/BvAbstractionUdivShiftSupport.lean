module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace UdivShiftCases

theorem le_allOnes {w : Nat} (x : BitVec w) : x ≤ BitVec.allOnes w := by
  simp only [BitVec.le_def, BitVec.toNat_allOnes]
  have hx := x.isLt
  omega


theorem succ_le_two_pow_of_pos (n : Nat) (hn : 0 < n) : n + 1 ≤ 2 ^ n := by
  exact Nat.lt_two_pow_self

theorem nat_udiv13 (x s : Nat) (hs : 0 < s) :
    x / 2 ^ (x / s) ≤ s := by
  let q := x / s
  have hxlt : x < s * (q + 1) := by
    dsimp [q]
    have h := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self (x / s))
    simpa [Nat.mul_comm] using h
  by_cases hq : q = 0
  · rw [hq] at hxlt
    simp only [Nat.zero_add, Nat.mul_one] at hxlt
    have hq' : x / s = 0 := by simpa [q] using hq
    simp only [hq', Nat.pow_zero, Nat.div_one]
    exact Nat.le_of_lt hxlt
  · have hpow : q + 1 ≤ 2 ^ q := succ_le_two_pow_of_pos q (Nat.pos_of_ne_zero hq)
    rw [Nat.div_le_iff_le_mul (Nat.two_pow_pos q)]
    have hmul := Nat.mul_le_mul_left s hpow
    have hxb : x < s * 2 ^ q := Nat.lt_of_lt_of_le hxlt hmul
    have hp := Nat.two_pow_pos q
    omega

theorem udiv13 {w : Nat} (x s : BitVec w) :
    (x >>> (x.smtUDiv s).toNat) ≤ s := by
  by_cases hs : s = 0#w
  · subst s
    cases w with
    | zero => simp [BitVec.eq_nil x]
    | succ w =>
      simp only [BitVec.smtUDiv, BitVec.toNat_allOnes]
      have hshift : x >>> (2 ^ (w + 1) - 1) = 0#(w + 1) := by
        apply BitVec.ushiftRight_eq_zero
        have hp : w + 1 < 2 ^ (w + 1) := Nat.lt_two_pow_self
        omega
      simp [hshift]
  · rw [BitVec.smtUDiv_eq, if_neg hs]
    simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, Nat.shiftRight_eq_div_pow]
    exact nat_udiv13 x.toNat s.toNat
      (Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs))

theorem nat_udiv35 (x s : Nat) (hs : 0 < s) :
    x / 2 ^ (x / s) ≤ s - 1 := by
  let q := x / s
  have hxlt : x < s * (q + 1) := by
    have h := (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self (x / s))
    simpa [q, Nat.mul_comm] using h
  by_cases hq : q = 0
  · rw [hq] at hxlt
    simp only [Nat.zero_add, Nat.mul_one] at hxlt
    have hq' : x / s = 0 := by simpa [q] using hq
    simp only [hq', Nat.pow_zero, Nat.div_one]
    omega
  · have hpow : q + 1 ≤ 2 ^ q :=
      succ_le_two_pow_of_pos q (Nat.pos_of_ne_zero hq)
    have hmul := Nat.mul_le_mul_left s hpow
    have hxb : x < s * 2 ^ q := Nat.lt_of_lt_of_le hxlt hmul
    have hdiv : x / 2 ^ q < s :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos q)).mpr
        (by simpa [Nat.mul_comm] using hxb)
    exact Nat.le_sub_one_of_lt hdiv

theorem udiv35 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (x >>> (x.smtUDiv s).toNat) ≤ s - 1#w := by
  by_cases hs : s = 0#w
  · subst s
    have hshift : x >>> (BitVec.allOnes w).toNat = 0#w := by
      apply BitVec.ushiftRight_eq_zero
      rw [BitVec.toNat_allOnes]
      have hp : w < 2 ^ w := Nat.lt_two_pow_self
      omega
    rw [BitVec.toNat_allOnes] at hshift
    have hsub : 0#w - 1#w = BitVec.allOnes w := by
      rw [BitVec.zero_sub, BitVec.neg_one_eq_allOnes]
    rw [hsub]
    change x >>> (BitVec.allOnes w).toNat ≤ BitVec.allOnes w
    rw [BitVec.toNat_allOnes]
    rw [hshift]
    simp [BitVec.le_def]
  · rw [BitVec.smtUDiv_eq, if_neg hs]
    simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, Nat.shiftRight_eq_div_pow]
    rw [toNat_sub_one_of_ne_zero s hs]
    exact nat_udiv35 x.toNat s.toNat
      (Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs))

theorem two_mul_le_two_pow_of_pos (n : Nat) (hn : 0 < n) :
    2 * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      decide
    · have ihn : 2 * n ≤ 2 ^ n := ih (Nat.pos_of_ne_zero hn0)
      have hp : 2 ≤ 2 ^ n := Nat.one_lt_two_pow hn0
      rw [Nat.pow_succ]
      omega

theorem nat_udiv34 (x s : Nat) (hs : 0 < s) :
    x / 2 ^ (s - 1) ≤ x / s := by
  by_cases hs1 : s = 1
  · simp [hs1]
  · have hs2 : 2 ≤ s := by omega
    have hp : s ≤ 2 ^ (s - 1) := by
      have h2 := two_mul_le_two_pow_of_pos (s - 1) (by omega)
      omega
    let y := x / 2 ^ (s - 1)
    apply (Nat.le_div_iff_mul_le hs).mpr
    have hy : y * 2 ^ (s - 1) ≤ x := by
      dsimp [y]
      exact Nat.div_mul_le_self _ _
    have hymul := Nat.mul_le_mul_left y hp
    exact Nat.le_trans hymul hy

theorem udiv34 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (x >>> (s - 1#w).toNat) ≤ x.smtUDiv s := by
  by_cases hs : s = 0#w
  · subst s
    change (x >>> ((0#w - 1#w).toNat)) ≤ BitVec.allOnes w
    exact le_allOnes _
  · rw [BitVec.smtUDiv_eq, if_neg hs]
    simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, Nat.shiftRight_eq_div_pow]
    rw [toNat_sub_one_of_ne_zero s hs]
    exact nat_udiv34 x.toNat s.toNat
      (Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs))

theorem nat_udiv16 (x s : Nat) (hs : 0 < s) :
    ((x / 2 ^ s) * 2) ≤ x / s := by
  let y := x / 2 ^ s
  apply (Nat.le_div_iff_mul_le hs).mpr
  have hy : y * 2 ^ s ≤ x := by
    dsimp [y]
    exact Nat.div_mul_le_self _ _
  have hpow := two_mul_le_two_pow_of_pos s hs
  have hymul := Nat.mul_le_mul_left y hpow
  calc
    y * 2 * s = y * (2 * s) := by simp [Nat.mul_assoc]
    _ ≤ y * 2 ^ s := hymul
    _ ≤ x := hy

theorem udiv16 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (x >>> s.toNat) <<< 1 ≤ x.smtUDiv s := by
  by_cases hs : s = 0#w
  · subst s
    exact le_allOnes _
  · rw [BitVec.smtUDiv_eq, if_neg hs]
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, BitVec.toNat_udiv,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have h := nat_udiv16 x.toNat s.toNat
      (Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs))
    exact Nat.le_trans (Nat.mod_le _ _) h

theorem nat_udiv22 (x s d : Nat) (hs : 0 < s) (hd : d ≤ 2 * x) :
    d / 2 ^ s ≤ x / s := by
  let y := d / 2 ^ s
  apply (Nat.le_div_iff_mul_le hs).mpr
  have hy : y * 2 ^ s ≤ d := by
    dsimp [y]
    exact Nat.div_mul_le_self _ _
  have hpow := two_mul_le_two_pow_of_pos s hs
  have hymul := Nat.mul_le_mul_left y hpow
  have htwo : 2 * (y * s) ≤ 2 * x := by
    calc
      2 * (y * s) = y * (2 * s) := by ac_rfl
      _ ≤ y * 2 ^ s := hymul
      _ ≤ d := hy
      _ ≤ 2 * x := hd
  change y * s ≤ x
  exact Nat.le_of_mul_le_mul_left htwo (by decide)

theorem udiv22 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    ((x <<< 1) >>> s.toNat) ≤ x.smtUDiv s := by
  by_cases hs : s = 0#w
  · subst s
    exact le_allOnes _
  · rw [BitVec.smtUDiv_eq, if_neg hs]
    simp only [BitVec.le_def, BitVec.toNat_ushiftRight,
      BitVec.toNat_udiv, Nat.shiftRight_eq_div_pow]
    apply nat_udiv22 x.toNat s.toNat (x <<< 1).toNat
      (Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs))
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.pow_one, Nat.mul_comm x.toNat 2]
    exact Nat.mod_le _ _

end UdivShiftCases
end BvAbstraction

