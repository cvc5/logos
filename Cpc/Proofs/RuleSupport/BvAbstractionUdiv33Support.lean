module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace Udiv33Case

theorem nat_xor_le_add (a b : Nat) : a ^^^ b ≤ a + b := by
  have hmask : (a ^^^ b) &&& (a ||| b) = a ^^^ b := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  calc
    a ^^^ b = (a ^^^ b) &&& (a ||| b) := hmask.symm
    _ ≤ a ||| b := Nat.and_le_right
    _ ≤ a + b := nat_or_le_add a b

theorem nat_sub_le_xor (a b : Nat) : b - a ≤ a ^^^ b := by
  have hpart : (b &&& a) ||| (b &&& (a ^^^ b)) = b := by
    apply Nat.eq_of_testBit_eq
    intro i
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  have hor := nat_or_le_add (b &&& a) (b &&& (a ^^^ b))
  have hba : b &&& a ≤ a := Nat.and_le_right
  have hbx : b &&& (a ^^^ b) ≤ a ^^^ b := Nat.and_le_right
  rw [hpart] at hor
  omega

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

theorem smtUDiv_upper {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    x.toNat < s.toNat * ((x.smtUDiv s).toNat + 1) := by
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  have h := (Nat.div_lt_iff_lt_mul hsPos).mp
    (Nat.lt_succ_self (x.toNat / s.toNat))
  simpa [Nat.mul_comm] using h

theorem udiv33 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    (s ^^^ (x ||| x.smtUDiv s)) ≥ (x.smtUDiv s ^^^ 1#w) := by
  let t := x.smtUDiv s
  change (s ^^^ (x ||| t)) ≥ (t ^^^ 1#w)
  by_cases hs : s = 0#w
  · subst s
    have ht : t = BitVec.allOnes w := by simpa [t] using udiv3 x (0#w) rfl
    rw [ht]
    simp [BitVec.le_def, BitVec.toNat_allOnes]
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  have htNat : t.toNat = x.toNat / s.toNat := by
    dsimp [t]
    rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  by_cases hsOne : s.toNat = 1
  · have htEqX : t = x := by
      apply BitVec.eq_of_toNat_eq
      rw [htNat, hsOne]
      simp
    have hsEqOne : s = 1#w := by
      apply BitVec.eq_of_toNat_eq
      rw [hsOne]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [htEqX, hsEqOne, BitVec.or_self, BitVec.xor_comm]
    simp
  have hsTwo : 2 ≤ s.toNat := by omega
  by_cases ht0 : t.toNat = 0
  · simp only [BitVec.le_def, BitVec.toNat_xor, BitVec.toNat_or]
    have hxlt : x.toNat < s.toNat := by
      rw [htNat] at ht0
      have hz := (Nat.div_eq_zero_iff).mp ht0
      exact hz.resolve_left (by omega)
    have hne : s.toNat ^^^ x.toNat ≠ 0 := by
      intro hzero
      have heq : s.toNat = x.toNat := by
        apply Nat.eq_of_testBit_eq
        intro i
        have hb := congrArg (fun n : Nat => n.testBit i) hzero
        have hquot : x.toNat / s.toNat = 0 := htNat.symm.trans ht0
        cases hsbit : s.toNat.testBit i <;>
          cases hxbit : x.toNat.testBit i
        all_goals
          simp only [Nat.testBit_xor, hsbit, hxbit, hquot, Nat.zero_testBit] at hb
        all_goals simp at hb
        all_goals rfl
      omega
    have hpos : 1 ≤ s.toNat ^^^ x.toNat := Nat.one_le_iff_ne_zero.mpr hne
    rw [ht0]
    simp only [Nat.zero_xor, Nat.or_zero]
    have hone : (1#w).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [hone]
    simpa [Nat.xor_comm] using hpos
  have htPos : 0 < t.toNat := Nat.pos_of_ne_zero ht0
  by_cases htOne : t.toNat = 1
  · simp only [BitVec.le_def]
    have hzero : (s ^^^ 1#w).toNat ≥ 0 := Nat.zero_le _
    have htEq : t = 1#w := by
      apply BitVec.eq_of_toNat_eq
      rw [htOne]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [htEq]
    simp [BitVec.le_def]
  have htTwo : 2 ≤ t.toNat := by omega
  have hprod := smtUDiv_mul_le x s hs
  change s.toNat * t.toNat ≤ x.toNat at hprod
  have hupper := smtUDiv_upper x s hs
  change x.toNat < s.toNat * (t.toNat + 1) at hupper
  by_cases h22 : s.toNat = 2 ∧ t.toNat = 2
  · rcases h22 with ⟨hs2, ht2⟩
    have hxCases : x.toNat = 4 ∨ x.toNat = 5 := by
      rw [hs2, ht2] at hprod hupper
      omega
    simp only [BitVec.le_def, BitVec.toNat_xor, BitVec.toNat_or]
    have hone : (1#w).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [hs2, ht2, hone]
    rcases hxCases with hx4 | hx5
    · rw [hx4]
      decide
    · rw [hx5]
      decide
  · have hmulGap : s.toNat * (t.toNat - 1) ≥ t.toNat + 1 := by
      by_cases hs3 : 3 ≤ s.toNat
      · have hm := Nat.mul_le_mul_right (t.toNat - 1) hs3
        have htPred : 1 ≤ t.toNat - 1 := by omega
        have htExpand : 3 * (t.toNat - 1) ≥ t.toNat + 1 := by omega
        omega
      · have hs2 : s.toNat = 2 := by omega
        have ht3 : 3 ≤ t.toNat := by omega
        rw [hs2]
        omega
    have hxSub : t.toNat + 1 ≤ x.toNat - s.toNat := by
      have hrewrite : s.toNat * (t.toNat - 1) =
          s.toNat * t.toNat - s.toNat := by
        rw [Nat.mul_sub_left_distrib]
        simp
      rw [hrewrite] at hmulGap
      omega
    simp only [BitVec.le_def, BitVec.toNat_xor, BitVec.toNat_or]
    have hlower := nat_sub_le_xor s.toNat (x.toNat ||| t.toNat)
    have hxOr : x.toNat ≤ x.toNat ||| t.toNat := nat_le_or_left _ _
    have hrhs := nat_xor_le_add t.toNat (1#w).toNat
    have hone : (1#w).toNat = 1 := by
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    rw [hone] at hrhs ⊢
    omega

end Udiv33Case
end BvAbstraction
