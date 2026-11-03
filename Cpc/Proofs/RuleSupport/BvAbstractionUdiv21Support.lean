module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace Udiv21Case

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

theorem allOnes_of_eq_not_self_and {w : Nat} (x a : BitVec w)
    (h : x = ~~~(x &&& a)) : x = BitVec.allOnes w := by
  ext i hi
  have hb := congrArg (fun z : BitVec w => z[i]) h
  change x[i] = (~~~(x &&& a))[i] at hb
  rw [BitVec.getElem_not hi, BitVec.getElem_and hi] at hb
  cases hxv : x[i] <;> cases hav : a[i] <;>
    simp [hxv, hav] at hb ⊢

theorem shiftLeft_one_eq_zero_cases {w : Nat} (hw : 0 < w) (x : BitVec w)
    (h : x <<< 1 = 0#w) : x.toNat = 0 ∨ 2 * x.toNat = 2 ^ w := by
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
    BitVec.toNat_ofNat, Nat.zero_mod] at hn
  have hdvd : 2 ^ w ∣ x.toNat * 2 := Nat.dvd_of_mod_eq_zero hn
  rcases hdvd with ⟨k, hk⟩
  have hxlt := x.isLt
  have hp := Nat.two_pow_pos w
  have hklt : k < 2 := by
    by_cases hlt : k < 2
    · exact hlt
    · have hkTwo : 2 ≤ k := by omega
      have hmul := Nat.mul_le_mul_left (2 ^ w) hkTwo
      exact False.elim (by omega)
  by_cases hk0 : k = 0
  · left
    rw [hk0] at hk
    simp at hk
    omega
  · right
    have hk1 : k = 1 := by omega
    rw [hk1] at hk
    simp at hk
    omega

theorem udiv21 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ ~~~(x &&& (x.smtUDiv s <<< 1)) := by
  intro heq
  let t := x.smtUDiv s
  change x = ~~~(x &&& (t <<< 1)) at heq
  have hx : x = BitVec.allOnes w := allOnes_of_eq_not_self_and x (t <<< 1) heq
  have hshift : t <<< 1 = 0#w := by
    rw [hx] at heq
    have hn := congrArg (fun z : BitVec w => ~~~z) heq
    simpa using hn.symm
  rcases shiftLeft_one_eq_zero_cases (by omega) t hshift with ht0 | htHalf
  · by_cases hs : s = 0#w
    · subst s
      have htAll : t = BitVec.allOnes w := by simpa [t] using udiv3 x (0#w) rfl
      rw [htAll, BitVec.toNat_allOnes] at ht0
      have hp := Nat.one_lt_two_pow (by omega : w ≠ 0)
      omega
    · have hsPos : 0 < s.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
      have htNat : t.toNat = x.toNat / s.toNat := by
        dsimp [t]
        rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
      have hsLeX : s.toNat ≤ x.toNat := by
        rw [hx, BitVec.toNat_allOnes]
        have hslt := s.isLt
        omega
      have htPos : 0 < t.toNat := by
        rw [htNat]
        exact Nat.div_pos hsLeX hsPos
      omega
  · by_cases hs : s = 0#w
    · subst s
      have htAll : t = BitVec.allOnes w := by simpa [t] using udiv3 x (0#w) rfl
      rw [htAll, BitVec.toNat_allOnes] at htHalf
      have hp := Nat.one_lt_two_pow (by omega : w ≠ 0)
      have hp8 : 8 ≤ 2 ^ w := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hw
        simpa using hpow
      exact False.elim (by omega)
    · have hprod := smtUDiv_mul_le x s hs
      change s.toNat * t.toNat ≤ x.toNat at hprod
      rw [hx, BitVec.toNat_allOnes] at hprod
      have hsPos : 0 < s.toNat :=
        Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
      have hp := Nat.one_lt_two_pow (by omega : w ≠ 0)
      have hsOne : s.toNat = 1 := by
        have hsLtTwo : s.toNat < 2 := by
          by_cases hlt : s.toNat < 2
          · exact hlt
          · have hsTwo : 2 ≤ s.toNat := by omega
            have hmul := Nat.mul_le_mul_right t.toNat hsTwo
            have hmul' : 2 * t.toNat ≤ s.toNat * t.toNat := by
              simpa [Nat.mul_comm] using hmul
            exact False.elim (by omega)
        omega
      have htNat : t.toNat = x.toNat / s.toNat := by
        dsimp [t]
        rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
      rw [hsOne] at htNat
      simp at htNat
      rw [hx, BitVec.toNat_allOnes] at htNat
      have hp8 : 8 ≤ 2 ^ w := by
        have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hw
        simpa using hpow
      omega

end Udiv21Case
end BvAbstraction

