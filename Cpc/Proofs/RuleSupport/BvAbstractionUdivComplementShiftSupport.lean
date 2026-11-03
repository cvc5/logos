module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvAbstraction
namespace UdivComplementShiftCases


theorem zero_le_bv {w : Nat} (x : BitVec w) : 0#w ≤ x := by
  simp [BitVec.le_def]

theorem succ_le_two_pow (k : Nat) : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self

theorem smtUDiv_mul_le {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat := by
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  exact Nat.mul_div_le _ _

theorem pow_factor (k w : Nat) (hkw : k ≤ w) :
    2 ^ w = 2 ^ (w - k) * 2 ^ k := by
  rw [← Nat.pow_add]
  congr
  omega

theorem nat_shift_complement_bound (w a b k : Nat)
    (hb : b < 2 ^ w) (hk : k = 2 ^ w - 1 - b) (hkw : k ≤ w) :
    (a * 2 ^ k) % 2 ^ w ≤ b := by
  let m := 2 ^ (w - k)
  let p := 2 ^ k
  have hP : 2 ^ w = m * p := by simpa [m, p] using pow_factor k w hkw
  have hy : (a * p) % (m * p) = (a % m) * p :=
    Nat.mul_mod_mul_right p a m
  have ham : a % m < m := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hmp : m * p = 2 ^ w := hP.symm
  have hmax : (a % m) * p ≤ m * p - p := by
    have hmul := Nat.mul_le_mul_right p (Nat.le_sub_one_of_lt ham)
    calc
      (a % m) * p ≤ (m - 1) * p := hmul
      _ = m * p - p := by rw [Nat.sub_mul]; simp
  have hpk : k + 1 ≤ p := by simpa [p] using succ_le_two_pow k
  rw [hP, hy]
  have hkb : b + k + 1 = 2 ^ w := by omega
  have htail : m * p - p ≤ b := by
    rw [← hP]
    omega
  exact Nat.le_trans hmax htail

theorem nat_shift_complement_le (w x a c b k : Nat)
    (hb : b < 2 ^ w) (hk : k = 2 ^ w - 1 - b) (hkw : k ≤ w)
    (hprod : a * c ≤ x)
    (hhigh : c < 2 ^ k → b / 2 ^ k = x / 2 ^ k) :
    (a * 2 ^ k) % 2 ^ w ≤ x := by
  let y := (a * 2 ^ k) % 2 ^ w
  have hyb : y ≤ b := nat_shift_complement_bound w a b k hb hk hkw
  by_cases hpc : 2 ^ k ≤ c
  · have hmul := Nat.mul_le_mul_left a hpc
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.le_trans hmul hprod)
  · have hcp : c < 2 ^ k := by omega
    have hP := pow_factor k w hkw
    have hyEq : y = (a % 2 ^ (w - k)) * 2 ^ k := by
      dsimp [y]
      rw [hP]
      exact Nat.mul_mod_mul_right (2 ^ k) a (2 ^ (w - k))
    have hyDiv : y / 2 ^ k = a % 2 ^ (w - k) := by
      rw [hyEq]
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos k)
    have hdiv := Nat.div_le_div_right hyb (c := 2 ^ k)
    rw [hhigh hcp] at hdiv
    rw [hyDiv] at hdiv
    have hmul := Nat.mul_le_mul_right (2 ^ k) hdiv
    rw [← hyEq] at hmul
    exact Nat.le_trans hmul (Nat.div_mul_le_self x (2 ^ k))

theorem allOnes_shift_complement_le {w : Nat} (x : BitVec w) :
    BitVec.allOnes w <<< (~~~x) ≤ x := by
  let k := (~~~x).toNat
  by_cases hkw : k ≤ w
  · change BitVec.allOnes w <<< k ≤ x
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft,
      BitVec.toNat_allOnes, Nat.shiftLeft_eq]
    apply nat_shift_complement_bound w (2 ^ w - 1) x.toNat k x.isLt
    · dsimp [k]
      rw [BitVec.toNat_not]
    · exact hkw
  · change BitVec.allOnes w <<< k ≤ x
    rw [BitVec.shiftLeft_eq_zero (by omega)]
    exact zero_le_bv _

theorem udiv23 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s <<< (~~~(x ||| x.smtUDiv s)) ≤ x := by
  let t := x.smtUDiv s
  let b := x ||| t
  let k := (~~~b).toNat
  by_cases hs : s = 0#w
  · subst s
    simp
    exact zero_le_bv _
  by_cases hkw : k ≤ w
  · change s <<< k ≤ x
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    apply nat_shift_complement_le w x.toNat s.toNat t.toNat b.toNat k
    · exact b.isLt
    · dsimp [k, b]
      rw [BitVec.toNat_not, BitVec.toNat_or]
    · exact hkw
    · have hp := smtUDiv_mul_le x s hs
      simpa [Nat.mul_comm] using hp
    · intro htp
      dsimp [b]
      simp only [BitVec.toNat_or, Nat.or_div_two_pow]
      rw [Nat.div_eq_of_lt htp]
      simp
  · have hzero : s <<< k = 0#w := BitVec.shiftLeft_eq_zero (by omega)
    change s <<< k ≤ x
    rw [hzero]
    exact zero_le_bv _

theorem udiv24 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x.smtUDiv s <<< (~~~(x ||| s)) ≤ x := by
  let t := x.smtUDiv s
  by_cases hs0 : s = 0#w
  · subst s
    change t <<< (~~~(x ||| 0#w)) ≤ x
    rw [BitVec.or_zero]
    have htAll : t = BitVec.allOnes w := by
      simpa [t] using udiv3 x (0#w) rfl
    rw [htAll]
    exact allOnes_shift_complement_le x
  by_cases ht : t = 0#w
  · change t <<< (~~~(x ||| s)) ≤ x
    rw [ht]
    simp
    exact zero_le_bv _
  have hs : s ≠ 0#w := hs0
  let b := x ||| s
  let k := (~~~b).toNat
  by_cases hkw : k ≤ w
  · change t <<< k ≤ x
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    apply nat_shift_complement_le w x.toNat t.toNat s.toNat b.toNat k
    · exact b.isLt
    · dsimp [k, b]
      rw [BitVec.toNat_not, BitVec.toNat_or]
    · exact hkw
    · simpa [t, Nat.mul_comm] using smtUDiv_mul_le x s hs
    · intro hsp
      dsimp [b]
      simp only [BitVec.toNat_or, Nat.or_div_two_pow]
      rw [Nat.div_eq_of_lt hsp]
      simp
  · change t <<< k ≤ x
    rw [BitVec.shiftLeft_eq_zero (by omega)]
    exact zero_le_bv _

theorem udiv27 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    s <<< (~~~(x ^^^ x.smtUDiv s)) ≤ x := by
  let t := x.smtUDiv s
  let b := x ^^^ t
  let k := (~~~b).toNat
  by_cases hs : s = 0#w
  · subst s
    simp
    exact zero_le_bv _
  by_cases hkw : k ≤ w
  · change s <<< k ≤ x
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    apply nat_shift_complement_le w x.toNat s.toNat t.toNat b.toNat k
    · exact b.isLt
    · dsimp [k, b]
      rw [BitVec.toNat_not, BitVec.toNat_xor]
    · exact hkw
    · have hp := smtUDiv_mul_le x s hs
      simpa [Nat.mul_comm] using hp
    · intro htp
      dsimp [b]
      simp only [BitVec.toNat_xor, Nat.xor_div_two_pow]
      rw [Nat.div_eq_of_lt htp]
      simp
  · change s <<< k ≤ x
    rw [BitVec.shiftLeft_eq_zero (by omega)]
    exact zero_le_bv _

theorem udiv28 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x.smtUDiv s <<< (~~~(x ^^^ s)) ≤ x := by
  let t := x.smtUDiv s
  by_cases hs0 : s = 0#w
  · subst s
    change t <<< (~~~(x ^^^ 0#w)) ≤ x
    rw [BitVec.xor_zero]
    have htAll : t = BitVec.allOnes w := by
      simpa [t] using udiv3 x (0#w) rfl
    rw [htAll]
    exact allOnes_shift_complement_le x
  by_cases ht : t = 0#w
  · change t <<< (~~~(x ^^^ s)) ≤ x
    rw [ht]
    simp
    exact zero_le_bv _
  have hs : s ≠ 0#w := hs0
  let b := x ^^^ s
  let k := (~~~b).toNat
  by_cases hkw : k ≤ w
  · change t <<< k ≤ x
    simp only [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    apply nat_shift_complement_le w x.toNat t.toNat s.toNat b.toNat k
    · exact b.isLt
    · dsimp [k, b]
      rw [BitVec.toNat_not, BitVec.toNat_xor]
    · exact hkw
    · simpa [t, Nat.mul_comm] using smtUDiv_mul_le x s hs
    · intro hsp
      dsimp [b]
      simp only [BitVec.toNat_xor, Nat.xor_div_two_pow]
      rw [Nat.div_eq_of_lt hsp]
      simp
  · change t <<< k ≤ x
    rw [BitVec.shiftLeft_eq_zero (by omega)]
    exact zero_le_bv _

end UdivComplementShiftCases
end BvAbstraction

