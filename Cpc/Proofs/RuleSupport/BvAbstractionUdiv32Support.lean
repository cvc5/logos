module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

namespace BvAbstraction
namespace Udiv32Case

theorem two_mul_and_two_mul_add_one (a b : Nat) :
    (2 * a) &&& (2 * b + 1) = 2 * (a &&& b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.and_div_two]
      have ha : (2 * a) / 2 = a := by omega
      have hb : (2 * b + 1) / 2 = b := by omega
      have hab : (2 * (a &&& b)) / 2 = a &&& b := by omega
      rw [ha, hb, hab]

theorem nat_or_add_and (a b : Nat) :
    (a ||| b) + (a &&& b) = a + b := by
  by_cases ha0 : a = 0
  · simp [ha0]
  by_cases hb0 : b = 0
  · simp [hb0]
  let a' := a / 2
  let b' := b / 2
  have haeq : a = 2 * a' + a % 2 := by dsimp [a']; omega
  have hbeq : b = 2 * b' + b % 2 := by dsimp [b']; omega
  have hsum : a' + b' < a + b := by
    have ha' : a' < a := by dsimp [a']; omega
    have hb' : b' < b := by dsimp [b']; omega
    omega
  have ih := nat_or_add_and a' b'
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · rw [ha] at haeq
    rw [hb] at hbeq
    simp only [Nat.add_zero] at haeq hbeq
    rw [haeq, hbeq, two_mul_or, two_mul_and]
    omega
  · rw [ha] at haeq
    rw [hb] at hbeq
    simp only [Nat.add_zero] at haeq
    rw [haeq, hbeq, two_mul_or_two_mul_add_one,
      two_mul_and_two_mul_add_one]
    omega
  · rw [ha] at haeq
    rw [hb] at hbeq
    simp only [Nat.add_zero] at hbeq
    have ih' : (b' ||| a') + (b' &&& a') = b' + a' := by
      simpa [Nat.or_comm, Nat.and_comm, Nat.add_comm] using ih
    rw [haeq, hbeq, Nat.or_comm, Nat.and_comm,
      two_mul_or_two_mul_add_one, two_mul_and_two_mul_add_one]
    omega
  · rw [ha] at haeq
    rw [hb] at hbeq
    rw [haeq, hbeq, two_mul_add_one_or, two_mul_add_one_and]
    omega
termination_by a + b

theorem bitvec_partition_toNat {w : Nat} (x s : BitVec w) :
    (s &&& x).toNat + (s &&& ~~~x).toNat = s.toNat := by
  let c := s &&& x
  let d := s &&& ~~~x
  have hor : c ||| d = s := by
    ext i hi
    cases hsbit : s[i] <;> cases hxbit : x[i] <;>
      simp_all [c, d]
  have hand : c &&& d = 0#w := by
    ext i hi
    cases hsbit : s[i] <;> cases hxbit : x[i] <;>
      simp_all [c, d]
  have hi := nat_or_add_and c.toNat d.toNat
  simp only [← BitVec.toNat_or, hor, ← BitVec.toNat_and, hand,
    BitVec.toNat_ofNat, Nat.zero_mod] at hi
  exact hi.symm

theorem high_bit_true {w n : Nat} (hw : 0 < w)
    (hnLo : 2 ^ (w - 1) ≤ n) (hnHi : n < 2 ^ w) :
    n.testBit (w - 1) = true := by
  have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
    simpa [Nat.two_mul] using (Nat.two_pow_pred_add_two_pow_pred hw).symm
  have hdiv : n / 2 ^ (w - 1) = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hnLo
    · rw [show (1 + 1) * 2 ^ (w - 1) = 2 * 2 ^ (w - 1) by omega,
        ← hp]
      exact hnHi
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
  decide

theorem disjoint_le_implies_lt_half {w : Nat} (hw : 0 < w)
    (a b : BitVec w) (hab : a &&& b = 0#w) (hle : a ≤ b) :
    a.toNat < 2 ^ (w - 1) := by
  by_cases hgoal : a.toNat < 2 ^ (w - 1)
  · exact hgoal
  have haLo : 2 ^ (w - 1) ≤ a.toNat := by omega
  have hbLo : 2 ^ (w - 1) ≤ b.toNat := by
    simpa [BitVec.le_def] using Nat.le_trans haLo (by simpa [BitVec.le_def] using hle)
  have haBit := high_bit_true (w := w) hw haLo a.isLt
  have hbBit := high_bit_true (w := w) hw hbLo b.isLt
  have heq := congrArg (fun n : Nat => n.testBit (w - 1))
    (congrArg BitVec.toNat hab)
  simp only [BitVec.toNat_and, Nat.testBit_and, haBit, hbBit,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_testBit] at heq
  simp at heq

theorem quotient_bounds {w : Nat} (x s : BitVec w) (hs : s ≠ 0#w) :
    s.toNat * (x.smtUDiv s).toNat ≤ x.toNat ∧
      x.toNat < s.toNat * ((x.smtUDiv s).toNat + 1) := by
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  constructor
  · exact Nat.mul_div_le _ _
  · have h := (Nat.div_lt_iff_lt_mul hsPos).mp
      (Nat.lt_succ_self (x.toNat / s.toNat))
    simpa [Nat.mul_comm] using h

theorem low3_two {w : Nat} (hw : 3 ≤ w) : low3 (2#w) = 2#3 := by
  apply BitVec.eq_of_toNat_eq
  have hpw : 2 < 2 ^ w := by
    have hh : 2 ^ 3 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    omega
  simp only [low3, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hpw, Nat.mod_eq_of_lt (by decide)]

theorem nat_and_two_ne_zero_near_max {w : Nat} (hw : 3 ≤ w)
    (x : BitVec w) (hx : x.toNat = 2 ^ w - 2 ∨ x.toNat = 2 ^ w - 1) :
    x.toNat &&& 2 ≠ 0 := by
  intro hc
  have hxCase : x = -2#w ∨ x = -1#w := by
    rcases hx with hx2 | hx1
    · left
      apply BitVec.eq_of_toNat_eq
      rw [hx2]
      have hp : 2 < 2 ^ w := by
        have hh : 2 ^ 3 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
        omega
      simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by omega)]
    · right
      apply BitVec.eq_of_toNat_eq
      rw [hx1]
      have hp : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
      simp only [BitVec.toNat_neg, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt (by omega)]
  have hcBv : x &&& 2#w = 0#w := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by
      have hh : 2 ^ 3 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
      omega)]
    simp [hc]
  have hl := congrArg low3 hcBv
  rw [low3_and, low3_two hw] at hl
  have hz : low3 (0#w) = 0#3 := by
    apply BitVec.eq_of_toNat_eq
    simp [low3]
  rw [hz] at hl
  rcases hxCase with hx2 | hx1
  · rw [hx2, low3_neg hw, low3_two hw] at hl
    have hne : (-2#3) &&& 2#3 ≠ 0#3 := by bv_decide
    exact hne hl
  · rw [hx1, low3_neg hw, low3_one hw] at hl
    have hne : (-1#3) &&& 2#3 ≠ 0#3 := by bv_decide
    exact hne hl

theorem udiv32 {w : Nat} (hw : 3 ≤ w) (x s : BitVec w) :
    x ≠ x.smtUDiv s + x.smtUDiv s + (x ||| s) := by
  let q := x.smtUDiv s
  change x ≠ q + q + (x ||| s)
  intro h
  let P := 2 ^ w
  have hP : P = 2 ^ w := rfl
  have hPPos : 0 < P := Nat.two_pow_pos _
  have hPLarge : 4 < P := by
    have h8 : 2 ^ 3 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    change 4 < 2 ^ w
    exact Nat.lt_of_lt_of_le (by decide) h8
  by_cases hs : s = 0#w
  · subst s
    have hq : q = BitVec.allOnes w := by
      simp [q]
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_add, hq, BitVec.toNat_allOnes,
      BitVec.toNat_or, BitVec.toNat_ofNat, Nat.zero_mod, Nat.or_zero] at hn
    change x.toNat = ((P - 1 + (P - 1)) % P + x.toNat) % P at hn
    have hinner : (P - 1 + (P - 1)) % P = P - 2 := by
      have heq : P - 1 + (P - 1) = P + (P - 2) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hinner] at hn
    have hraw : P - 2 + x.toNat < 2 * P := by omega
    by_cases hlt : P - 2 + x.toNat < P
    · rw [Nat.mod_eq_of_lt hlt] at hn
      omega
    · have heq : P - 2 + x.toNat = P + (x.toNat - 2) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hn
      omega
  have hb := quotient_bounds x s hs
  change s.toNat * q.toNat ≤ x.toNat ∧
    x.toNat < s.toNat * (q.toNat + 1) at hb
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  have hqLe : q.toNat ≤ x.toNat := by
    have hqNat : q.toNat = x.toNat / s.toNat := by
      dsimp [q]
      rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
    rw [hqNat]
    exact Nat.div_le_self _ _
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_or] at hn
  let A := x.toNat ||| s.toNat
  have hinnerLt : (q.toNat + q.toNat) % P < P := Nat.mod_lt _ hPPos
  have hrawLt : (q.toNat + q.toNat) % P + A < 2 * P := by
    have hAlt : A < P := by simpa [A, ← BitVec.toNat_or] using (x ||| s).isLt
    omega
  have hsumMod : (q.toNat + q.toNat) % P =
      if q.toNat + q.toNat < P then q.toNat + q.toNat
      else q.toNat + q.toNat - P := by
    split
    · rename_i hlt
      rw [Nat.mod_eq_of_lt hlt]
    · rename_i hnot
      have hlt2 : q.toNat + q.toNat < 2 * P := by omega
      have heq : q.toNat + q.toNat = P + (q.toNat + q.toNat - P) := by omega
      calc
        (q.toNat + q.toNat) % P =
            (P + (q.toNat + q.toNat - P)) % P := congrArg (fun n => n % P) heq
        _ = (q.toNat + q.toNat - P) % P := Nat.add_mod_left _ _
        _ = q.toNat + q.toNat - P := Nat.mod_eq_of_lt (by omega)
  rw [hsumMod] at hn hrawLt
  split at hn
  · rename_i h2q
    simp only [if_pos h2q] at hrawLt
    by_cases hraw : q.toNat + q.toNat + A < P
    · rw [Nat.mod_eq_of_lt hraw] at hn
      have hxLeA : x.toNat ≤ A := nat_le_or_left _ _
      have hsLeA : s.toNat ≤ A := nat_le_or_right _ _
      by_cases hq0 : q.toNat = 0
      · have hxltS : x.toNat < s.toNat := by
          have := hb.2
          rw [hq0] at this
          simpa using this
        omega
      · omega
    · have hrawEq : q.toNat + q.toNat + A = P + x.toNat := by
        have hlt2 : q.toNat + q.toNat + A < 2 * P := hrawLt
        have hdecomp : q.toNat + q.toNat + A =
            P + (q.toNat + q.toNat + A - P) := by omega
        rw [hdecomp, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hn
        omega
      have horAnd := nat_or_add_and x.toNat s.toNat
      change A + (x.toNat &&& s.toNat) = x.toNat + s.toNat at horAnd
      let c := s &&& x
      let d := s &&& ~~~x
      have hpart := bitvec_partition_toNat x s
      change c.toNat + d.toNat = s.toNat at hpart
      have hc : c.toNat = x.toNat &&& s.toNat := by
        simp [c, Nat.and_comm]
      have hdEq : d.toNat = P - (q.toNat + q.toNat) := by
        rw [hc] at hpart
        omega
      have hdLeS : d.toNat ≤ s.toNat := by omega
      have hqPos : 0 < q.toNat := by
        by_cases hq0 : q.toNat = 0
        · rw [hq0] at hdEq
          have hdLt := d.isLt
          omega
        · omega
      have hsLeX : s.toNat ≤ x.toNat := by
        by_cases hgoal : s.toNat ≤ x.toNat
        · exact hgoal
        have hxlt : x.toNat < s.toNat := by omega
        have hqZero : q.toNat = 0 := by
          have hqNat : q.toNat = x.toNat / s.toNat := by
            dsimp [q]
            rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
          rw [hqNat, Nat.div_eq_of_lt hxlt]
        omega
      have hdLeX : d ≤ x := by
        simp only [BitVec.le_def]
        omega
      have hdisj : d &&& x = 0#w := by
        ext i hi
        simp [d]
      have hdHalf := disjoint_le_implies_lt_half (by omega) d x hdisj hdLeX
      have hhalfEq : P = 2 * 2 ^ (w - 1) := by
        simpa [P, Nat.two_mul] using
          (Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w)).symm
      have hqQuarter : 2 ^ (w - 2) < q.toNat := by
        have hquarterEq : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by
          simpa [Nat.two_mul, show w - 1 - 1 = w - 2 by omega] using
            (Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w - 1)).symm
        omega
      have hquarterEq : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by
        simpa [Nat.two_mul, show w - 1 - 1 = w - 2 by omega] using
          (Nat.two_pow_pred_add_two_pow_pred (by omega : 0 < w - 1)).symm
      have hsLtFour : s.toNat < 4 := by
        have hmul := hb.1
        have hpFactor : P = 4 * 2 ^ (w - 2) := by
          rw [hhalfEq, hquarterEq]
          omega
        by_cases hgoal : s.toNat < 4
        · exact hgoal
        have hsFour : 4 ≤ s.toNat := by omega
        have hm : 4 * 2 ^ (w - 2) ≤ s.toNat * q.toNat :=
          Nat.mul_le_mul hsFour (Nat.le_of_lt hqQuarter)
        omega
      have hkey : q.toNat + q.toNat + s.toNat =
          P + (x.toNat &&& s.toNat) := by omega
      have hsCases : s.toNat = 1 ∨ s.toNat = 2 ∨ s.toNat = 3 := by omega
      rcases hsCases with hs1 | hs2 | hs3
      · have hqEqX : q.toNat = x.toNat := by
          have hqNat : q.toNat = x.toNat / s.toNat := by
            dsimp [q]
            rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
          rw [hqNat, hs1]
          simp
        have hcLeOne : x.toNat &&& s.toNat ≤ 1 := by
          rw [hs1]
          exact Nat.and_le_right
        omega
      · have hqNat : q.toNat = x.toNat / 2 := by
          dsimp [q]
          rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv, hs2]
        have hxParity : x.toNat = 2 * q.toNat ∨ x.toNat = 2 * q.toNat + 1 := by
          rw [hqNat]
          have hm := Nat.mod_two_eq_zero_or_one x.toNat
          omega
        have hcCases : x.toNat &&& s.toNat = 0 ∨ x.toNat &&& s.toNat = 2 := by
          rw [hs2]
          have hle : x.toNat &&& 2 ≤ 2 := Nat.and_le_right
          have hne : x.toNat &&& 2 ≠ 1 := by
            intro heq
            have hb := congrArg (fun n : Nat => n.testBit 0) heq
            simp at hb
          omega
        rw [hs2] at hkey
        rcases hxParity with hxEven | hxOdd
        · rcases hcCases with hc0 | hc2
          · rw [hs2] at hc0
            rw [hc0] at hkey
            have hxVal : x.toNat = 2 ^ w - 2 := by
              change P = 2 ^ w at hP
              omega
            exact nat_and_two_ne_zero_near_max hw x (Or.inl hxVal) hc0
          · rw [hs2] at hc2
            rw [hc2] at hkey
            omega
        · rcases hcCases with hc0 | hc2
          · rw [hs2] at hc0
            rw [hc0] at hkey
            have hxVal : x.toNat = 2 ^ w - 1 := by
              change P = 2 ^ w at hP
              omega
            exact nat_and_two_ne_zero_near_max hw x (Or.inr hxVal) hc0
          · rw [hs2] at hc2
            rw [hc2] at hkey
            omega
      · have hcLe : x.toNat &&& s.toNat ≤ 3 := by
          rw [hs3]
          exact Nat.and_le_right
        have hmul := hb.1
        rw [hs3] at hmul
        omega
  · rename_i h2q
    simp only [if_neg h2q] at hrawLt
    have hqLarge : P ≤ q.toNat + q.toNat := by omega
    have hqLeX' := hqLe
    have hsOne : s.toNat = 1 := by
      by_cases hgoal : s.toNat = 1
      · exact hgoal
      have hsTwo : 2 ≤ s.toNat := by omega
      have hmul := hb.1
      have hm := Nat.mul_le_mul_right q.toNat hsTwo
      omega
    have hqEqX : q.toNat = x.toNat := by
      have hqNat : q.toNat = x.toNat / s.toNat := by
        dsimp [q]
        rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
      rw [hqNat, hsOne]
      simp
    have hlow := congrArg low3 h
    rw [low3_add hw, low3_add hw, low3_or] at hlow
    have hsBv : s = 1#w := by
      apply BitVec.eq_of_toNat_eq
      rw [hsOne]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
    have hqBv : q = x := BitVec.eq_of_toNat_eq hqEqX
    rw [hsBv, hqBv, low3_one hw] at hlow
    bv_decide

end Udiv32Case
end BvAbstraction
