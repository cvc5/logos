module

public import Cpc.Proofs.RuleSupport.BvAbstractionSupport
import all Cpc.Proofs.RuleSupport.BvAbstractionSupport

public section

namespace BvAbstraction
namespace Urem15Case

theorem two_mul_xor (a b : Nat) :
    (2 * a) ^^^ (2 * b) = 2 * (a ^^^ b) := by
  simpa [Nat.shiftLeft_eq, Nat.mul_comm] using
    (Nat.shiftLeft_xor_distrib (a := a) (b := b) (i := 1)).symm

theorem two_mul_add_one_xor (a b : Nat) :
    (2 * a + 1) ^^^ (2 * b + 1) = 2 * (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, Nat.xor_div_two]
      have ha : (2 * a + 1) / 2 = a := by omega
      have hb : (2 * b + 1) / 2 = b := by omega
      have hab : (2 * (a ^^^ b)) / 2 = a ^^^ b := by omega
      rw [ha, hb, hab]

theorem complement_xor_or_ge (w a b : Nat)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    b ≤ (2 ^ w - 1 - b) ^^^ (a ||| b) := by
  let A := BitVec.ofNat w a
  let B := BitVec.ofNat w b
  have hA : A.toNat = a := by simp [A, Nat.mod_eq_of_lt ha]
  have hB : B.toNat = b := by simp [B, Nat.mod_eq_of_lt hb]
  have hid : (~~~B) ^^^ (A ||| B) = B ||| ~~~A := by
    ext i hi
    cases haBit : A[i] <;> cases hbBit : B[i] <;> simp_all
  have hn := congrArg BitVec.toNat hid
  simp only [BitVec.toNat_xor, BitVec.toNat_not, BitVec.toNat_or,
    hA, hB] at hn
  rw [hn]
  exact nat_le_or_left _ _

theorem even_remainder (x s bit : Nat) (hs : 0 < s) (hbit : bit < 2) :
    (2 * x + bit) % (2 * s) = 2 * (x % s) + bit := by
  rw [Nat.add_mod, Nat.mul_mod_mul_left]
  have hr : x % s < s := Nat.mod_lt _ hs
  have hbitMod : bit % (2 * s) = bit := by
    rw [Nat.mod_eq_of_lt]
    omega
  rw [hbitMod, Nat.mod_eq_of_lt]
  omega

theorem nat_urem15 : ∀ (w x s : Nat), x < 2 ^ w → s < 2 ^ w →
    let negs := if s = 0 then 0 else 2 ^ w - s
    x % s ≤ negs ^^^ (x ||| s) := by
  intro w
  induction w with
  | zero =>
      intro x s hx hs
      have hx0 : x = 0 := by omega
      have hs0 : s = 0 := by omega
      simp [hx0, hs0]
  | succ w ih =>
      intro x s hx hs
      by_cases hs0 : s = 0
      · simp [hs0]
      have hsPos : 0 < s := Nat.pos_of_ne_zero hs0
      rcases Nat.mod_two_eq_zero_or_one s with hsEven | hsOdd
      · let x' := x / 2
        let s' := s / 2
        have hxEq : x = 2 * x' + x % 2 := by dsimp [x']; omega
        have hsEq : s = 2 * s' := by dsimp [s']; omega
        have hs'Pos : 0 < s' := by rw [hsEq] at hsPos; omega
        have hs'Lt : s' < 2 ^ w := by
          rw [hsEq, Nat.pow_succ] at hs
          omega
        have hx'Lt : x' < 2 ^ w := by
          dsimp [x']
          rw [Nat.pow_succ] at hx
          omega
        have hrec := ih x' s' hx'Lt hs'Lt
        simp only [if_neg (Nat.ne_of_gt hs'Pos)] at hrec
        have hneg : 2 ^ (w + 1) - s = 2 * (2 ^ w - s') := by
          rw [Nat.pow_succ, hsEq]
          omega
        have hor : x ||| s = 2 * (x' ||| s') + x % 2 := by
          rcases Nat.mod_two_eq_zero_or_one x with hxEven | hxOdd
          · have hxEq0 : x = 2 * x' := by omega
            calc
              x ||| s = (2 * x') ||| (2 * s') := by rw [hxEq0, hsEq]
              _ = 2 * (x' ||| s') := two_mul_or _ _
              _ = 2 * (x' ||| s') + x % 2 := by rw [hxEven]; omega
          · have hxEq1 : x = 2 * x' + 1 := by omega
            calc
              x ||| s = (2 * x' + 1) ||| (2 * s') :=
                by rw [hxEq1, hsEq]
              _ = 2 * (x' ||| s') + 1 := by
                rw [Nat.or_comm, two_mul_or_two_mul_add_one, Nat.or_comm]
              _ = 2 * (x' ||| s') + x % 2 := by rw [hxOdd]
        have hrem : x % s = 2 * (x' % s') + x % 2 := by
          let bit := x % 2
          have hxEqBit : x = 2 * x' + bit := by simpa [bit] using hxEq
          have hcalc : x % s = 2 * (x' % s') + bit := by
            rw [hxEqBit, hsEq]
            exact even_remainder x' s' bit hs'Pos (by
              dsimp [bit]
              exact Nat.mod_lt _ (by decide))
          simpa [bit] using hcalc
        simp only [hs0, if_false, hneg, hor, hrem]
        rcases Nat.mod_two_eq_zero_or_one x with hxEven | hxOdd
        · rw [hxEven]
          simp only [Nat.add_zero, two_mul_xor]
          omega
        · rw [hxOdd]
          have hxor : (2 * (2 ^ w - s')) ^^^
              (2 * (x' ||| s') + 1) =
              2 * ((2 ^ w - s') ^^^ (x' ||| s')) + 1 := by
            apply Nat.eq_of_testBit_eq
            intro i
            cases i with
            | zero => simp
            | succ i =>
                rw [Nat.testBit_succ, Nat.testBit_succ, Nat.xor_div_two]
                have ha : (2 * (2 ^ w - s')) / 2 = 2 ^ w - s' := by omega
                have hb : (2 * (x' ||| s') + 1) / 2 = x' ||| s' := by omega
                have hc : (2 * ((2 ^ w - s') ^^^ (x' ||| s')) + 1) / 2 =
                    (2 ^ w - s') ^^^ (x' ||| s') := by omega
                rw [ha, hb, hc]
          rw [hxor]
          omega
      · let x' := x / 2
        let s' := s / 2
        have hxEq : x = 2 * x' + x % 2 := by dsimp [x']; omega
        have hsEq : s = 2 * s' + 1 := by dsimp [s']; omega
        have hs'Lt : s' < 2 ^ w := by
          rw [hsEq, Nat.pow_succ] at hs
          omega
        have hx'Lt : x' < 2 ^ w := by
          dsimp [x']
          rw [Nat.pow_succ] at hx
          omega
        have hneg : 2 ^ (w + 1) - s = 2 * (2 ^ w - 1 - s') + 1 := by
          rw [Nat.pow_succ, hsEq]
          omega
        have hor : x ||| s = 2 * (x' ||| s') + 1 := by
          rcases Nat.mod_two_eq_zero_or_one x with hxEven | hxOdd
          · have hxEq0 : x = 2 * x' := by omega
            rw [hxEq0, hsEq, two_mul_or_two_mul_add_one]
          · have hxEq1 : x = 2 * x' + 1 := by omega
            rw [hxEq1, hsEq, two_mul_add_one_or]
        have hlower := complement_xor_or_ge w x' s' hx'Lt hs'Lt
        have hrlt : x % s < s := Nat.mod_lt _ hsPos
        simp only [hs0, if_false, hneg, hor, two_mul_add_one_xor]
        omega

theorem urem15 {w : Nat} (x s : BitVec w) :
    x % s ≤ (-s) ^^^ (x ||| s) := by
  simp only [BitVec.le_def, BitVec.toNat_umod, BitVec.toNat_xor,
    BitVec.toNat_or]
  by_cases hs : s = 0#w
  · subst s
    simp
  · have hsNat : s.toNat ≠ 0 := BitVec.toNat_ne_iff_ne.mpr hs
    have hneg : (-s).toNat = 2 ^ w - s.toNat := by
      exact BitVec.toNat_neg_of_pos (by
        simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod]
        exact Nat.pos_of_ne_zero hsNat)
    rw [hneg]
    simpa [hsNat] using nat_urem15 w x.toNat s.toNat x.isLt s.isLt

end Urem15Case
end BvAbstraction
