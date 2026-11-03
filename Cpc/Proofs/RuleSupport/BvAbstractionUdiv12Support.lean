module

public import Cpc.Proofs.RuleSupport.BvAbstractionUrem13Support
import all Cpc.Proofs.RuleSupport.BvAbstractionUrem13Support

public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false

namespace BvAbstraction
namespace Udiv12Case

theorem and_complement_pos_of_lt {w b c : Nat}
    (hb : b < 2 ^ w) (hc : c < 2 ^ w) (hbc : b < c) :
    0 < c &&& (2 ^ w - 1 - b) := by
  have hcomp : 2 ^ w - 1 - b = 2 ^ w - (b + 1) := by grind
  rw [hcomp]
  by_cases hz : c &&& (2 ^ w - (b + 1)) = 0
  · have hcb : c ≤ b := by
      apply Nat.le_of_testBit
      intro i hci
      have hi : i < w := by
        by_cases hi : i < w
        · exact hi
        · have hbit := Nat.ge_two_pow_of_testBit hci
          have hpow := Nat.pow_le_pow_right (by decide : 0 < 2)
            (Nat.le_of_not_gt hi)
          grind
      have hzBit := congrArg (fun n : Nat => n.testBit i) hz
      simp only [Nat.testBit_and, Nat.zero_testBit, hci, Bool.true_and] at hzBit
      rw [Nat.testBit_two_pow_sub_succ hb] at hzBit
      simp [hi] at hzBit
      exact hzBit
    grind
  · grind

theorem strong_even_bound (A B C d : Nat) (hA : 0 < A) (hB : 0 < B)
    (hd : d ≤ 1)
    (h : 2 * (2 * A) * (2 * B) + 2 * A < 2 * C + d) :
    2 * A * B + A < C := by
  have hnorm :
      2 * (2 * A) * (2 * B) + 2 * A =
        2 * (4 * (A * B) + A) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_add]
  rw [hnorm] at h
  have hABpos : 0 < A * B := Nat.mul_pos hA hB
  have hmul : 2 * A * B = 2 * (A * B) := by
    simp [Nat.mul_assoc]
  rw [hmul]
  omega

theorem nat_udiv12_aux : ∀ w : Nat,
    (∀ a b c : Nat, a < 2 ^ w → b < 2 ^ w → c < 2 ^ w →
      a * b ≤ c → a &&& b ≤ c &&& ((2 ^ w - b) % 2 ^ w)) ∧
    (∀ a b c : Nat, a < 2 ^ w → b < 2 ^ w → c < 2 ^ w →
      2 * a * b + a ≤ c →
      a &&& b ≤ c &&& (2 ^ w - 1 - b) ∧
      (0 < a → 2 * a * b + a < c →
        a &&& b < c &&& (2 ^ w - 1 - b))) := by
  intro w
  induction w with
  | zero =>
      constructor
      · intro a b c ha hb hc hab
        simp at ha hb hc
        subst a
        subst b
        subst c
        simp
      · intro a b c ha hb hc hab
        simp at ha hb hc
        subst a
        subst b
        subst c
        simp
  | succ w ih =>
      let P := 2 ^ w
      have hPow : 2 ^ (w + 1) = 2 * P := by
        simp [P, Nat.pow_succ, Nat.mul_comm]
      constructor
      · intro a b c ha hb hc hab
        let A := a / 2
        let B := b / 2
        let C := c / 2
        have haEq : a = 2 * A + a % 2 := by dsimp [A]; grind
        have hbEq : b = 2 * B + b % 2 := by dsimp [B]; grind
        have hcEq : c = 2 * C + c % 2 := by dsimp [C]; grind
        have hA : A < P := by rw [hPow] at ha; dsimp [A]; grind
        have hB : B < P := by rw [hPow] at hb; dsimp [B]; grind
        have hC : C < P := by rw [hPow] at hc; dsimp [C]; grind
        rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1 <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1 <;>
          rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
        all_goals (first | rw [ha0] at haEq | rw [ha1] at haEq)
        all_goals (first | rw [hb0] at hbEq | rw [hb1] at hbEq)
        all_goals (first | rw [hc0] at hcEq | rw [hc1] at hcEq)
        all_goals try simp only [Nat.add_zero] at haEq hbEq hcEq
        all_goals rw [haEq, hbEq, hcEq] at hab
        all_goals simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_one, Nat.one_mul] at hab
        all_goals rw [hPow]
        · have hi := ih.1 A B C hA hB hC (by grind)
          have hB0 : B = 0 ∨ 0 < B := Nat.eq_zero_or_pos B
          rcases hB0 with hBz | hBp
          · subst B
            rw [hBz] at hbEq
            simp at hbEq
            subst b
            simp
          · have hmod : (2 * P - 2 * B) % (2 * P) = 2 * (P - B) := by
              rw [show 2 * P - 2 * B = 2 * (P - B) by grind]
              rw [Nat.mod_eq_of_lt (by grind)]
            have hi' : A &&& B ≤ C &&& (P - B) := by
              change A &&& B ≤ C &&& ((P - B) % P) at hi
              rw [Nat.mod_eq_of_lt (by grind)] at hi
              exact hi
            rw [haEq, hbEq, hcEq, hmod, two_mul_and, two_mul_and]
            exact Nat.mul_le_mul_left 2 hi'
        · have hi := ih.1 A B C hA hB hC (by grind)
          by_cases hBz : B = 0
          · subst B
            rw [hBz] at hbEq
            simp at hbEq
            subst b
            simp
          · have hmod : (2 * P - 2 * B) % (2 * P) = 2 * (P - B) := by
              rw [show 2 * P - 2 * B = 2 * (P - B) by grind]
              rw [Nat.mod_eq_of_lt (by grind)]
            have hi' : A &&& B ≤ C &&& (P - B) := by
              change A &&& B ≤ C &&& ((P - B) % P) at hi
              rw [Nat.mod_eq_of_lt (by grind)] at hi
              exact hi
            rw [haEq, hbEq, hcEq, hmod, two_mul_and,
              Nat.and_comm (2 * C + 1) (2 * (P - B)),
              Udiv32Case.two_mul_and_two_mul_add_one]
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          have hneg : (2 * P - (2 * B + 1)) % (2 * P) =
              2 * (P - 1 - B) + 1 := by
            rw [show 2 * P - (2 * B + 1) = 2 * (P - 1 - B) + 1 by grind]
            rw [Nat.mod_eq_of_lt (by grind)]
          rw [haEq, hbEq, hcEq, hneg,
            Udiv32Case.two_mul_and_two_mul_add_one,
            Udiv32Case.two_mul_and_two_mul_add_one]
          grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          have hneg : (2 * P - (2 * B + 1)) % (2 * P) =
              2 * (P - 1 - B) + 1 := by
            rw [show 2 * P - (2 * B + 1) = 2 * (P - 1 - B) + 1 by grind]
            rw [Nat.mod_eq_of_lt (by grind)]
          rw [haEq, hbEq, hcEq, hneg,
            Udiv32Case.two_mul_and_two_mul_add_one, two_mul_add_one_and]
          grind
        · have hi := ih.1 A B C hA hB hC (by grind)
          by_cases hBz : B = 0
          · subst B
            rw [hBz] at hbEq
            simp at hbEq
            subst b
            simp
          · have hmod : (2 * P - 2 * B) % (2 * P) = 2 * (P - B) := by
              rw [show 2 * P - 2 * B = 2 * (P - B) by grind]
              rw [Nat.mod_eq_of_lt (by grind)]
            have hi' : A &&& B ≤ C &&& (P - B) := by
              change A &&& B ≤ C &&& ((P - B) % P) at hi
              rw [Nat.mod_eq_of_lt (by grind)] at hi
              exact hi
            rw [haEq, hbEq, hcEq, hmod, Nat.and_comm (2 * A + 1) (2 * B),
              Udiv32Case.two_mul_and_two_mul_add_one, two_mul_and]
            simpa [Nat.and_comm] using Nat.mul_le_mul_left 2 hi'
        · have hi := ih.1 A B C hA hB hC (by grind)
          by_cases hBz : B = 0
          · subst B
            rw [hBz] at hbEq
            simp at hbEq
            subst b
            simp
          · have hmod : (2 * P - 2 * B) % (2 * P) = 2 * (P - B) := by
              rw [show 2 * P - 2 * B = 2 * (P - B) by grind]
              rw [Nat.mod_eq_of_lt (by grind)]
            have hi' : A &&& B ≤ C &&& (P - B) := by
              change A &&& B ≤ C &&& ((P - B) % P) at hi
              rw [Nat.mod_eq_of_lt (by grind)] at hi
              exact hi
            rw [haEq, hbEq, hcEq, hmod, Nat.and_comm (2 * A + 1) (2 * B),
              Udiv32Case.two_mul_and_two_mul_add_one,
              Nat.and_comm (2 * C + 1) (2 * (P - B)),
              Udiv32Case.two_mul_and_two_mul_add_one]
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          have hneg : (2 * P - (2 * B + 1)) % (2 * P) =
              2 * (P - 1 - B) + 1 := by
            rw [show 2 * P - (2 * B + 1) = 2 * (P - 1 - B) + 1 by grind]
            rw [Nat.mod_eq_of_lt (by grind)]
          have hhi : A &&& B < C &&& (P - 1 - B) := by
            by_cases hAz : A = 0
            · change A &&& B < C &&& (P - 1 - B)
              rw [hAz]
              simpa [P] using and_complement_pos_of_lt hB hC (by grind)
            · exact hi.2 (by grind) (by grind)
          rw [haEq, hbEq, hcEq, hneg, two_mul_add_one_and,
            Udiv32Case.two_mul_and_two_mul_add_one]
          grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          have hneg : (2 * P - (2 * B + 1)) % (2 * P) =
              2 * (P - 1 - B) + 1 := by
            rw [show 2 * P - (2 * B + 1) = 2 * (P - 1 - B) + 1 by grind]
            rw [Nat.mod_eq_of_lt (by grind)]
          rw [haEq, hbEq, hcEq, hneg, two_mul_add_one_and,
            two_mul_add_one_and]
          grind
      · intro a b c ha hb hc hab
        let A := a / 2
        let B := b / 2
        let C := c / 2
        have haEq : a = 2 * A + a % 2 := by dsimp [A]; grind
        have hbEq : b = 2 * B + b % 2 := by dsimp [B]; grind
        have hcEq : c = 2 * C + c % 2 := by dsimp [C]; grind
        have hA : A < P := by rw [hPow] at ha; dsimp [A]; grind
        have hB : B < P := by rw [hPow] at hb; dsimp [B]; grind
        have hC : C < P := by rw [hPow] at hc; dsimp [C]; grind
        rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1 <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1 <;>
          rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
        all_goals (first | rw [ha0] at haEq | rw [ha1] at haEq)
        all_goals (first | rw [hb0] at hbEq | rw [hb1] at hbEq)
        all_goals (first | rw [hc0] at hcEq | rw [hc1] at hcEq)
        all_goals try simp only [Nat.add_zero] at haEq hbEq hcEq
        all_goals rw [haEq, hbEq, hcEq] at hab
        all_goals simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_one, Nat.one_mul] at hab
        all_goals rw [hPow]
        all_goals have hcomp : 2 * P - 1 - (2 * B) = 2 * (P - 1 - B) + 1 := by grind
        all_goals have hcompOdd : 2 * P - 1 - (2 * B + 1) = 2 * (P - 1 - B) := by grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcomp, two_mul_and,
            Udiv32Case.two_mul_and_two_mul_add_one]
          constructor
          · grind
          · intro haPos hlt
            by_cases hAz : A = 0
            · subst A
              grind
            by_cases hBz : B = 0
            · subst B
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hsmall := strong_even_bound A B C 0 (by omega) (by omega)
              (by omega) hlt
            have hs := hi.2 (by omega) hsmall
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcomp, two_mul_and,
            two_mul_add_one_and]
          constructor
          · grind
          · intro haPos hlt
            by_cases hAz : A = 0
            · subst A
              grind
            by_cases hBz : B = 0
            · subst B
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hsmall := strong_even_bound A B C 1 (by omega) (by omega)
              (by omega) hlt
            have hs := hi.2 (by omega) hsmall
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcompOdd,
            Udiv32Case.two_mul_and_two_mul_add_one, two_mul_and]
          constructor
          · grind
          · intro haPos hlt
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcompOdd,
            Udiv32Case.two_mul_and_two_mul_add_one,
            Nat.and_comm (2 * C + 1) (2 * (P - 1 - B)),
            Udiv32Case.two_mul_and_two_mul_add_one]
          constructor
          · grind
          · intro haPos hlt
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcomp,
            Nat.and_comm (2 * A + 1) (2 * B),
            Udiv32Case.two_mul_and_two_mul_add_one,
            Udiv32Case.two_mul_and_two_mul_add_one]
          constructor
          · grind
          · intro haPos hlt
            by_cases hAz : A = 0
            · subst A
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            by_cases hBz : B = 0
            · subst B
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hs := hi.2 (by grind) (by grind)
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcomp,
            Nat.and_comm (2 * A + 1) (2 * B),
            Udiv32Case.two_mul_and_two_mul_add_one, two_mul_add_one_and]
          constructor
          · grind
          · intro haPos hlt
            by_cases hAz : A = 0
            · subst A
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            by_cases hBz : B = 0
            · subst B
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hs := hi.2 (by grind) (by grind)
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcompOdd, two_mul_add_one_and, two_mul_and]
          constructor
          · by_cases hAz : A = 0
            · subst A
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hs := hi.2 (by grind) (by grind)
            grind
          · intro haPos hlt
            by_cases hAz : A = 0
            · subst A
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hs := hi.2 (by grind) (by grind)
            grind
        · have hi := ih.2 A B C hA hB hC (by grind)
          change A &&& B ≤ C &&& (P - 1 - B) ∧ _ at hi
          rw [haEq, hbEq, hcEq, hcompOdd, two_mul_add_one_and,
            Nat.and_comm (2 * C + 1) (2 * (P - 1 - B)),
            Udiv32Case.two_mul_and_two_mul_add_one]
          constructor
          · by_cases hAz : A = 0
            · subst A
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hs := hi.2 (by grind) (by grind)
            grind
          · intro haPos hlt
            by_cases hAz : A = 0
            · subst A
              have hp := and_complement_pos_of_lt hB hC (by grind)
              grind
            have hs := hi.2 (by grind) (by grind)
            grind

theorem udiv12 {w : Nat} (x s : BitVec w) :
    (s &&& x.smtUDiv s) ≤ (x &&& -(x.smtUDiv s)) := by
  let q := x.smtUDiv s
  change s &&& q ≤ x &&& -q
  by_cases hs : s = 0#w
  · subst s
    simp [q, BitVec.le_def]
  have hq : q.toNat = x.toNat / s.toNat := by
    dsimp [q]
    rw [BitVec.smtUDiv_eq, if_neg hs, BitVec.toNat_udiv]
  have hsPos : 0 < s.toNat :=
    Nat.pos_of_ne_zero (BitVec.toNat_ne_iff_ne.mpr hs)
  have hprod : s.toNat * q.toNat ≤ x.toNat := by
    rw [hq]
    exact Nat.mul_div_le x.toNat s.toNat
  have hnq : (-q).toNat = (2 ^ w - q.toNat) % 2 ^ w := by
    simp [BitVec.toNat_neg]
  simp only [BitVec.le_def, BitVec.toNat_and, hnq]
  exact (nat_udiv12_aux w).1 s.toNat q.toNat x.toNat
    s.isLt q.isLt x.isLt hprod

end Udiv12Case
end BvAbstraction
