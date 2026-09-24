module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVec
import all Cpc.Proofs.TypePreservation.BitVec

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem natpow2_eq (w : Nat) :
    native_int_pow2 (↑w : Int) = (2 : Int) ^ w := by
  have hwnn : ¬ ((↑w : Int) < 0) := by omega
  unfold native_int_pow2 native_zexp_total
  rw [if_neg hwnn, Int.toNat_natCast]

private theorem ofInt_toNat_canonical (w : Nat) (c : Int)
    (h0 : 0 ≤ c) (h1 : c < 2 ^ w) :
    (BitVec.ofInt w c).toNat = c.toNat := by
  rw [BitVec.toNat_ofInt]
  congr 1
  exact Int.emod_eq_of_lt h0 (by exact_mod_cast h1)

private theorem extract_valN (W : Nat) (Xn : Int) (hi lo : Nat)
    (hX0 : 0 ≤ Xn) (hlo : lo ≤ hi + 1) :
    __smtx_model_eval_extract (SmtValue.Numeral ↑hi) (SmtValue.Numeral ↑lo)
        (SmtValue.Binary ↑W Xn) =
      SmtValue.Binary ↑(hi + 1 - lo)
        ↑((Xn.toNat / 2 ^ lo) % 2 ^ (hi + 1 - lo)) := by
  obtain ⟨N, rfl⟩ : ∃ N : Nat, Xn = (↑N : Int) :=
    ⟨Xn.toNat, (Int.toNat_of_nonneg hX0).symm⟩
  simp only [__smtx_model_eval_extract, native_zplus, native_zneg,
    native_mod_total, native_binary_extract, native_div_total, Int.toNat_natCast]
  have hw : (↑hi + 1 + -↑lo : Int) = ↑(hi + 1 - lo) := by omega
  rw [hw, natpow2_eq lo, natpow2_eq (hi + 1 - lo),
    show ((2 : Int) ^ lo) = ((2 ^ lo : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (hi + 1 - lo)) = ((2 ^ (hi + 1 - lo) : Nat) : Int) by
      norm_cast]
  norm_cast

private theorem concat_valN (w1 p1 w2 p2 : Nat) :
    __smtx_model_eval_concat (SmtValue.Binary ↑w1 ↑p1)
        (SmtValue.Binary ↑w2 ↑p2) =
      SmtValue.Binary ↑(w1 + w2)
        ↑((p1 * 2 ^ w2 + p2) % 2 ^ (w1 + w2)) := by
  simp only [__smtx_model_eval_concat, native_zplus, native_mod_total,
    native_binary_concat, native_zmult]
  have hw : (↑w1 + ↑w2 : Int) = ↑(w1 + w2) := by norm_cast
  rw [hw, natpow2_eq w2, natpow2_eq (w1 + w2),
    show ((2 : Int) ^ w2) = ((2 ^ w2 : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (w1 + w2)) = ((2 ^ (w1 + w2) : Nat) : Int) by norm_cast]
  norm_cast

private theorem append_extract_eq_rotateLeft_one_aux
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((x.extractLsb' 0 (w - 1)) ++ (x.extractLsb' (w - 1) 1)).cast (by omega) =
      x.rotateLeft 1 := by
  cases w with
  | zero => omega
  | succ w =>
      cases w with
      | zero =>
          apply BitVec.eq_of_getElem_eq
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          simp only [BitVec.getElem_cast, BitVec.getElem_append]
          simp [BitVec.rotateLeft, BitVec.rotateLeftAux]
      | succ w =>
          have hmod : 1 % (w + 2) = 1 := Nat.mod_eq_of_lt (by omega)
          apply BitVec.eq_of_getElem_eq
          intro i hi
          simp only [BitVec.getElem_cast, BitVec.getElem_append,
            BitVec.getElem_extractLsb']
          rw [BitVec.getElem_rotateLeft hi]
          simp only [hmod]
          by_cases hi0 : i = 0
          · subst i
            simp [BitVec.getLsbD_eq_getElem]
          · have hi1 : 1 ≤ i := by omega
            have hiNot : ¬ i < 1 := by omega
            simp only [hiNot, Nat.zero_add]
            simp
            rw [BitVec.getLsbD_eq_getElem
              (Nat.lt_of_le_of_lt (Nat.sub_le i 1) hi)]

private theorem append_extract_eq_rotateRight_one_aux
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    ((x.extractLsb' 0 1) ++ (x.extractLsb' 1 (w - 1))).cast (by omega) =
      x.rotateRight 1 := by
  cases w with
  | zero => omega
  | succ w =>
      cases w with
      | zero =>
          apply BitVec.eq_of_getElem_eq
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          simp only [BitVec.getElem_cast, BitVec.getElem_append,
            BitVec.getElem_extractLsb']
          simp [BitVec.rotateRight, BitVec.rotateRightAux]
      | succ w =>
          have hmod : 1 % (w + 2) = 1 := Nat.mod_eq_of_lt (by omega)
          apply BitVec.eq_of_getElem_eq
          intro i hi
          simp only [BitVec.getElem_cast, BitVec.getElem_append,
            BitVec.getElem_extractLsb']
          rw [BitVec.getElem_rotateRight hi]
          simp only [hmod]
          have hCut : w + 1 + 1 - 1 = w + 1 := by omega
          by_cases hLow : i < w + 1
          · simp [hCut, hLow]
            rw [BitVec.getLsbD_eq_getElem (by omega)]
          · have hiTop : i = w + 1 := by omega
            subst i
            simp [BitVec.getLsbD_eq_getElem]

private theorem rotateLeft_rotateLeft (x : BitVec w) (a b : Nat) :
    (x.rotateLeft a).rotateLeft b = x.rotateLeft (a + b) := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  have hw : 0 < w := by omega
  simp only [BitVec.getMsbD_rotateLeft, hi, decide_true, Bool.true_and]
  have hmod : (b + i) % w < w := Nat.mod_lt _ hw
  simp only [BitVec.getMsbD_rotateLeft, hmod, decide_true, Bool.true_and]
  congr 1
  simp [Nat.add_mod, Nat.add_assoc]

private theorem rotateRight_one_eq_rotateLeft_pred
    {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.rotateRight 1 = x.rotateLeft (w - 1) := by
  cases w with
  | zero => omega
  | succ w =>
      cases w with
      | zero =>
          apply BitVec.eq_of_getMsbD_eq
          intro i hi
          have hi0 : i = 0 := by omega
          subst i
          simp [BitVec.getMsbD_rotateRight, BitVec.getMsbD_rotateLeft]
      | succ w =>
          have hmod : 1 % (w + 2) = 1 := Nat.mod_eq_of_lt (by omega)
          apply BitVec.eq_of_getMsbD_eq
          intro i hi
          rw [BitVec.getMsbD_rotateRight, BitVec.getMsbD_rotateLeft]
          simp only [hi, decide_true, Bool.true_and, hmod]
          by_cases hi0 : i = 0
          · subst i
            simp
          · have hi1 : 1 ≤ i := by omega
            have hiNot : ¬ i < 1 := by omega
            simp only [hiNot, ↓reduceIte]
            congr 1
            have hSum : w + 2 - 1 + i = (w + 2) + (i - 1) := by omega
            rw [hSum, Nat.add_mod]
            simp [Nat.mod_eq_of_lt (by omega : i - 1 < w + 2)]

private def leftStep (w p : Int) : SmtValue :=
  __smtx_model_eval_concat
    (__smtx_model_eval_extract
      (SmtValue.Numeral
        (native_zplus (native_zplus w (native_zneg 1)) (native_zneg 1)))
      (SmtValue.Numeral 0) (SmtValue.Binary w p))
    (__smtx_model_eval_extract
      (SmtValue.Numeral (native_zplus w (native_zneg 1)))
      (SmtValue.Numeral (native_zplus w (native_zneg 1)))
      (SmtValue.Binary w p))

private theorem leftStep_eq_rotateLeft_one
    (W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    leftStep (↑W) p =
      SmtValue.Binary (↑W)
        (↑((BitVec.ofInt W p).rotateLeft 1).toNat) := by
  cases W with
  | zero =>
      have hp : p = 0 := by simp at hp1; omega
      subst p
      native_decide
  | succ W =>
      cases W with
      | zero =>
          have hp : p = 0 ∨ p = 1 := by simp at hp1; omega
          rcases hp with rfl | rfl <;> native_decide
      | succ W =>
          have hNat : W + 1 + 1 = W + 2 := by omega
          rw [hNat] at hp1 ⊢
          have hToNat : (BitVec.ofInt (W + 2) p).toNat = p.toNat :=
            ofInt_toNat_canonical (W + 2) p hp0 hp1
          have hLowHi : ((↑(W + 2) : Int) + -1 + -1) = ↑W := by omega
          have hHigh : ((↑(W + 2) : Int) + -1) = ↑(W + 1) := by omega
          unfold leftStep
          simp only [SmtEval.native_zplus, SmtEval.native_zneg]
          rw [hLowHi, hHigh]
          have hLowEval :
              __smtx_model_eval_extract (SmtValue.Numeral (↑W))
                  (SmtValue.Numeral 0) (SmtValue.Binary (↑(W + 2)) p) =
                SmtValue.Binary (↑(W + 1))
                  (↑((p.toNat % 2 ^ (W + 1)) : Nat) : Int) := by
            simpa using extract_valN (W + 2) p W 0 hp0 (by omega)
          rw [hLowEval]
          rw [extract_valN (W + 2) p (W + 1) (W + 1) hp0 (by omega)]
          have hOne : W + 1 + 1 - (W + 1) = 1 := by omega
          rw [hOne]
          rw [concat_valN (W + 1) _ 1 _]
          simp only [Nat.add_sub_cancel_left, Nat.sub_self, Nat.add_zero,
            Nat.pow_zero, Nat.div_one, Nat.add_sub_cancel, Nat.add_assoc]
          congr 2
          let x := BitVec.ofInt (W + 2) p
          let low := x.extractLsb' 0 (W + 1)
          let high := x.extractLsb' (W + 1) 1
          let joined := low ++ high
          have hHighLt : high.toNat < 2 ^ 1 := high.isLt
          have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hHighLt low.toNat
          have hFormula :
              p.toNat % 2 ^ (W + 1) * 2 ^ 1 +
                  p.toNat / 2 ^ (W + 1) % 2 ^ 1 =
                joined.toNat := by
            rw [BitVec.toNat_append]
            rw [← hShiftOr, Nat.shiftLeft_eq]
            simp [low, high, x, BitVec.extractLsb'_toNat, hToNat,
              Nat.shiftRight_eq_div_pow]
          rw [hFormula]
          have hJoinedLt : joined.toNat < 2 ^ (W + 2) := by
            simpa [joined, low, high] using joined.isLt
          rw [Nat.mod_eq_of_lt hJoinedLt]
          have hRotate := append_extract_eq_rotateLeft_one_aux
            (by omega : 0 < W + 2) x
          have hAppend :
              ((x.extractLsb' 0 (W + 1)) ++ (x.extractLsb' (W + 1) 1)).toNat =
                (x.rotateLeft 1).toNat := by
            simpa [x] using congrArg BitVec.toNat hRotate
          exact hAppend

private def rightStep (w p : Int) : SmtValue :=
  __smtx_model_eval_concat
    (__smtx_model_eval_extract (SmtValue.Numeral 0)
      (SmtValue.Numeral 0) (SmtValue.Binary w p))
    (__smtx_model_eval_extract
      (SmtValue.Numeral (native_zplus w (native_zneg 1)))
      (SmtValue.Numeral 1) (SmtValue.Binary w p))

private theorem rightStep_eq_rotateRight_one
    (W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    rightStep (↑W) p =
      SmtValue.Binary (↑W)
        (↑((BitVec.ofInt W p).rotateRight 1).toNat) := by
  cases W with
  | zero =>
      have hp : p = 0 := by simp at hp1; omega
      subst p
      native_decide
  | succ W =>
      cases W with
      | zero =>
          have hp : p = 0 ∨ p = 1 := by simp at hp1; omega
          rcases hp with rfl | rfl <;> native_decide
      | succ W =>
          have hNat : W + 1 + 1 = W + 2 := by omega
          rw [hNat] at hp1 ⊢
          have hToNat : (BitVec.ofInt (W + 2) p).toNat = p.toNat :=
            ofInt_toNat_canonical (W + 2) p hp0 hp1
          have hHigh : ((↑(W + 2) : Int) + -1) = ↑(W + 1) := by omega
          unfold rightStep
          simp only [SmtEval.native_zplus, SmtEval.native_zneg]
          rw [hHigh]
          have hBitEval :
              __smtx_model_eval_extract (SmtValue.Numeral 0)
                  (SmtValue.Numeral 0) (SmtValue.Binary (↑(W + 2)) p) =
                SmtValue.Binary 1 (↑((p.toNat % 2) : Nat) : Int) := by
            simpa using extract_valN (W + 2) p 0 0 hp0 (by omega)
          rw [hBitEval]
          have hRestWidth : W + 1 + 1 - 1 = W + 1 := by omega
          have hRestEval :
              __smtx_model_eval_extract (SmtValue.Numeral (↑(W + 1)))
                  (SmtValue.Numeral 1) (SmtValue.Binary (↑(W + 2)) p) =
                SmtValue.Binary (↑(W + 1))
                  (↑((p.toNat / 2 % 2 ^ (W + 1)) : Nat) : Int) := by
            exact extract_valN (W + 2) p (W + 1) 1 hp0 (by omega)
          rw [hRestEval]
          have hConcatEval :
              __smtx_model_eval_concat
                  (SmtValue.Binary 1 (↑((p.toNat % 2) : Nat) : Int))
                  (SmtValue.Binary (↑(W + 1))
                    (↑((p.toNat / 2 % 2 ^ (W + 1)) : Nat) : Int)) =
                SmtValue.Binary (↑(W + 2))
                  (↑(((p.toNat % 2) * 2 ^ (W + 1) +
                    p.toNat / 2 % 2 ^ (W + 1)) % 2 ^ (W + 2) : Nat) : Int) := by
            -- v4.33 no longer normalises `1 + (W + 1)` to `W + 2` on its own.
            have hWn : 1 + (W + 1) = W + 2 := by omega
            have hWi : (1 : Int) + ((W : Int) + 1) = (W : Int) + 2 := by omega
            simpa [hWn, hWi, Nat.add_comm] using
              concat_valN 1 (p.toNat % 2) (W + 1) (p.toNat / 2 % 2 ^ (W + 1))
          rw [hConcatEval]
          congr 2
          let x := BitVec.ofInt (W + 2) p
          let low := x.extractLsb' 0 1
          let rest := x.extractLsb' 1 (W + 1)
          let joined := low ++ rest
          have hRestLt : rest.toNat < 2 ^ (W + 1) := rest.isLt
          have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hRestLt low.toNat
          have hFormula :
              p.toNat % 2 * 2 ^ (W + 1) +
                  p.toNat / 2 % 2 ^ (W + 1) =
                joined.toNat := by
            rw [BitVec.toNat_append]
            rw [← hShiftOr, Nat.shiftLeft_eq]
            simp [low, rest, x, BitVec.extractLsb'_toNat, hToNat,
              Nat.shiftRight_eq_div_pow]
          rw [hFormula]
          have hWidth : 1 + (W + 1) = W + 2 := by omega
          have hJoinedLt : joined.toNat < 2 ^ (W + 2) := by
            simpa only [hWidth] using joined.isLt
          rw [Nat.mod_eq_of_lt hJoinedLt]
          have hRotate := append_extract_eq_rotateRight_one_aux
            (by omega : 0 < W + 2) x
          have hAppend :
              ((x.extractLsb' 0 1) ++ (x.extractLsb' 1 (W + 1))).toNat =
                (x.rotateRight 1).toNat := by
            simpa [x] using congrArg BitVec.toNat hRotate
          exact hAppend

private theorem ofInt_natCast_toNat (x : BitVec w) :
    BitVec.ofInt w (Int.ofNat x.toNat) = x := by
  simp [BitVec.ofInt_natCast, BitVec.ofNat_toNat]

private theorem rotateLeft_zero (x : BitVec w) :
    x.rotateLeft 0 = x := by
  apply BitVec.eq_of_getMsbD_eq
  intro i hi
  simp [BitVec.getMsbD_rotateLeft, hi, Nat.mod_eq_of_lt hi]

private theorem rotateLeftRec_eq
    (n W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_rotate_left_rec n (SmtValue.Binary (↑W) p) =
      SmtValue.Binary (↑W)
        (↑((BitVec.ofInt W p).rotateLeft n).toNat) := by
  induction n generalizing p with
  | zero =>
      rw [__smtx_rotate_left_rec, rotateLeft_zero,
        ofInt_toNat_canonical W p hp0 hp1, Int.toNat_of_nonneg hp0]
  | succ n ih =>
      rw [__smtx_rotate_left_rec]
      change __smtx_rotate_left_rec n (leftStep (↑W) p) = _
      rw [leftStep_eq_rotateLeft_one W p hp0 hp1]
      let y := (BitVec.ofInt W p).rotateLeft 1
      have hy0 : 0 ≤ (Int.ofNat y.toNat) := Int.natCast_nonneg _
      have hy1 : (Int.ofNat y.toNat) < (2 : Int) ^ W := by
        have hPow : (2 : Int) ^ W = Int.ofNat (2 ^ W) := by norm_cast
        rw [hPow]
        exact Int.ofNat_lt.mpr y.isLt
      change __smtx_rotate_left_rec n
        (SmtValue.Binary (↑W) (Int.ofNat y.toNat)) = _
      rw [ih (Int.ofNat y.toNat) hy0 hy1]
      congr 2
      rw [ofInt_natCast_toNat]
      rw [show y = (BitVec.ofInt W p).rotateLeft 1 by rfl]
      have hRotate := congrArg BitVec.toNat
        (rotateLeft_rotateLeft (BitVec.ofInt W p) 1 n)
      rw [Nat.add_comm 1 n] at hRotate
      exact hRotate

private theorem rotateRightRec_eq
    (n W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_rotate_right_rec n (SmtValue.Binary (↑W) p) =
      SmtValue.Binary (↑W)
        (↑((BitVec.ofInt W p).rotateLeft (n * (W - 1))).toNat) := by
  induction n generalizing p with
  | zero =>
      rw [__smtx_rotate_right_rec]
      simp only [Nat.zero_mul]
      rw [rotateLeft_zero, ofInt_toNat_canonical W p hp0 hp1,
        Int.toNat_of_nonneg hp0]
  | succ n ih =>
      rw [__smtx_rotate_right_rec]
      change __smtx_rotate_right_rec n (rightStep (↑W) p) = _
      rw [rightStep_eq_rotateRight_one W p hp0 hp1]
      let y := (BitVec.ofInt W p).rotateRight 1
      have hy0 : 0 ≤ (Int.ofNat y.toNat) := Int.natCast_nonneg _
      have hy1 : (Int.ofNat y.toNat) < (2 : Int) ^ W := by
        have hPow : (2 : Int) ^ W = Int.ofNat (2 ^ W) := by norm_cast
        rw [hPow]
        exact Int.ofNat_lt.mpr y.isLt
      change __smtx_rotate_right_rec n
        (SmtValue.Binary (↑W) (Int.ofNat y.toNat)) = _
      rw [ih (Int.ofNat y.toNat) hy0 hy1]
      congr 2
      rw [ofInt_natCast_toNat]
      cases W with
      | zero =>
          apply congrArg BitVec.toNat
          apply BitVec.eq_of_getMsbD_eq
          intro i hi
          omega
      | succ W =>
          have hRight := rotateRight_one_eq_rotateLeft_pred
            (by omega : 0 < W + 1) (BitVec.ofInt (W + 1) p)
          rw [show y = (BitVec.ofInt (W + 1) p).rotateRight 1 by rfl]
          rw [hRight]
          have hRotate := congrArg BitVec.toNat
            (rotateLeft_rotateLeft (BitVec.ofInt (W + 1) p)
              (W + 1 - 1) (n * (W + 1 - 1)))
          rw [Nat.add_comm (W + 1 - 1) (n * (W + 1 - 1))] at hRotate
          rw [Nat.succ_mul]
          exact hRotate

/-- Canonical value-level interpretation of the recursive left-rotation evaluator. -/
theorem bv_rotate_left_rec_eval
    (n W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_rotate_left_rec n (SmtValue.Binary (↑W) p) =
      SmtValue.Binary (↑W)
        (↑((BitVec.ofInt W p).rotateLeft n).toNat) :=
  rotateLeftRec_eq n W p hp0 hp1

/-- Canonical value-level interpretation of the recursive right-rotation evaluator. -/
theorem bv_rotate_right_rec_eval
    (n W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_rotate_right_rec n (SmtValue.Binary (↑W) p) =
      SmtValue.Binary (↑W)
        (↑((BitVec.ofInt W p).rotateLeft (n * (W - 1))).toNat) :=
  rotateRightRec_eq n W p hp0 hp1

private theorem rotateLeft_eq_self_of_mod_eq_zero
    (x : BitVec w) (n : Nat) (hmod : n % w = 0) :
    x.rotateLeft n = x := by
  rw [← BitVec.rotateLeft_mod_eq_rotateLeft, hmod]
  exact rotateLeft_zero x

private theorem rotateRightTracked_eq_self_of_mod_eq_zero
    (x : BitVec w) (n : Nat) (hmod : n % w = 0) :
    x.rotateLeft (n * (w - 1)) = x := by
  cases w with
  | zero =>
      apply BitVec.eq_of_getMsbD_eq
      intro i hi
      omega
  | succ w =>
      apply rotateLeft_eq_self_of_mod_eq_zero
      have hdiv : w + 1 ∣ n := Nat.dvd_of_mod_eq_zero hmod
      rcases hdiv with ⟨k, rfl⟩
      simp [Nat.mul_assoc]

private theorem rotateLeft_eq_self_of_width_zero_or_mod_eq_zero
    (x : BitVec w) (n : Nat) (h : w = 0 ∨ n % w = 0) :
    x.rotateLeft n = x := by
  rcases h with hWidth | hMod
  · subst w
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    omega
  · exact rotateLeft_eq_self_of_mod_eq_zero x n hMod

private theorem rotateRightTracked_eq_self_of_width_zero_or_mod_eq_zero
    (x : BitVec w) (n : Nat) (h : w = 0 ∨ n % w = 0) :
    x.rotateLeft (n * (w - 1)) = x := by
  rcases h with hWidth | hMod
  · subst w
    apply BitVec.eq_of_getMsbD_eq
    intro i hi
    omega
  · exact rotateRightTracked_eq_self_of_mod_eq_zero x n hMod

inductive BvRotateElimKind where
  | left
  | right
  deriving DecidableEq

def bvRotateElimLhs (k : BvRotateElimKind) (x amount : Term) : Term :=
  match k with
  | .left => Term.Apply (Term.UOp1 UserOp1.rotate_left amount) x
  | .right => Term.Apply (Term.UOp1 UserOp1.rotate_right amount) x

def bvRotateElimTerm (k : BvRotateElimKind) (x amount : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvRotateElimLhs k x amount)) x

def bvRotateElimPrem (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) amount)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Numeral 0)

private theorem rotate_amount_nonneg_of_guard
    (amount : Term) :
    __eo_gt amount (Term.Numeral (-1 : native_Int)) = Term.Boolean true ->
    ∃ i : native_Int, amount = Term.Numeral i ∧ native_zleq 0 i = true := by
  intro h
  cases amount <;> simp [__eo_gt] at h
  case Numeral i =>
    have hi : (-1 : native_Int) < i := by
      simpa [SmtEval.native_zlt] using h
    have hi0 : (0 : native_Int) ≤ i := by
      simpa using Int.add_one_le_iff.mpr hi
    exact ⟨i, rfl, by simpa [SmtEval.native_zleq] using hi0⟩

private theorem eo_typeof_rotate_arg_bitvec_of_ne_stuck
    {A amount C : Term}
    (h : __eo_typeof_rotate_left A amount C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_rotate_left at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_rotate_requires_of_ne_stuck
    {amount w : Term}
    (h :
      __eo_typeof_rotate_left (__eo_typeof amount) amount
          (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck) :
    __eo_requires (__eo_gt amount (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true)
        (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
      Term.Stuck := by
  unfold __eo_typeof_rotate_left at h
  split at h <;> simp_all

theorem bv_rotate_elim_args_type_of_bool
    (k : BvRotateElimKind) (x amount : Term) :
    __eo_typeof (bvRotateElimTerm k x amount) = Term.Bool ->
    ∃ w i,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      amount = Term.Numeral i ∧ native_zleq 0 i = true := by
  intro hTy
  have hRotNe :
      __eo_typeof_rotate_left (__eo_typeof amount) amount (__eo_typeof x) ≠
        Term.Stuck := by
    have hOperands := RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (bvRotateElimLhs k x amount)) (__eo_typeof x)
      (by cases k <;> exact hTy)
    cases k <;> exact hOperands.1
  rcases eo_typeof_rotate_arg_bitvec_of_ne_stuck hRotNe with ⟨w, hXTy⟩
  have hReq :
      __eo_requires (__eo_gt amount (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck :=
    eo_typeof_rotate_requires_of_ne_stuck (by simpa [hXTy] using hRotNe)
  have hGuard :
      __eo_gt amount (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  rcases rotate_amount_nonneg_of_guard amount hGuard with ⟨i, hAmount, hi0⟩
  exact ⟨w, i, hXTy, hAmount, hi0⟩

private theorem smt_bitvec_type_of_eo_bitvec_type_with_width
    (x w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w ->
    ∃ n, w = Term.Numeral n ∧ native_zleq 0 n = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat n) := by
  intro hXTrans hXType
  have hSmtType :
      __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (Term.Apply (Term.UOp UserOp.BitVec) w) (__eo_to_smt x) rfl
        hXTrans hXType
  cases w <;> simp [__eo_to_smt_type] at hSmtType
  case Numeral n =>
    cases hNonneg : native_zleq 0 n <;>
      simp [__eo_to_smt_type, hNonneg] at hSmtType
    · exact False.elim (hXTrans hSmtType)
    · exact ⟨n, rfl, hNonneg, hSmtType⟩
  all_goals exact False.elim (hXTrans hSmtType)

theorem bv_rotate_elim_context
    (k : BvRotateElimKind) (x amount : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateElimTerm k x amount) = Term.Bool ->
    ∃ i w,
      amount = Term.Numeral i ∧
      native_zleq 0 i = true ∧
      native_zleq 0 w = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hTy
  rcases bv_rotate_elim_args_type_of_bool k x amount hTy with
    ⟨width, i, hXTy, hAmount, hi0⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width x width hXTrans hXTy with
    ⟨w, hWidth, hw0, hXSmtTy⟩
  subst width
  exact ⟨i, w, hAmount, hi0, hw0, hXTy, hXSmtTy⟩

theorem typed_bv_rotate_elim_term
    (k : BvRotateElimKind) (x amount : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateElimTerm k x amount) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvRotateElimTerm k x amount) := by
  intro hXTrans hTy
  rcases bv_rotate_elim_context k x amount hXTrans hTy with
    ⟨i, w, hAmount, hi0, _hw0, _hXType, hXSmtTy⟩
  subst amount
  have hRotTy :
      __smtx_typeof (__eo_to_smt
        (bvRotateElimLhs k x (Term.Numeral i))) =
        SmtType.BitVec (native_int_to_nat w) := by
    cases k with
    | left =>
        change __smtx_typeof
            (SmtTerm.rotate_left (SmtTerm.Numeral i) (__eo_to_smt x)) = _
        rw [typeof_rotate_left_eq]
        simp [__smtx_typeof_rotate_left, hXSmtTy, native_ite, hi0]
    | right =>
        change __smtx_typeof
            (SmtTerm.rotate_right (SmtTerm.Numeral i) (__eo_to_smt x)) = _
        rw [typeof_rotate_right_eq]
        simp [__smtx_typeof_rotate_right, hXSmtTy, native_ite, hi0]
  unfold bvRotateElimTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hRotTy.trans hXSmtTy.symm) (by rw [hRotTy]; simp)

private theorem native_int_to_nat_roundtrip
    (w : native_Int) (hw0 : native_zleq 0 w = true) :
    native_nat_to_int (native_int_to_nat w) = w := by
  have hw : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  simpa [Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
    native_nat_to_int, native_int_to_nat] using Int.toNat_of_nonneg hw

private theorem eval_bvsize_eq
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  have hRound := native_int_to_nat_roundtrip w hw0
  have hSize :
      __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)) = w := by
    rw [hXSmtTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0 (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  rw [hSize]
  simp [native_ite, hw0, __smtx_model_eval, __smtx_model_eval__at_purify]

private theorem model_eval_eq_true_of_eo_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem bv_rotate_elim_prem_mod_eq_zero
    (M : SmtModel) (x : Term) (i w : native_Int) :
    native_zleq 0 i = true ->
    native_zleq 0 w = true ->
    native_int_to_nat w ≠ 0 ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat w) ->
    eo_interprets M (bvRotateElimPrem x (Term.Numeral i)) true ->
    native_int_to_nat i % native_int_to_nat w = 0 := by
  intro hi0 hw0 hWNe hXSmtTy hPrem
  let modTerm :=
    Term.Apply (Term.Apply (Term.UOp UserOp.mod) (Term.Numeral i))
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)
  have hEq := model_eval_eq_true_of_eo_eq_true M modTerm (Term.Numeral 0)
    (by simpa [modTerm, bvRotateElimPrem] using hPrem)
  have hSizeEval := eval_bvsize_eq M x w hw0 hXSmtTy
  have hRound := native_int_to_nat_roundtrip w hw0
  have hwNe : w ≠ 0 := by
    intro hw
    subst w
    simp [native_int_to_nat, SmtEval.native_int_to_nat] at hWNe
  have hModEval :
      __smtx_model_eval M (__eo_to_smt modTerm) =
        SmtValue.Numeral (native_mod_total i w) := by
    change __smtx_model_eval M
        (SmtTerm.mod (SmtTerm.Numeral i)
          (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) = _
    rw [__smtx_model_eval.eq_27, hSizeEval]
    simp [__smtx_model_eval, __smtx_model_eval_eq, __smtx_model_eval_ite,
      __smtx_model_eval_mod_total, native_veq, hwNe]
  have hZeroEval :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) =
        SmtValue.Numeral 0 := by
    change __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0
    rw [__smtx_model_eval.eq_2]
  rw [hModEval, hZeroEval] at hEq
  have hModInt : i % w = 0 := by
    simpa [__smtx_model_eval_eq, native_veq, native_mod_total] using hEq
  have hi : (0 : Int) ≤ i := by
    simpa [SmtEval.native_zleq] using hi0
  have hw : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  have hToNat := Int.toNat_emod hi hw
  rw [hModInt] at hToNat
  simpa [native_int_to_nat, SmtEval.native_int_to_nat] using hToNat.symm

private theorem eval_bv_rotate_elim_lhs_eq
    (M : SmtModel) (hM : model_wf M)
    (k : BvRotateElimKind) (x amount : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateElimTerm k x amount) = Term.Bool ->
    eo_interprets M (bvRotateElimPrem x amount) true ->
    __smtx_model_eval M (__eo_to_smt (bvRotateElimLhs k x amount)) =
      __smtx_model_eval M (__eo_to_smt x) := by
  intro hXTrans hTy hPrem
  rcases bv_rotate_elim_context k x amount hXTrans hTy with
    ⟨i, w, hAmount, hi0, hw0, _hXType, hXSmtTy⟩
  subst amount
  let W := native_int_to_nat w
  let A := native_int_to_nat i
  have hXNonNone : term_has_non_none_type (__eo_to_smt x) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using
      hXTrans
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec W := by
    simpa [W, hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXNonNone
  rcases bitvec_value_canonical hEvalTy with ⟨p, hXEval⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary (↑W) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
  have hEvalTy' :
      __smtx_typeof_value (SmtValue.Binary (↑W) p) = SmtType.BitVec W := by
    simpa [hXEval'] using hEvalTy
  have hCanon :
      native_zeq p (native_mod_total p (native_int_pow2 (↑W))) = true :=
    bitvec_payload_canonical hEvalTy'
  have hRange := bitvec_payload_range_of_canonical
    (w := (↑W : Int)) (n := p)
    (by simp [SmtEval.native_zleq]) hCanon
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq] using hRange.2
  have hCycle : W = 0 ∨ A % W = 0 := by
    by_cases hW0 : W = 0
    · exact Or.inl hW0
    · exact Or.inr (bv_rotate_elim_prem_mod_eq_zero M x i w hi0 hw0
        (by simpa [W] using hW0) hXSmtTy
        (by simpa using hPrem))
  have hPayload :
      (↑(BitVec.ofInt W p).toNat : Int) = p := by
    rw [ofInt_toNat_canonical W p hp0 hp1, Int.toNat_of_nonneg hp0]
  cases k with
  | left =>
      change __smtx_model_eval M
          (SmtTerm.rotate_left (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_model_eval M (__eo_to_smt x)
      rw [__smtx_model_eval.eq_def] <;> simp only
      rw [__smtx_model_eval.eq_2, hXEval']
      change __smtx_rotate_left_rec A (SmtValue.Binary (↑W) p) =
        SmtValue.Binary (↑W) p
      rw [rotateLeftRec_eq A W p hp0 hp1]
      rw [rotateLeft_eq_self_of_width_zero_or_mod_eq_zero
        (BitVec.ofInt W p) A hCycle]
      congr 2
  | right =>
      change __smtx_model_eval M
          (SmtTerm.rotate_right (SmtTerm.Numeral i) (__eo_to_smt x)) =
        __smtx_model_eval M (__eo_to_smt x)
      rw [__smtx_model_eval.eq_def] <;> simp only
      rw [__smtx_model_eval.eq_2, hXEval']
      change __smtx_rotate_right_rec A (SmtValue.Binary (↑W) p) =
        SmtValue.Binary (↑W) p
      rw [rotateRightRec_eq A W p hp0 hp1]
      rw [rotateRightTracked_eq_self_of_width_zero_or_mod_eq_zero
        (BitVec.ofInt W p) A hCycle]
      congr 2

theorem facts_bv_rotate_elim_term
    (M : SmtModel) (hM : model_wf M)
    (k : BvRotateElimKind) (x amount : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateElimTerm k x amount) = Term.Bool ->
    eo_interprets M (bvRotateElimPrem x amount) true ->
    eo_interprets M (bvRotateElimTerm k x amount) true := by
  intro hXTrans hTy hPrem
  have hBool := typed_bv_rotate_elim_term k x amount hXTrans hTy
  unfold bvRotateElimTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvRotateElimTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvRotateElimLhs k x amount)))
      (__smtx_model_eval M (__eo_to_smt x))
    rw [eval_bv_rotate_elim_lhs_eq M hM k x amount hXTrans hTy hPrem]
    exact RuleProofs.smt_value_rel_refl _

theorem bv_rotate_left_elim_program_eq_term_of_ne_stuck (x amount : Term) :
    x ≠ Term.Stuck ->
    amount ≠ Term.Stuck ->
    __eo_prog_bv_rotate_left_eliminate_2 x amount
        (Proof.pf (bvRotateElimPrem x amount)) =
      bvRotateElimTerm .left x amount := by
  intro hX hAmount
  unfold bvRotateElimPrem
  rw [__eo_prog_bv_rotate_left_eliminate_2.eq_3 x amount amount x hX hAmount]
  simp [bvRotateElimPrem, bvRotateElimTerm, bvRotateElimLhs,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount]

theorem bv_rotate_right_elim_program_eq_term_of_ne_stuck (x amount : Term) :
    x ≠ Term.Stuck ->
    amount ≠ Term.Stuck ->
    __eo_prog_bv_rotate_right_eliminate_2 x amount
        (Proof.pf (bvRotateElimPrem x amount)) =
      bvRotateElimTerm .right x amount := by
  intro hX hAmount
  unfold bvRotateElimPrem
  rw [__eo_prog_bv_rotate_right_eliminate_2.eq_3 x amount amount x hX hAmount]
  simp [bvRotateElimPrem, bvRotateElimTerm, bvRotateElimLhs,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount]

theorem bv_rotate_left_elim_shape_of_ne_stuck (x amount P : Term) :
    __eo_prog_bv_rotate_left_eliminate_2 x amount (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ amount ≠ Term.Stuck ∧
      ∃ pa px, P = bvRotateElimPrem px pa := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_rotate_left_eliminate_2.eq_1 amount (Proof.pf P))
  have hAmountNe : amount ≠ Term.Stuck := by
    intro hAmount
    subst amount
    exact hProg
      (__eo_prog_bv_rotate_left_eliminate_2.eq_2 x (Proof.pf P) hXNe)
  refine ⟨hXNe, hAmountNe, ?_⟩
  by_cases hShape : ∃ pa px, P = bvRotateElimPrem px pa
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_rotate_left_eliminate_2.eq_4 x amount (Proof.pf P)
        hXNe hAmountNe (by
          intro pa px hP
          cases hP
          exact hShape ⟨pa, px, rfl⟩)))

theorem bv_rotate_right_elim_shape_of_ne_stuck (x amount P : Term) :
    __eo_prog_bv_rotate_right_eliminate_2 x amount (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ amount ≠ Term.Stuck ∧
      ∃ pa px, P = bvRotateElimPrem px pa := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_rotate_right_eliminate_2.eq_1 amount (Proof.pf P))
  have hAmountNe : amount ≠ Term.Stuck := by
    intro hAmount
    subst amount
    exact hProg
      (__eo_prog_bv_rotate_right_eliminate_2.eq_2 x (Proof.pf P) hXNe)
  refine ⟨hXNe, hAmountNe, ?_⟩
  by_cases hShape : ∃ pa px, P = bvRotateElimPrem px pa
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_rotate_right_eliminate_2.eq_4 x amount (Proof.pf P)
        hXNe hAmountNe (by
          intro pa px hP
          cases hP
          exact hShape ⟨pa, px, rfl⟩)))
