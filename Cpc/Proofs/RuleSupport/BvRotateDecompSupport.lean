module

public import Cpc.Proofs.RuleSupport.BvRotateElimSupport
import all Cpc.Proofs.RuleSupport.BvRotateElimSupport
public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport

public section

/-! Shared support for the nontrivial rotate-left/right decompositions. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvRotateModTerm (x amount : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.mod) amount)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)

def bvRotateWidthMinusOneTerm (x : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (Term.Apply (Term.UOp UserOp._at_bvsize) x)) (Term.Numeral 1)

def bvRotateLeftUpper1Value (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.plus) (bvRotateModTerm x amount))
        (Term.Numeral 0)))

def bvRotateLeftUpper1PremRaw
    (xSize xMod amount u1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u1)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize) xSize))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.plus)
            (bvRotateModTerm xMod amount))
          (Term.Numeral 0))))

def bvRotateLeftLowerValue (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x))
    (bvRotateModTerm x amount)

def bvRotateLeftLowerPremRaw
    (xSize xMod amount l1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) l1)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg)
        (Term.Apply (Term.UOp UserOp._at_bvsize) xSize))
      (bvRotateModTerm xMod amount))

def bvRotateRightUpper1Value (x amount : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (bvRotateModTerm x amount)) (Term.Numeral 1)

def bvRotateNonzeroPrem (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (bvRotateModTerm x amount)) (Term.Numeral 0)))
    (Term.Boolean false)

def bvRotateUpper2Prem (x u2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u2)
    (bvRotateWidthMinusOneTerm x)

def bvRotateLeftUpper1Prem (x amount u1 : Term) : Term :=
  bvRotateLeftUpper1PremRaw x x amount u1

def bvRotateLeftLowerPrem (x amount l1 : Term) : Term :=
  bvRotateLeftLowerPremRaw x x amount l1

def bvRotateRightUpper1Prem (x amount u1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u1)
    (bvRotateRightUpper1Value x amount)

def bvRotateRightLowerPrem (x amount l1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) l1)
    (bvRotateModTerm x amount)

def bvRotateDecompRhs (x u1 u2 l1 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x u1 (Term.Numeral 0)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvExtractTerm x u2 l1))
      (Term.Binary 0 0))

def bvRotateDecompTerm
    (k : BvRotateElimKind) (x amount u1 u2 l1 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq) (bvRotateElimLhs k x amount))
    (bvRotateDecompRhs x u1 u2 l1)

private theorem rotate_left_append_extract
    {x : BitVec W} {R : Nat} (hR : R < W) :
    ((x.extractLsb' 0 (W - R)) ++
        (x.extractLsb' (W - R) R)).cast (by omega) =
      x.rotateLeft R := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_cast, BitVec.getElem_append,
    BitVec.getElem_extractLsb']
  rw [BitVec.getElem_rotateLeft hi]
  simp only [Nat.mod_eq_of_lt hR]
  by_cases hiR : i < R
  · simp only [hiR, dif_pos]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
  · have hRi : R ≤ i := Nat.le_of_not_gt hiR
    simp only [hiR, dif_neg, if_false, Nat.zero_add]
    rw [BitVec.getLsbD_eq_getElem
      (Nat.lt_of_le_of_lt (Nat.sub_le i R) hi)]
    simp

private theorem rotate_right_append_extract
    {x : BitVec W} {R : Nat} (hR : R < W) :
    ((x.extractLsb' 0 R) ++
        (x.extractLsb' R (W - R))).cast (by omega) =
      x.rotateRight R := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_cast, BitVec.getElem_append,
    BitVec.getElem_extractLsb']
  rw [BitVec.getElem_rotateRight hi]
  simp only [Nat.mod_eq_of_lt hR]
  by_cases hLow : i < W - R
  · simp only [hLow, dif_pos]
    have hSplit : W - R + R = W := Nat.sub_add_cancel (Nat.le_of_lt hR)
    rw [BitVec.getLsbD_eq_getElem (by omega)]
  · have hHigh : W - R ≤ i := Nat.le_of_not_gt hLow
    simp only [hLow, dif_neg, if_false, Nat.zero_add]
    rw [BitVec.getLsbD_eq_getElem
      (Nat.lt_of_le_of_lt (Nat.sub_le i (W - R)) hi)]
    simp

private theorem concat_val_nat (w1 p1 w2 p2 : Nat) :
    __smtx_model_eval_concat (SmtValue.Binary ↑w1 ↑p1)
        (SmtValue.Binary ↑w2 ↑p2) =
      SmtValue.Binary ↑(w1 + w2)
        ↑((p1 * 2 ^ w2 + p2) % 2 ^ (w1 + w2)) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hw : (↑w1 + ↑w2 : Int) = ↑(w1 + w2) := by norm_cast
  rw [hw, _root_.natpow2_eq w2, _root_.natpow2_eq (w1 + w2),
    show ((2 : Int) ^ w2) = ((2 ^ w2 : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (w1 + w2)) = ((2 ^ (w1 + w2) : Nat) : Int) by
      norm_cast]
  norm_cast

private theorem concat_bitvec_values
    (x : BitVec A) (y : BitVec B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑B : Int) (↑y.toNat : Int)) =
      SmtValue.Binary (↑(A + B) : Int) (↑(x ++ y).toNat : Int) := by
  rw [concat_val_nat A x.toNat B y.toNat]
  congr 2
  have hyLt : y.toNat < 2 ^ B := y.isLt
  have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hyLt x.toNat
  have hFormula : x.toNat * 2 ^ B + y.toNat = (x ++ y).toNat := by
    rw [BitVec.toNat_append, ← hShiftOr, Nat.shiftLeft_eq]
  rw [hFormula, Nat.mod_eq_of_lt (x ++ y).isLt]

private theorem concat_empty_right_value (x : BitVec A) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑x.toNat : Int))
        (SmtValue.Binary 0 0) =
      SmtValue.Binary (↑A : Int) (↑x.toNat : Int) := by
  have h := concat_bitvec_values x (0#0)
  simpa using h

private theorem rotate_left_decomp_value
    (W R : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hR0 : 0 < R) (hR : R < W) :
    __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral (↑(W - R - 1) : Int))
          (SmtValue.Numeral 0) (SmtValue.Binary (↑W : Int) p))
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral (↑(W - 1) : Int))
            (SmtValue.Numeral (↑(W - R) : Int))
            (SmtValue.Binary (↑W : Int) p))
          (SmtValue.Binary 0 0)) =
      SmtValue.Binary (↑W : Int)
        (↑((BitVec.ofInt W p).rotateLeft R).toNat : Int) := by
  let X := BitVec.ofInt W p
  let low := X.extractLsb' 0 (W - R)
  let high := X.extractLsb' (W - R) R
  rw [extract_val_bitvec_start_len W 0 (W - R) p
      (↑(W - R - 1) : Int) 0 hp0 hp1 (by rfl) (by
        have h : W - R - 1 + 1 = W - R := by omega
        simpa using congrArg (fun n : Nat => (n : Int)) h)]
  rw [extract_val_bitvec_start_len W (W - R) R p
      (↑(W - 1) : Int) (↑(W - R) : Int) hp0 hp1 rfl (by omega)]
  change __smtx_model_eval_concat
      (SmtValue.Binary (↑(W - R) : Int) (↑low.toNat : Int))
      (__smtx_model_eval_concat
        (SmtValue.Binary (↑R : Int) (↑high.toNat : Int))
        (SmtValue.Binary 0 0)) = _
  rw [concat_empty_right_value high, concat_bitvec_values low high]
  have hWidth : W - R + R = W := Nat.sub_add_cancel (Nat.le_of_lt hR)
  have hWidthInt : (↑(W - R + R) : Int) = (↑W : Int) :=
    congrArg (fun n : Nat => (n : Int)) hWidth
  rw [hWidthInt]
  congr 2
  have hRotate := rotate_left_append_extract (x := X) hR
  simpa [X, low, high] using congrArg BitVec.toNat hRotate

private theorem rotate_right_eq_tracked
    {x : BitVec W} {R : Nat} (hR0 : 0 < R) (hR : R < W) :
    x.rotateRight R = x.rotateLeft (R * (W - 1)) := by
  have hSubPos : 0 < W - R := by omega
  have hSubLt : W - R < W := by omega
  have hRightLeft : x.rotateRight R = x.rotateLeft (W - R) := by
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [BitVec.getElem_rotateRight hi, BitVec.getElem_rotateLeft hi]
    simp only [Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hSubLt]
    have hCancel : W - (W - R) = R := Nat.sub_sub_self (Nat.le_of_lt hR)
    simp only [hCancel]
  have hMulEq :
      R * (W - 1) = (R - 1) * W + (W - R) := by
    calc
      R * (W - 1) = R * W - R := by
        rw [Nat.mul_sub_left_distrib]
        simp
      _ = ((R - 1) + 1) * W - R := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : R ≠ 0))]
      _ = (R - 1) * W + W - R := by rw [Nat.add_mul]; simp
      _ = (R - 1) * W + (W - R) := by omega
  have hMod : (R * (W - 1)) % W = W - R := by
    rw [hMulEq, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hSubLt]
  calc
    x.rotateRight R = x.rotateLeft (W - R) := hRightLeft
    _ = x.rotateLeft ((R * (W - 1)) % W) := by rw [hMod]
    _ = x.rotateLeft (R * (W - 1)) :=
      BitVec.rotateLeft_mod_eq_rotateLeft

private theorem rotate_right_decomp_value
    (W R : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hR0 : 0 < R) (hR : R < W) :
    __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral (↑(R - 1) : Int))
          (SmtValue.Numeral 0) (SmtValue.Binary (↑W : Int) p))
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral (↑(W - 1) : Int))
            (SmtValue.Numeral (↑R : Int))
            (SmtValue.Binary (↑W : Int) p))
          (SmtValue.Binary 0 0)) =
      SmtValue.Binary (↑W : Int)
        (↑((BitVec.ofInt W p).rotateLeft (R * (W - 1))).toNat : Int) := by
  let X := BitVec.ofInt W p
  let low := X.extractLsb' 0 R
  let high := X.extractLsb' R (W - R)
  rw [extract_val_bitvec_start_len W 0 R p (↑(R - 1) : Int) 0
      hp0 hp1 (by rfl) (by
        have h : R - 1 + 1 = R := by omega
        simpa using congrArg (fun n : Nat => (n : Int)) h)]
  rw [extract_val_bitvec_start_len W R (W - R) p
      (↑(W - 1) : Int) (↑R : Int) hp0 hp1 rfl (by omega)]
  change __smtx_model_eval_concat
      (SmtValue.Binary (↑R : Int) (↑low.toNat : Int))
      (__smtx_model_eval_concat
        (SmtValue.Binary (↑(W - R) : Int) (↑high.toNat : Int))
        (SmtValue.Binary 0 0)) = _
  rw [concat_empty_right_value high, concat_bitvec_values low high]
  have hWidth : R + (W - R) = W := Nat.add_sub_of_le (Nat.le_of_lt hR)
  have hWidthInt : (↑(R + (W - R)) : Int) = (↑W : Int) :=
    congrArg (fun n : Nat => (n : Int)) hWidth
  rw [hWidthInt]
  congr 2
  have hRotate := rotate_right_append_extract (x := X) hR
  have hTracked := rotate_right_eq_tracked (x := X) hR0 hR
  rw [hTracked] at hRotate
  simpa [X, low, high] using congrArg BitVec.toNat hRotate

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck
    {A B : Term} (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ wa wb,
      A = Term.Apply (Term.UOp UserOp.BitVec) wa ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) wb := by
  cases A <;> cases B <;> simp [__eo_typeof_concat] at h ⊢
  case Apply.Apply f a g b =>
    cases f <;> cases g <;> simp [__eo_typeof_concat] at h ⊢
    case UOp.UOp op op' =>
      cases op <;> cases op' <;> simp [__eo_typeof_concat] at h ⊢

private theorem rotate_lhs_type_eq_x_of_ne_stuck
    (k : BvRotateElimKind) (x amount : Term)
    (h : __eo_typeof (bvRotateElimLhs k x amount) ≠ Term.Stuck) :
    __eo_typeof (bvRotateElimLhs k x amount) = __eo_typeof x := by
  cases k <;>
    change __eo_typeof_rotate_left (__eo_typeof amount) amount
      (__eo_typeof x) ≠ Term.Stuck at h <;>
    change __eo_typeof_rotate_left (__eo_typeof amount) amount
      (__eo_typeof x) = __eo_typeof x
  all_goals
    unfold __eo_typeof_rotate_left at h ⊢
    split at h <;> simp_all
    have hGuard := support_eo_requires_cond_eq_of_non_stuck h
    simp [__eo_requires, hGuard, native_ite, native_teq, native_not]

theorem bv_rotate_decomp_context
    (k : BvRotateElimKind) (x amount u1 u2 l1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateDecompTerm k x amount u1 u2 l1) = Term.Bool ->
    ∃ i w a b c : native_Int,
      amount = Term.Numeral i ∧
      u1 = Term.Numeral a ∧ u2 = Term.Numeral b ∧
      l1 = Term.Numeral c ∧
      native_zleq 0 i = true ∧ native_zleq 0 w = true ∧
      native_zleq 0 c = true ∧
      native_zlt a w = true ∧ native_zlt b w = true ∧
      native_zlt 0 (native_zplus a 1) = true ∧
      native_zlt 0
        (native_zplus (native_zplus b 1) (native_zneg c)) = true ∧
      native_zplus (native_zplus a 1)
          (native_zplus (native_zplus b 1) (native_zneg c)) = w ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hTy
  change __eo_typeof_eq
      (__eo_typeof (bvRotateElimLhs k x amount))
      (__eo_typeof (bvRotateDecompRhs x u1 u2 l1)) = Term.Bool at hTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy with
    ⟨hLhsNe, hRhsNe⟩
  have hLhsEqX := rotate_lhs_type_eq_x_of_ne_stuck k x amount hLhsNe
  have hFakeTy : __eo_typeof (bvRotateElimTerm k x amount) = Term.Bool := by
    change __eo_typeof_eq
      (__eo_typeof (bvRotateElimLhs k x amount)) (__eo_typeof x) = Term.Bool
    rw [hLhsEqX]
    have hXNe : __eo_typeof x ≠ Term.Stuck := by
      rw [← hLhsEqX]
      exact hLhsNe
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, hXNe, native_ite,
      native_teq, native_not]
  rcases bv_rotate_elim_context k x amount hXTrans hFakeTy with
    ⟨i, w, hAmount, hi0, hw0, hXTy, hXSmtTy⟩
  have hRhsTy :
      __eo_typeof (bvRotateDecompRhs x u1 u2 l1) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
    have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hTy
    rw [hLhsEqX, hXTy] at hTypes
    exact hTypes.symm
  change __eo_typeof_concat
      (__eo_typeof (bvExtractTerm x u1 (Term.Numeral 0)))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x u2 l1)) (Term.Binary 0 0))) ≠
      Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck hRhsNe with
    ⟨wa, wb, hExt1Ty, hInnerTy⟩
  have hInnerNe :
      __eo_typeof_concat (__eo_typeof (bvExtractTerm x u2 l1))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    exact (show
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x u2 l1)) (Term.Binary 0 0)) ≠ Term.Stuck by
        rw [hInnerTy]
        intro h
        cases h)
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck hInnerNe with
    ⟨wc, wd, hExt2Ty, _hEmptyTy⟩
  have hExt1Ne : __eo_typeof (bvExtractTerm x u1 (Term.Numeral 0)) ≠
      Term.Stuck := by rw [hExt1Ty]; intro h; cases h
  have hExt2Ne : __eo_typeof (bvExtractTerm x u2 l1) ≠ Term.Stuck := by
    rw [hExt2Ty]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x u1 (Term.Numeral 0)
      hXTrans hExt1Ne with
    ⟨w1, a, z, hXTy1, hU1, hZero, _hw10, hz0, haw,
      hD10, _hXSmtTy1⟩
  have hw1 : w1 = w := by
    rw [hXTy] at hXTy1
    injection hXTy1 with _ hNum
    injection hNum with hWW
    exact hWW.symm
  subst w1
  have hz : z = 0 := by
    injection hZero with hZ
    exact hZ.symm
  subst z
  subst u1
  rcases bv_extract_context_of_non_stuck x u2 l1 hXTrans hExt2Ne with
    ⟨w2, b, c, hXTy2, hU2, hL1, _hw20, hc0, hbw, hD20,
      _hXSmtTy2⟩
  have hw2 : w2 = w := by
    rw [hXTy] at hXTy2
    injection hXTy2 with _ hNum
    injection hNum with hWW
    exact hWW.symm
  subst w2
  subst u2
  subst l1
  have hExt1Computed := eo_typeof_extract_of_context x w a 0 hXTy hz0 haw hD10
  have hExt2Computed := eo_typeof_extract_of_context x w b c hXTy hc0 hbw hD20
  have hExt1Computed' :
      __eo_typeof (bvExtractTerm x (Term.Numeral a) (Term.Numeral 0)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus a 1)) := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hExt1Computed
  have hInnerComputed :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x (Term.Numeral b) (Term.Numeral c)))
            (Term.Binary 0 0)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral
            (native_zplus (native_zplus b 1) (native_zneg c))) := by
    change __eo_typeof_concat
      (__eo_typeof (bvExtractTerm x (Term.Numeral b) (Term.Numeral c)))
      (__eo_typeof (Term.Binary 0 0)) = _
    rw [hExt2Computed]
    change __eo_typeof_concat
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral
          (native_zplus (native_zplus b 1) (native_zneg c))))
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) = _
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus]
  have hWidthEq :
      native_zplus (native_zplus a 1)
          (native_zplus (native_zplus b 1) (native_zneg c)) = w := by
    have hRhsTy' := hRhsTy
    unfold bvRotateDecompRhs at hRhsTy'
    change __eo_typeof_concat
      (__eo_typeof (bvExtractTerm x (Term.Numeral a) (Term.Numeral 0)))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x (Term.Numeral b) (Term.Numeral c)))
          (Term.Binary 0 0))) = _ at hRhsTy'
    rw [hExt1Computed', hInnerComputed] at hRhsTy'
    simp only [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus] at hRhsTy'
    change Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral
          (native_zplus (native_zplus a 1)
            (native_zplus (native_zplus b 1) (native_zneg c)))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at hRhsTy'
    injection hRhsTy' with _ hNum
    injection hNum
  have hD10' : native_zlt 0 (native_zplus a 1) = true := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hD10
  exact ⟨i, w, a, b, c, hAmount, rfl, rfl, rfl, hi0, hw0,
    hc0, haw, hbw, hD10', hD20, hWidthEq, hXTy, hXSmtTy⟩

theorem typed_bv_rotate_decomp_term
    (k : BvRotateElimKind) (x amount u1 u2 l1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateDecompTerm k x amount u1 u2 l1) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvRotateDecompTerm k x amount u1 u2 l1) := by
  intro hXTrans hTy
  rcases bv_rotate_decomp_context k x amount u1 u2 l1 hXTrans hTy with
    ⟨i, w, a, b, c, rfl, rfl, rfl, rfl, hi0, hw0, hc0, haw, hbw,
      hD10, hD20, hWidthEq, _hXTy, hXSmtTy⟩
  let d1 := native_zplus a 1
  let d2 := native_zplus (native_zplus b 1) (native_zneg c)
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
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
  have hZero0 : native_zleq 0 (0 : native_Int) = true := by native_decide
  have hExt1Ty :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral a) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat d1) := by
    simpa [d1, SmtEval.native_zplus, SmtEval.native_zneg] using
      (smt_typeof_extract_of_context x w a 0 hXSmtTy hw0 hZero0 haw
        (by
          change native_zlt 0 (a + 1 + -0) = true
          change native_zlt 0 (a + 1) = true at hD10
          simpa using hD10))
  have hExt2Ty :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral b) (Term.Numeral c))) =
        SmtType.BitVec (native_int_to_nat d2) := by
    exact smt_typeof_extract_of_context x w b c hXSmtTy hw0 hc0 hbw
      (by simpa [d2] using hD20)
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 := by
    rfl
  have hD2Round : native_nat_to_int (native_int_to_nat d2) = d2 :=
    _root_.native_int_to_nat_roundtrip d2
      (native_zleq_of_zlt_true _ _ (by simpa [d2] using hD20))
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.concat)
                (bvExtractTerm x (Term.Numeral b) (Term.Numeral c)))
              (Term.Binary 0 0))) =
        SmtType.BitVec (native_int_to_nat d2) := by
    change __smtx_typeof
      (SmtTerm.concat
        (__eo_to_smt
          (bvExtractTerm x (Term.Numeral b) (Term.Numeral c)))
        (__eo_to_smt (Term.Binary 0 0))) = _
    rw [typeof_concat_eq, hExt2Ty, hEmptyTy]
    simp only [__smtx_typeof_concat]
    rw [hD2Round]
    simp [SmtEval.native_zplus, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hd1 : (0 : Int) ≤ d1 := by
    simpa [d1, SmtEval.native_zleq] using
      native_zleq_of_zlt_true _ _ hD10
  have hd2 : (0 : Int) ≤ d2 := by
    simpa [d2, SmtEval.native_zleq] using
      native_zleq_of_zlt_true _ _ hD20
  have hw : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  have hD1Round : native_nat_to_int (native_int_to_nat d1) = d1 :=
    _root_.native_int_to_nat_roundtrip d1
      (native_zleq_of_zlt_true _ _ (by simpa [d1] using hD10))
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvRotateDecompRhs x (Term.Numeral a)
              (Term.Numeral b) (Term.Numeral c))) =
        SmtType.BitVec (native_int_to_nat w) := by
    unfold bvRotateDecompRhs
    change __smtx_typeof
      (SmtTerm.concat
        (__eo_to_smt
          (bvExtractTerm x (Term.Numeral a) (Term.Numeral 0)))
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.concat)
              (bvExtractTerm x (Term.Numeral b) (Term.Numeral c)))
            (Term.Binary 0 0)))) = _
    rw [typeof_concat_eq, hExt1Ty, hInnerTy]
    simp only [__smtx_typeof_concat]
    rw [hD1Round, hD2Round, show native_zplus d1 d2 = w by
      simpa [d1, d2] using hWidthEq]
  unfold bvRotateDecompTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)

private theorem smtx_eval_plus_term_eq_local
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.plus x y) =
      __smtx_model_eval_plus
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_neg_term_eq_local
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bvsize_rotate
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  have hRound := _root_.native_int_to_nat_roundtrip w hw0
  have hSize :
      __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)) = w := by
    rw [hXSmtTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  rw [hSize]
  simp [native_ite, hw0, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem smt_typeof_bvsize_rotate
    (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtType.Int := by
  change __smtx_typeof
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtType.Int
  rw [hXSmtTy]
  have hRound := _root_.native_int_to_nat_roundtrip w hw0
  change __smtx_typeof
      (native_ite
        (native_zleq 0 (native_nat_to_int (native_int_to_nat w)))
        (SmtTerm._at_purify
          (SmtTerm.Numeral (native_nat_to_int (native_int_to_nat w))))
        SmtTerm.None) = SmtType.Int
  rw [hRound]
  simp [native_ite, hw0, __smtx_typeof]

private theorem eval_rotate_mod_numeral
    (M : SmtModel) (hM : model_wf M)
    (x : Term) (i w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    ∃ r : native_Int,
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r := by
  have hSizeTy := smt_typeof_bvsize_rotate x w hw0 hXSmtTy
  have hModTy :
      __smtx_typeof
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtType.Int := by
    unfold bvRotateModTerm
    change __smtx_typeof
      (SmtTerm.mod (SmtTerm.Numeral i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) = _
    rw [typeof_mod_eq, hSizeTy]
    simp [native_ite, native_Teq, __smtx_typeof]
  have hNN :
      term_has_non_none_type
        (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) := by
    unfold term_has_non_none_type
    rw [hModTy]
    intro h
    cases h
  have hEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M
            (__eo_to_smt (bvRotateModTerm x (Term.Numeral i)))) =
        SmtType.Int := by
    simpa [hModTy] using
      smt_model_eval_preserves_type_of_non_none M hM
        (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) hNN
  rcases int_value_canonical hEvalTy with ⟨r, hEval⟩
  exact ⟨r, hEval⟩

private theorem eval_rotate_mod_term_of_width_ne_zero
    (M : SmtModel) (x : Term) (i w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hwNe : w ≠ 0)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
      SmtValue.Numeral (native_mod_total i w) := by
  unfold bvRotateModTerm
  change __smtx_model_eval M
      (SmtTerm.mod (SmtTerm.Numeral i)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))) = _
  rw [__smtx_model_eval.eq_27, eval_bvsize_rotate M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval_eq, __smtx_model_eval_ite,
    __smtx_model_eval_mod_total, native_veq, hwNe]

private theorem numeral_eq_of_interprets
    (M : SmtModel) (n v : native_Int) (t : Term)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral v) :
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Numeral n)) t)
      true ->
    n = v := by
  intro hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at hPrem
  cases hPrem with
  | intro_true _ hEq =>
      rw [smtx_eval_eq_term_eq, hEval] at hEq
      change __smtx_model_eval_eq (SmtValue.Numeral n)
        (SmtValue.Numeral v) = SmtValue.Boolean true at hEq
      simpa [__smtx_model_eval_eq, native_veq] using hEq

private theorem eval_rotate_width_minus_one
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M (__eo_to_smt (bvRotateWidthMinusOneTerm x)) =
      SmtValue.Numeral (native_zplus w (native_zneg 1)) := by
  unfold bvRotateWidthMinusOneTerm
  change __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (SmtTerm.Numeral 1)) = _
  rw [smtx_eval_neg_term_eq_local, eval_bvsize_rotate M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval__]

private theorem eval_rotate_left_upper1_value
    (M : SmtModel) (x : Term) (i w r : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w))
    (hModEval :
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvRotateLeftUpper1Value x (Term.Numeral i))) =
      SmtValue.Numeral
        (native_zplus w
          (native_zneg
            (native_zplus 1
              (native_zplus r 0)))) := by
  unfold bvRotateLeftUpper1Value
  change __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (SmtTerm.plus (SmtTerm.Numeral 1)
          (SmtTerm.plus
            (__eo_to_smt (bvRotateModTerm x (Term.Numeral i)))
            (SmtTerm.Numeral 0)))) = _
  rw [smtx_eval_neg_term_eq_local, eval_bvsize_rotate M x w hw0 hXSmtTy,
    smtx_eval_plus_term_eq_local, smtx_eval_plus_term_eq_local,
    hModEval]
  simp [__smtx_model_eval, __smtx_model_eval_plus, __smtx_model_eval__]

private theorem eval_rotate_left_lower_value
    (M : SmtModel) (x : Term) (i w r : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w))
    (hModEval :
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r) :
    __smtx_model_eval M
        (__eo_to_smt (bvRotateLeftLowerValue x (Term.Numeral i))) =
      SmtValue.Numeral
        (native_zplus w (native_zneg r)) := by
  unfold bvRotateLeftLowerValue
  change __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (__eo_to_smt (bvRotateModTerm x (Term.Numeral i)))) = _
  rw [smtx_eval_neg_term_eq_local, eval_bvsize_rotate M x w hw0 hXSmtTy,
    hModEval]
  simp [__smtx_model_eval__]

private theorem eval_rotate_right_upper1_value
    (M : SmtModel) (x : Term) (i w r : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w))
    (hModEval :
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvRotateRightUpper1Value x (Term.Numeral i))) =
      SmtValue.Numeral
        (native_zplus r (native_zneg 1)) := by
  unfold bvRotateRightUpper1Value
  change __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (bvRotateModTerm x (Term.Numeral i)))
        (SmtTerm.Numeral 1)) = _
  rw [smtx_eval_neg_term_eq_local,
    hModEval]
  simp [__smtx_model_eval, __smtx_model_eval__]

private theorem rotate_mod_ne_zero_of_nonzero_prem
    (M : SmtModel) (x : Term) (i r : native_Int)
    (hModEval :
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r) :
    eo_interprets M
        (bvRotateNonzeroPrem x (Term.Numeral i)) true ->
    r ≠ 0 := by
  intro hPrem hr
  subst r
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      unfold bvRotateNonzeroPrem at hEval
      change __smtx_model_eval M
          (SmtTerm.eq
            (SmtTerm.eq
              (__eo_to_smt (bvRotateModTerm x (Term.Numeral i)))
              (SmtTerm.Numeral 0))
            (SmtTerm.Boolean false)) = SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq, hModEval] at hEval
      simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq] at hEval

private theorem bv_rotate_left_indices_of_premises
    (M : SmtModel) (x : Term) (i w r a b c : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w))
    (hModEval :
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r) :
    eo_interprets M
        (bvRotateLeftUpper1Prem x (Term.Numeral i) (Term.Numeral a)) true ->
    eo_interprets M
        (bvRotateUpper2Prem x (Term.Numeral b)) true ->
    eo_interprets M
        (bvRotateLeftLowerPrem x (Term.Numeral i) (Term.Numeral c)) true ->
    a = native_zplus w
          (native_zneg (native_zplus 1 (native_zplus r 0))) ∧
      b = native_zplus w (native_zneg 1) ∧
      c = native_zplus w (native_zneg r) := by
  intro hA hB hC
  refine ⟨?_, ?_, ?_⟩
  · apply numeral_eq_of_interprets M a _ _
      (eval_rotate_left_upper1_value M x i w r hw0 hXSmtTy hModEval)
    simp only [bvRotateLeftUpper1Prem] at hA
    exact hA
  · apply numeral_eq_of_interprets M b _ _
      (eval_rotate_width_minus_one M x w hw0 hXSmtTy)
    simpa [bvRotateUpper2Prem] using hB
  · apply numeral_eq_of_interprets M c _ _
      (eval_rotate_left_lower_value M x i w r hw0 hXSmtTy hModEval)
    simp only [bvRotateLeftLowerPrem] at hC
    exact hC

private theorem bv_rotate_right_indices_of_premises
    (M : SmtModel) (x : Term) (i w r a b c : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w))
    (hModEval :
      __smtx_model_eval M
          (__eo_to_smt (bvRotateModTerm x (Term.Numeral i))) =
        SmtValue.Numeral r) :
    eo_interprets M
        (bvRotateRightUpper1Prem x (Term.Numeral i) (Term.Numeral a)) true ->
    eo_interprets M
        (bvRotateUpper2Prem x (Term.Numeral b)) true ->
    eo_interprets M
        (bvRotateRightLowerPrem x (Term.Numeral i) (Term.Numeral c)) true ->
    a = native_zplus r (native_zneg 1) ∧
      b = native_zplus w (native_zneg 1) ∧ c = r := by
  intro hA hB hC
  refine ⟨?_, ?_, ?_⟩
  · apply numeral_eq_of_interprets M a _ _
      (eval_rotate_right_upper1_value M x i w r hw0 hXSmtTy hModEval)
    simpa [bvRotateRightUpper1Prem] using hA
  · apply numeral_eq_of_interprets M b _ _
      (eval_rotate_width_minus_one M x w hw0 hXSmtTy)
    simpa [bvRotateUpper2Prem] using hB
  · apply numeral_eq_of_interprets M c r _ hModEval
    simpa [bvRotateRightLowerPrem] using hC

private theorem eval_concat_eo_term
    (M : SmtModel) (x y : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)) =
      __smtx_model_eval_concat
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  change __smtx_model_eval M
      (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_rotate_decomp
    (M : SmtModel) (hM : model_wf M)
    (k : BvRotateElimKind) (x amount u1 u2 l1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateDecompTerm k x amount u1 u2 l1) = Term.Bool ->
    eo_interprets M (bvRotateNonzeroPrem x amount) true ->
    (match k with
      | .left => eo_interprets M (bvRotateLeftUpper1Prem x amount u1) true
      | .right => eo_interprets M (bvRotateRightUpper1Prem x amount u1) true) ->
    eo_interprets M (bvRotateUpper2Prem x u2) true ->
    (match k with
      | .left => eo_interprets M (bvRotateLeftLowerPrem x amount l1) true
      | .right => eo_interprets M (bvRotateRightLowerPrem x amount l1) true) ->
    __smtx_model_eval M (__eo_to_smt (bvRotateElimLhs k x amount)) =
      __smtx_model_eval M (__eo_to_smt (bvRotateDecompRhs x u1 u2 l1)) := by
  intro hXTrans hTy hNonzero hUpper1 hUpper2 hLower
  rcases bv_rotate_decomp_context k x amount u1 u2 l1 hXTrans hTy with
    ⟨i, w, a, b, c, rfl, rfl, rfl, rfl, hi0, hw0, hc0, haw, hbw,
      hD10, hD20, _hWidthEq, _hXTy, hXSmtTy⟩
  rcases eval_rotate_mod_numeral M hM x i w hw0 hXSmtTy with
    ⟨r, hModEval⟩
  have hrNe := rotate_mod_ne_zero_of_nonzero_prem M x i r hModEval hNonzero
  have hi : (0 : Int) ≤ i := by
    simpa [SmtEval.native_zleq] using hi0
  have hw : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  have hc : (0 : Int) ≤ c := by
    simpa [SmtEval.native_zleq] using hc0
  have hawInt : a < w := by
    simpa [SmtEval.native_zlt] using haw
  have hbwInt : b < w := by
    simpa [SmtEval.native_zlt] using hbw
  cases k with
  | left =>
      rcases bv_rotate_left_indices_of_premises M x i w r a b c hw0
          hXSmtTy hModEval hUpper1 hUpper2 hLower with
        ⟨hA, hB, hC⟩
      have hAInt : a = w - (1 + (r + 0)) := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hA
        exact hA
      have hBInt : b = w - 1 := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hB
        exact hB
      have hCInt : c = w - r := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hC
        exact hC
      have hwNe : w ≠ 0 := by
        intro hwz
        have hrLe : r ≤ 0 := by
          have hC0 := hCInt
          rw [hwz] at hC0
          have hcr : c = -r := by simpa using hC0
          have hneg : 0 ≤ -r := by
            rw [← hcr]
            exact hc
          exact Int.nonpos_of_neg_nonneg hneg
        have hrGe : 0 ≤ r := by
          have hA0 := hAInt
          rw [hwz] at hA0
          have har : a = -(1 + r) := by simpa using hA0
          have hneg : -(1 + r) < 0 := by
            rw [← har, ← hwz]
            exact hawInt
          have hpos : 0 < 1 + r := Int.neg_lt_zero_iff.mp hneg
          have hpos' : 0 < r + 1 := by simpa [Int.add_comm] using hpos
          exact Int.lt_add_one_iff.mp hpos'
        exact hrNe (Int.le_antisymm hrLe hrGe)
      have hModStd := eval_rotate_mod_term_of_width_ne_zero M x i w hw0
        hwNe hXSmtTy
      rw [hModEval] at hModStd
      have hrMod : r = native_mod_total i w := by injection hModStd
      have hwPos : (0 : Int) < w := by
        rcases Int.lt_trichotomy w 0 with hlt | heq | hgt
        · exact False.elim (by omega)
        · exact False.elim (hwNe heq)
        · exact hgt
      have hr0 : (0 : Int) ≤ r := by
        rw [hrMod]
        exact Int.emod_nonneg i hwNe
      have hrw : r < w := by
        rw [hrMod]
        exact Int.emod_lt_of_pos i hwPos
      have hrPos : (0 : Int) < r := by
        rcases Int.lt_trichotomy r 0 with hlt | heq | hgt
        · exact False.elim (by omega)
        · exact False.elim (hrNe heq)
        · exact hgt
      let W := native_int_to_nat w
      let A := native_int_to_nat i
      let R := native_int_to_nat r
      have hWRound : (↑W : Int) = w := by
        simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
          _root_.native_int_to_nat_roundtrip w hw0
      have hR0Native : native_zleq 0 r = true := by
        simpa [SmtEval.native_zleq] using hr0
      have hRRound : (↑R : Int) = r := by
        simpa [R, native_nat_to_int, Smtm.native_nat_to_int] using
          _root_.native_int_to_nat_roundtrip r hR0Native
      have hR0 : 0 < R := by
        apply Int.ofNat_lt.mp
        change (0 : Int) < (R : Int)
        rw [hRRound]
        exact hrPos
      have hR : R < W := by
        apply Int.ofNat_lt.mp
        change (R : Int) < (W : Int)
        rw [hRRound, hWRound]
        exact hrw
      have hAmod : A % W = R := by
        have hToNat := Int.toNat_emod hi hw
        have hrMod' : r = i % w := by
          simpa [SmtEval.native_mod_total] using hrMod
        rw [← hrMod'] at hToNat
        simpa [A, W, R, native_int_to_nat,
          SmtEval.native_int_to_nat] using hToNat.symm
      have hWRCast : (↑(W - R) : Int) = (↑W : Int) - (↑R : Int) :=
        Int.ofNat_sub (Nat.le_of_lt hR)
      have hWRPredCast :
          (↑(W - R - 1) : Int) = (↑(W - R) : Int) - 1 :=
        Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.sub_pos_of_lt hR)))
      have hWPredCast : (↑(W - 1) : Int) = (↑W : Int) - 1 :=
        Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.lt_trans hR0 hR)))
      have haCast : a = (↑(W - R - 1) : Int) := by
        rw [hAInt, hWRPredCast, hWRCast, hWRound, hRRound]
        simp [Int.sub_sub, Int.add_comm]
      have hbCast : b = (↑(W - 1) : Int) := by
        rw [hBInt, hWPredCast, hWRound]
      have hcCast : c = (↑(W - R) : Int) := by
        rw [hCInt, hWRCast, hWRound, hRRound]
      rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
          (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
      have hXEval' :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Binary (↑W : Int) p := by
        simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
      have hRange := bitvec_payload_range_of_canonical
        (w := (↑W : Int)) (n := p) (by simp [SmtEval.native_zleq]) hCan
      have hp0 : (0 : Int) ≤ p := hRange.1
      have hp1 : p < (2 : Int) ^ W := by
        simpa [_root_.natpow2_eq] using hRange.2
      have hLhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (bvRotateElimLhs .left x (Term.Numeral i))) =
            SmtValue.Binary (↑W : Int)
              (↑((BitVec.ofInt W p).rotateLeft R).toNat : Int) := by
        unfold bvRotateElimLhs
        change __smtx_model_eval M
            (SmtTerm.rotate_left (SmtTerm.Numeral i) (__eo_to_smt x)) = _
        rw [__smtx_model_eval.eq_def] <;> simp only
        rw [__smtx_model_eval.eq_2, hXEval']
        change __smtx_rotate_left_rec A
            (SmtValue.Binary (↑W : Int) p) = _
        rw [bv_rotate_left_rec_eval A W p hp0 hp1]
        congr 2
        have hRot :
            (BitVec.ofInt W p).rotateLeft A =
              (BitVec.ofInt W p).rotateLeft R := by
          calc
            (BitVec.ofInt W p).rotateLeft A =
                (BitVec.ofInt W p).rotateLeft (A % W) :=
              BitVec.rotateLeft_mod_eq_rotateLeft.symm
            _ = (BitVec.ofInt W p).rotateLeft R := by rw [hAmod]
        exact congrArg BitVec.toNat hRot
      have hRhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (bvRotateDecompRhs x (Term.Numeral a)
                  (Term.Numeral b) (Term.Numeral c))) =
            SmtValue.Binary (↑W : Int)
              (↑((BitVec.ofInt W p).rotateLeft R).toNat : Int) := by
        unfold bvRotateDecompRhs
        rw [eval_concat_eo_term, eval_extract_term, eval_concat_eo_term,
          eval_extract_term, hXEval']
        change __smtx_model_eval_concat
            (__smtx_model_eval_extract (SmtValue.Numeral a)
              (SmtValue.Numeral 0) (SmtValue.Binary (↑W : Int) p))
            (__smtx_model_eval_concat
              (__smtx_model_eval_extract (SmtValue.Numeral b)
                (SmtValue.Numeral c) (SmtValue.Binary (↑W : Int) p))
              (SmtValue.Binary 0 0)) = _
        rw [haCast, hbCast, hcCast]
        exact rotate_left_decomp_value W R p hp0 hp1 hR0 hR
      rw [hLhsEval, hRhsEval]
  | right =>
      rcases bv_rotate_right_indices_of_premises M x i w r a b c hw0
          hXSmtTy hModEval hUpper1 hUpper2 hLower with
        ⟨hA, hB, hC⟩
      have hAInt : a = r - 1 := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hA
        exact hA
      have hBInt : b = w - 1 := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hB
        exact hB
      have hCInt : c = r := hC
      have hwNe : w ≠ 0 := by
        intro hwz
        have hrLe : r ≤ 0 := by
          have hra : r - 1 = a := hAInt.symm
          have hlt : r - 1 < 0 := by
            rw [hra, ← hwz]
            exact hawInt
          have hlt' : r < 0 + 1 := by
            have h := Int.add_lt_add_right hlt 1
            simpa using h
          exact Int.lt_add_one_iff.mp hlt'
        have hrGe : 0 ≤ r := by
          calc
            0 ≤ c := hc
            _ = r := hCInt
        exact hrNe (Int.le_antisymm hrLe hrGe)
      have hModStd := eval_rotate_mod_term_of_width_ne_zero M x i w hw0
        hwNe hXSmtTy
      rw [hModEval] at hModStd
      have hrMod : r = native_mod_total i w := by injection hModStd
      have hwPos : (0 : Int) < w := by
        rcases Int.lt_trichotomy w 0 with hlt | heq | hgt
        · exact False.elim (by omega)
        · exact False.elim (hwNe heq)
        · exact hgt
      have hr0 : (0 : Int) ≤ r := by
        rw [hrMod]
        exact Int.emod_nonneg i hwNe
      have hrw : r < w := by
        rw [hrMod]
        exact Int.emod_lt_of_pos i hwPos
      have hrPos : (0 : Int) < r := by
        rcases Int.lt_trichotomy r 0 with hlt | heq | hgt
        · exact False.elim (by omega)
        · exact False.elim (hrNe heq)
        · exact hgt
      let W := native_int_to_nat w
      let A := native_int_to_nat i
      let R := native_int_to_nat r
      have hWRound : (↑W : Int) = w := by
        simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
          _root_.native_int_to_nat_roundtrip w hw0
      have hR0Native : native_zleq 0 r = true := by
        simpa [SmtEval.native_zleq] using hr0
      have hRRound : (↑R : Int) = r := by
        simpa [R, native_nat_to_int, Smtm.native_nat_to_int] using
          _root_.native_int_to_nat_roundtrip r hR0Native
      have hR0 : 0 < R := by
        apply Int.ofNat_lt.mp
        change (0 : Int) < (R : Int)
        rw [hRRound]
        exact hrPos
      have hR : R < W := by
        apply Int.ofNat_lt.mp
        change (R : Int) < (W : Int)
        rw [hRRound, hWRound]
        exact hrw
      have hAmod : A % W = R := by
        have hToNat := Int.toNat_emod hi hw
        have hrMod' : r = i % w := by
          simpa [SmtEval.native_mod_total] using hrMod
        rw [← hrMod'] at hToNat
        simpa [A, W, R, native_int_to_nat,
          SmtEval.native_int_to_nat] using hToNat.symm
      have hRPredCast : (↑(R - 1) : Int) = (↑R : Int) - 1 :=
        Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hR0))
      have hWPredCast : (↑(W - 1) : Int) = (↑W : Int) - 1 :=
        Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.lt_trans hR0 hR)))
      have haCast : a = (↑(R - 1) : Int) := by
        rw [hAInt, hRPredCast, hRRound]
      have hbCast : b = (↑(W - 1) : Int) := by
        rw [hBInt, hWPredCast, hWRound]
      have hcCast : c = (↑R : Int) := by rw [hCInt, hRRound]
      rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
          (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
      have hXEval' :
          __smtx_model_eval M (__eo_to_smt x) =
            SmtValue.Binary (↑W : Int) p := by
        simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval
      have hRange := bitvec_payload_range_of_canonical
        (w := (↑W : Int)) (n := p) (by simp [SmtEval.native_zleq]) hCan
      have hp0 : (0 : Int) ≤ p := hRange.1
      have hp1 : p < (2 : Int) ^ W := by
        simpa [_root_.natpow2_eq] using hRange.2
      have hLhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (bvRotateElimLhs .right x (Term.Numeral i))) =
            SmtValue.Binary (↑W : Int)
              (↑((BitVec.ofInt W p).rotateLeft
                (R * (W - 1))).toNat : Int) := by
        unfold bvRotateElimLhs
        change __smtx_model_eval M
            (SmtTerm.rotate_right (SmtTerm.Numeral i) (__eo_to_smt x)) = _
        rw [__smtx_model_eval.eq_def] <;> simp only
        rw [__smtx_model_eval.eq_2, hXEval']
        change __smtx_rotate_right_rec A
            (SmtValue.Binary (↑W : Int) p) = _
        rw [bv_rotate_right_rec_eval A W p hp0 hp1]
        congr 2
        have hMulMod :
            (A * (W - 1)) % W = (R * (W - 1)) % W := by
          calc
            (A * (W - 1)) % W =
                ((A % W) * ((W - 1) % W)) % W := Nat.mul_mod A (W - 1) W
            _ = (R * ((W - 1) % W)) % W := by rw [hAmod]
            _ = (R * (W - 1)) % W := by
              simpa [Nat.mod_eq_of_lt hR] using
                (Nat.mul_mod R (W - 1) W).symm
        have hRot :
            (BitVec.ofInt W p).rotateLeft (A * (W - 1)) =
              (BitVec.ofInt W p).rotateLeft (R * (W - 1)) := by
          calc
            (BitVec.ofInt W p).rotateLeft (A * (W - 1)) =
                (BitVec.ofInt W p).rotateLeft ((A * (W - 1)) % W) :=
              BitVec.rotateLeft_mod_eq_rotateLeft.symm
            _ = (BitVec.ofInt W p).rotateLeft ((R * (W - 1)) % W) := by
              rw [hMulMod]
            _ = (BitVec.ofInt W p).rotateLeft (R * (W - 1)) :=
              BitVec.rotateLeft_mod_eq_rotateLeft
        exact congrArg BitVec.toNat hRot
      have hRhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (bvRotateDecompRhs x (Term.Numeral a)
                  (Term.Numeral b) (Term.Numeral c))) =
            SmtValue.Binary (↑W : Int)
              (↑((BitVec.ofInt W p).rotateLeft
                (R * (W - 1))).toNat : Int) := by
        unfold bvRotateDecompRhs
        rw [eval_concat_eo_term, eval_extract_term, eval_concat_eo_term,
          eval_extract_term, hXEval']
        change __smtx_model_eval_concat
            (__smtx_model_eval_extract (SmtValue.Numeral a)
              (SmtValue.Numeral 0) (SmtValue.Binary (↑W : Int) p))
            (__smtx_model_eval_concat
              (__smtx_model_eval_extract (SmtValue.Numeral b)
                (SmtValue.Numeral c) (SmtValue.Binary (↑W : Int) p))
              (SmtValue.Binary 0 0)) = _
        rw [haCast, hbCast, hcCast]
        exact rotate_right_decomp_value W R p hp0 hp1 hR0 hR
      rw [hLhsEval, hRhsEval]

theorem facts_bv_rotate_decomp_term
    (M : SmtModel) (hM : model_wf M)
    (k : BvRotateElimKind) (x amount u1 u2 l1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvRotateDecompTerm k x amount u1 u2 l1) = Term.Bool ->
    eo_interprets M (bvRotateNonzeroPrem x amount) true ->
    (match k with
      | .left => eo_interprets M (bvRotateLeftUpper1Prem x amount u1) true
      | .right => eo_interprets M (bvRotateRightUpper1Prem x amount u1) true) ->
    eo_interprets M (bvRotateUpper2Prem x u2) true ->
    (match k with
      | .left => eo_interprets M (bvRotateLeftLowerPrem x amount l1) true
      | .right => eo_interprets M (bvRotateRightLowerPrem x amount l1) true) ->
    eo_interprets M (bvRotateDecompTerm k x amount u1 u2 l1) true := by
  intro hXTrans hTy hNonzero hUpper1 hUpper2 hLower
  have hBool := typed_bv_rotate_decomp_term k x amount u1 u2 l1 hXTrans hTy
  unfold bvRotateDecompTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvRotateDecompTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvRotateElimLhs k x amount)))
      (__smtx_model_eval M (__eo_to_smt (bvRotateDecompRhs x u1 u2 l1)))
    rw [eval_bv_rotate_decomp M hM k x amount u1 u2 l1 hXTrans hTy
      hNonzero hUpper1 hUpper2 hLower]
    exact RuleProofs.smt_value_rel_refl _

def bvRotateLeftDecompProgram (x amount u1 u2 l1 : Term) : Term :=
  __eo_prog_bv_rotate_left_eliminate_1 x amount u1 u2 l1
    (Proof.pf (bvRotateNonzeroPrem x amount))
    (Proof.pf (bvRotateLeftUpper1Prem x amount u1))
    (Proof.pf (bvRotateUpper2Prem x u2))
    (Proof.pf (bvRotateLeftLowerPrem x amount l1))

def bvRotateRightDecompProgram (x amount u1 u2 l1 : Term) : Term :=
  __eo_prog_bv_rotate_right_eliminate_1 x amount u1 u2 l1
    (Proof.pf (bvRotateNonzeroPrem x amount))
    (Proof.pf (bvRotateRightUpper1Prem x amount u1))
    (Proof.pf (bvRotateUpper2Prem x u2))
    (Proof.pf (bvRotateRightLowerPrem x amount l1))

theorem bv_rotate_left_decomp_program_eq_term_of_ne_stuck
    (x amount u1 u2 l1 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> u1 ≠ Term.Stuck ->
    u2 ≠ Term.Stuck -> l1 ≠ Term.Stuck ->
    bvRotateLeftDecompProgram x amount u1 u2 l1 =
      bvRotateDecompTerm .left x amount u1 u2 l1 := by
  intro hX hAmount hU1 hU2 hL1
  unfold bvRotateLeftDecompProgram bvRotateNonzeroPrem
    bvRotateLeftUpper1Prem bvRotateUpper2Prem bvRotateLeftLowerPrem
    bvRotateLeftUpper1PremRaw bvRotateLeftLowerPremRaw
    bvRotateWidthMinusOneTerm bvRotateModTerm
  rw [__eo_prog_bv_rotate_left_eliminate_1.eq_6
    x amount u1 u2 l1 amount x u1 x amount x u2 x l1 x amount x
    hX hAmount hU1 hU2 hL1]
  simp [bvRotateDecompTerm, bvRotateDecompRhs, bvRotateElimLhs,
    bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hU1, hU2, hL1]

theorem bv_rotate_right_decomp_program_eq_term_of_ne_stuck
    (x amount u1 u2 l1 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> u1 ≠ Term.Stuck ->
    u2 ≠ Term.Stuck -> l1 ≠ Term.Stuck ->
    bvRotateRightDecompProgram x amount u1 u2 l1 =
      bvRotateDecompTerm .right x amount u1 u2 l1 := by
  intro hX hAmount hU1 hU2 hL1
  unfold bvRotateRightDecompProgram bvRotateNonzeroPrem
    bvRotateRightUpper1Prem bvRotateUpper2Prem bvRotateRightLowerPrem
    bvRotateRightUpper1Value bvRotateWidthMinusOneTerm bvRotateModTerm
  rw [__eo_prog_bv_rotate_right_eliminate_1.eq_6
    x amount u1 u2 l1 amount x u1 amount x u2 x l1 amount x
    hX hAmount hU1 hU2 hL1]
  simp [bvRotateDecompTerm, bvRotateDecompRhs, bvRotateElimLhs,
    bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hU1, hU2, hL1]

theorem bv_rotate_left_decomp_shape_of_ne_stuck
    (x amount u1 u2 l1 P1 P2 P3 P4 : Term) :
    __eo_prog_bv_rotate_left_eliminate_1 x amount u1 u2 l1
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) ≠
      Term.Stuck ->
    x ≠ Term.Stuck ∧ amount ≠ Term.Stuck ∧ u1 ≠ Term.Stuck ∧
      u2 ≠ Term.Stuck ∧ l1 ≠ Term.Stuck ∧
      ∃ pa1 px1 pu1 px2 pa2 px3 pu2 px4 pl1 px5 pa3 px6,
        P1 = bvRotateNonzeroPrem px1 pa1 ∧
        P2 = bvRotateLeftUpper1PremRaw px2 px3 pa2 pu1 ∧
        P3 = bvRotateUpper2Prem px4 pu2 ∧
        P4 = bvRotateLeftLowerPremRaw px5 px6 pa3 pl1 := by
  intro hProg
  have hX : x ≠ Term.Stuck := by
    intro h
    subst x
    exact hProg (__eo_prog_bv_rotate_left_eliminate_1.eq_1 amount u1 u2 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4))
  have hAmount : amount ≠ Term.Stuck := by
    intro h
    subst amount
    exact hProg (__eo_prog_bv_rotate_left_eliminate_1.eq_2 x u1 u2 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) hX)
  have hU1 : u1 ≠ Term.Stuck := by
    intro h
    subst u1
    exact hProg (__eo_prog_bv_rotate_left_eliminate_1.eq_3 x amount u2 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) hX hAmount)
  have hU2 : u2 ≠ Term.Stuck := by
    intro h
    subst u2
    exact hProg (__eo_prog_bv_rotate_left_eliminate_1.eq_4 x amount u1 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
      hX hAmount hU1)
  have hL1 : l1 ≠ Term.Stuck := by
    intro h
    subst l1
    exact hProg (__eo_prog_bv_rotate_left_eliminate_1.eq_5 x amount u1 u2
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
      hX hAmount hU1 hU2)
  refine ⟨hX, hAmount, hU1, hU2, hL1, ?_⟩
  by_cases hShape :
      ∃ pa1 px1 pu1 px2 pa2 px3 pu2 px4 pl1 px5 pa3 px6,
        P1 = bvRotateNonzeroPrem px1 pa1 ∧
        P2 = bvRotateLeftUpper1PremRaw px2 px3 pa2 pu1 ∧
        P3 = bvRotateUpper2Prem px4 pu2 ∧
        P4 = bvRotateLeftLowerPremRaw px5 px6 pa3 pl1
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_rotate_left_eliminate_1.eq_7 x amount u1 u2 l1
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
        hX hAmount hU1 hU2 hL1 (by
          intro pa1 px1 pu1 px2 pa2 px3 pu2 px4 pl1 px5 pa3 px6
            hP1 hP2 hP3 hP4
          cases hP1
          cases hP2
          cases hP3
          cases hP4
          exact hShape ⟨pa1, px1, pu1, px2, pa2, px3, pu2, px4,
            pl1, px5, pa3, px6, rfl, rfl, rfl, rfl⟩)))

theorem bv_rotate_right_decomp_shape_of_ne_stuck
    (x amount u1 u2 l1 P1 P2 P3 P4 : Term) :
    __eo_prog_bv_rotate_right_eliminate_1 x amount u1 u2 l1
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) ≠
      Term.Stuck ->
    x ≠ Term.Stuck ∧ amount ≠ Term.Stuck ∧ u1 ≠ Term.Stuck ∧
      u2 ≠ Term.Stuck ∧ l1 ≠ Term.Stuck ∧
      ∃ pa1 px1 pu1 pa2 px2 pu2 px3 pl1 pa3 px4,
        P1 = bvRotateNonzeroPrem px1 pa1 ∧
        P2 = bvRotateRightUpper1Prem px2 pa2 pu1 ∧
        P3 = bvRotateUpper2Prem px3 pu2 ∧
        P4 = bvRotateRightLowerPrem px4 pa3 pl1 := by
  intro hProg
  have hX : x ≠ Term.Stuck := by
    intro h
    subst x
    exact hProg (__eo_prog_bv_rotate_right_eliminate_1.eq_1 amount u1 u2 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4))
  have hAmount : amount ≠ Term.Stuck := by
    intro h
    subst amount
    exact hProg (__eo_prog_bv_rotate_right_eliminate_1.eq_2 x u1 u2 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) hX)
  have hU1 : u1 ≠ Term.Stuck := by
    intro h
    subst u1
    exact hProg (__eo_prog_bv_rotate_right_eliminate_1.eq_3 x amount u2 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4) hX hAmount)
  have hU2 : u2 ≠ Term.Stuck := by
    intro h
    subst u2
    exact hProg (__eo_prog_bv_rotate_right_eliminate_1.eq_4 x amount u1 l1
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
      hX hAmount hU1)
  have hL1 : l1 ≠ Term.Stuck := by
    intro h
    subst l1
    exact hProg (__eo_prog_bv_rotate_right_eliminate_1.eq_5 x amount u1 u2
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
      hX hAmount hU1 hU2)
  refine ⟨hX, hAmount, hU1, hU2, hL1, ?_⟩
  by_cases hShape :
      ∃ pa1 px1 pu1 pa2 px2 pu2 px3 pl1 pa3 px4,
        P1 = bvRotateNonzeroPrem px1 pa1 ∧
        P2 = bvRotateRightUpper1Prem px2 pa2 pu1 ∧
        P3 = bvRotateUpper2Prem px3 pu2 ∧
        P4 = bvRotateRightLowerPrem px4 pa3 pl1
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_rotate_right_eliminate_1.eq_7 x amount u1 u2 l1
        (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
        hX hAmount hU1 hU2 hL1 (by
          intro pa1 px1 pu1 pa2 px2 pu2 px3 pl1 pa3 px4
            hP1 hP2 hP3 hP4
          cases hP1
          cases hP2
          cases hP3
          cases hP4
          exact hShape ⟨pa1, px1, pu1, pa2, px2, pu2, px3, pl1,
            pa3, px4, rfl, rfl, rfl, rfl⟩)))

private theorem rotate_eo_and_eq_true_args (a b : Term) :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_ite, native_teq,
      native_not, SmtEval.native_not, native_and, SmtEval.native_and]
      at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

def bvRotateLeftDecompGuard
    (x amount u1 u2 l1 pa1 px1 pu1 px2 pa2 px3 pu2 px4 pl1 px5 pa3 px6 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and
                      (__eo_and (__eo_eq amount pa1) (__eo_eq x px1))
                      (__eo_eq u1 pu1))
                    (__eo_eq x px2))
                  (__eo_eq amount pa2))
                (__eo_eq x px3))
              (__eo_eq u2 pu2))
            (__eo_eq x px4))
          (__eo_eq l1 pl1))
        (__eo_eq x px5))
      (__eo_eq amount pa3))
    (__eo_eq x px6)

def bvRotateRightDecompGuard
    (x amount u1 u2 l1 pa1 px1 pu1 pa2 px2 pu2 px3 pl1 pa3 px4 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and (__eo_eq amount pa1) (__eo_eq x px1))
                  (__eo_eq u1 pu1))
                (__eo_eq amount pa2))
              (__eo_eq x px2))
            (__eo_eq u2 pu2))
          (__eo_eq x px3))
        (__eo_eq l1 pl1))
      (__eo_eq amount pa3))
    (__eo_eq x px4)

theorem bv_rotate_left_decomp_guard_eqs
    (x amount u1 u2 l1 pa1 px1 pu1 px2 pa2 px3 pu2 px4 pl1 px5 pa3 px6 body : Term) :
    __eo_requires
        (bvRotateLeftDecompGuard x amount u1 u2 l1 pa1 px1 pu1 px2
          pa2 px3 pu2 px4 pl1 px5 pa3 px6)
        (Term.Boolean true) body ≠ Term.Stuck ->
    pa1 = amount ∧ px1 = x ∧ pu1 = u1 ∧ px2 = x ∧
      pa2 = amount ∧ px3 = x ∧ pu2 = u2 ∧ px4 = x ∧
      pl1 = l1 ∧ px5 = x ∧ pa3 = amount ∧ px6 = x := by
  intro hReq
  have hGuard :
      bvRotateLeftDecompGuard x amount u1 u2 l1 pa1 px1 pu1 px2
          pa2 px3 pu2 px4 pl1 px5 pa3 px6 = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvRotateLeftDecompGuard at hGuard
  rcases rotate_eo_and_eq_true_args _ _ hGuard with ⟨h11, h12⟩
  rcases rotate_eo_and_eq_true_args _ _ h11 with ⟨h10, h11'⟩
  rcases rotate_eo_and_eq_true_args _ _ h10 with ⟨h9, h10'⟩
  rcases rotate_eo_and_eq_true_args _ _ h9 with ⟨h8, h9'⟩
  rcases rotate_eo_and_eq_true_args _ _ h8 with ⟨h7, h8'⟩
  rcases rotate_eo_and_eq_true_args _ _ h7 with ⟨h6, h7'⟩
  rcases rotate_eo_and_eq_true_args _ _ h6 with ⟨h5, h6'⟩
  rcases rotate_eo_and_eq_true_args _ _ h5 with ⟨h4, h5'⟩
  rcases rotate_eo_and_eq_true_args _ _ h4 with ⟨h3, h4'⟩
  rcases rotate_eo_and_eq_true_args _ _ h3 with ⟨h2, h3'⟩
  rcases rotate_eo_and_eq_true_args _ _ h2 with ⟨h1a, h1b⟩
  exact ⟨support_eq_of_eo_eq_true amount pa1 h1a,
    support_eq_of_eo_eq_true x px1 h1b,
    support_eq_of_eo_eq_true u1 pu1 h3',
    support_eq_of_eo_eq_true x px2 h4',
    support_eq_of_eo_eq_true amount pa2 h5',
    support_eq_of_eo_eq_true x px3 h6',
    support_eq_of_eo_eq_true u2 pu2 h7',
    support_eq_of_eo_eq_true x px4 h8',
    support_eq_of_eo_eq_true l1 pl1 h9',
    support_eq_of_eo_eq_true x px5 h10',
    support_eq_of_eo_eq_true amount pa3 h11',
    support_eq_of_eo_eq_true x px6 h12⟩

theorem bv_rotate_right_decomp_guard_eqs
    (x amount u1 u2 l1 pa1 px1 pu1 pa2 px2 pu2 px3 pl1 pa3 px4 body : Term) :
    __eo_requires
        (bvRotateRightDecompGuard x amount u1 u2 l1 pa1 px1 pu1 pa2
          px2 pu2 px3 pl1 pa3 px4)
        (Term.Boolean true) body ≠ Term.Stuck ->
    pa1 = amount ∧ px1 = x ∧ pu1 = u1 ∧ pa2 = amount ∧
      px2 = x ∧ pu2 = u2 ∧ px3 = x ∧ pl1 = l1 ∧
      pa3 = amount ∧ px4 = x := by
  intro hReq
  have hGuard :
      bvRotateRightDecompGuard x amount u1 u2 l1 pa1 px1 pu1 pa2
          px2 pu2 px3 pl1 pa3 px4 = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvRotateRightDecompGuard at hGuard
  rcases rotate_eo_and_eq_true_args _ _ hGuard with ⟨h9, h10⟩
  rcases rotate_eo_and_eq_true_args _ _ h9 with ⟨h8, h9'⟩
  rcases rotate_eo_and_eq_true_args _ _ h8 with ⟨h7, h8'⟩
  rcases rotate_eo_and_eq_true_args _ _ h7 with ⟨h6, h7'⟩
  rcases rotate_eo_and_eq_true_args _ _ h6 with ⟨h5, h6'⟩
  rcases rotate_eo_and_eq_true_args _ _ h5 with ⟨h4, h5'⟩
  rcases rotate_eo_and_eq_true_args _ _ h4 with ⟨h3, h4'⟩
  rcases rotate_eo_and_eq_true_args _ _ h3 with ⟨h2, h3'⟩
  rcases rotate_eo_and_eq_true_args _ _ h2 with ⟨h1a, h1b⟩
  exact ⟨support_eq_of_eo_eq_true amount pa1 h1a,
    support_eq_of_eo_eq_true x px1 h1b,
    support_eq_of_eo_eq_true u1 pu1 h3',
    support_eq_of_eo_eq_true amount pa2 h4',
    support_eq_of_eo_eq_true x px2 h5',
    support_eq_of_eo_eq_true u2 pu2 h6',
    support_eq_of_eo_eq_true x px3 h7',
    support_eq_of_eo_eq_true l1 pl1 h8',
    support_eq_of_eo_eq_true amount pa3 h9',
    support_eq_of_eo_eq_true x px4 h10⟩
