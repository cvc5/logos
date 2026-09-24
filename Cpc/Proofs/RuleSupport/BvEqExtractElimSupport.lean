module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport

public section

/-! Shared support for reconstructing a bitvector around an extracted slice. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvEqExtractElim2Slice (x j : Term) : Term :=
  bvExtractTerm x j (Term.Numeral 0)

def bvEqExtractElim2LeftEq (x y j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvEqExtractElim2Slice x j)) y

def bvEqExtractElim2High (x wm jp : Term) : Term :=
  bvExtractTerm x wm jp

def bvEqExtractElim2Rebuild (x y wm jp : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (bvEqExtractElim2High x wm jp))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
      (Term.Binary 0 0))

def bvEqExtractElim2RightEq (x y wm jp : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
    (bvEqExtractElim2Rebuild x y wm jp)

def bvEqExtractElim2Term (x y j wm jp : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvEqExtractElim2LeftEq x y j))
    (bvEqExtractElim2RightEq x y wm jp)

def bvEqExtractElimWidthMinusOnePrem (x wm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) wm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)) (Term.Numeral 1))

def bvEqExtractElimSuccessorPrem (j jp : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) jp)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) j)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0)))

def bvEqExtractElimHighRoomPrem (wm j : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) wm) j))
    (Term.Boolean true)

private theorem eo_typeof_eq_bool_of_ne_stuck_bv_extract
    (A B : Term) (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not] at h |-
  all_goals assumption

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract
    {A B : Term} (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ wa wb,
      A = Term.Apply (Term.UOp UserOp.BitVec) wa ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) wb := by
  cases A <;> cases B <;> simp [__eo_typeof_concat] at h |-
  case Apply.Apply f a g b =>
    cases f <;> cases g <;> simp [__eo_typeof_concat] at h |-
    case UOp.UOp op op' =>
      cases op <;> cases op' <;> simp [__eo_typeof_concat] at h |-

private theorem smt_typeof_concat_bitvec_extract
    (a b : Term) (wa wb : native_Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec wb ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b)) =
      SmtType.BitVec
        (native_int_to_nat
          (native_zplus (native_nat_to_int wa) (native_nat_to_int wb))) := by
  intro hA hB
  change __smtx_typeof (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [typeof_concat_eq]
  simp [__smtx_typeof_concat, hA, hB]

private theorem bv_eq_extract_elim2_inner_types
    (x y j wm jp : Term) :
    __eo_typeof (bvEqExtractElim2Term x y j wm jp) = Term.Bool ->
    __eo_typeof (bvEqExtractElim2LeftEq x y j) = Term.Bool ∧
      __eo_typeof (bvEqExtractElim2RightEq x y wm jp) = Term.Bool := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof (bvEqExtractElim2LeftEq x y j))
      (__eo_typeof (bvEqExtractElim2RightEq x y wm jp)) = Term.Bool at hTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy with
    ⟨hLeft, hRight⟩
  constructor
  . change __eo_typeof_eq
      (__eo_typeof (bvEqExtractElim2Slice x j)) (__eo_typeof y) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck_bv_extract
    exact hLeft
  . change __eo_typeof_eq (__eo_typeof x)
      (__eo_typeof (bvEqExtractElim2Rebuild x y wm jp)) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck_bv_extract
    exact hRight

private theorem bv_eq_extract_elim2_smt_context
    (x y j wm jp : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim2Term x y j wm jp) = Term.Bool ->
    ∃ w jv hwidth hv lv,
      j = Term.Numeral jv ∧ wm = Term.Numeral hv ∧
      jp = Term.Numeral lv ∧
      native_zleq 0 w = true ∧
      native_zlt 0 (native_zplus jv 1) = true ∧
      native_zlt jv w = true ∧
      native_zleq 0 hwidth = true ∧ native_zleq 0 lv = true ∧
      native_zlt hv w = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat (native_zplus jv 1)) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim2High x wm jp)) =
        SmtType.BitVec (native_int_to_nat hwidth) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim2Rebuild x y wm jp)) =
        __smtx_typeof (__eo_to_smt x) := by
  intro hXTrans hYTrans hTy
  rcases bv_eq_extract_elim2_inner_types x y j wm jp hTy with
    ⟨hLeftTy, hRightTy⟩
  have hLeftOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftTy
  have hSliceNe : __eo_typeof (bvEqExtractElim2Slice x j) ≠ Term.Stuck :=
    hLeftOps.1
  rcases bv_extract_context_of_non_stuck x j (Term.Numeral 0)
      hXTrans hSliceNe with
    ⟨w, jv, lowv, hXTy, hJ, hLow, hw0, hLow0, hjw, hD0, hXSmtTy⟩
  have hLowEq : lowv = 0 := by
    simpa using congrArg (fun t => match t with
      | Term.Numeral n => n
      | _ => 0) hLow.symm
  subst lowv
  have hD :
      native_zplus (native_zplus jv 1) (native_zneg 0) =
        native_zplus jv 1 := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg]
  have hD0Simple : native_zlt 0 (native_zplus jv 1) = true := by
    rw [← hD]
    exact hD0
  have hSliceSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim2Slice x j)) =
        SmtType.BitVec (native_int_to_nat (native_zplus jv 1)) := by
    rw [hJ]
    simpa [bvEqExtractElim2Slice, hD] using
      (smt_typeof_extract_of_context x w jv 0 hXSmtTy hw0 hLow0 hjw hD0)
  have hSliceTrans :
      RuleProofs.eo_has_smt_translation (bvEqExtractElim2Slice x j) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSliceSmtTy]
    intro h
    cases h
  have hLeftEoEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftTy
  have hSliceBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvEqExtractElim2Slice x j)
      (__eo_typeof (bvEqExtractElim2Slice x j))
      (__eo_to_smt (bvEqExtractElim2Slice x j)) rfl hSliceTrans rfl
  have hYBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y (__eo_typeof y) (__eo_to_smt y) rfl hYTrans rfl
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat (native_zplus jv 1)) := by
    rw [hYBridge, ← hLeftEoEq, ← hSliceBridge]
    exact hSliceSmtTy
  have hRightOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightTy
  have hRebuildNe :
      __eo_typeof (bvEqExtractElim2Rebuild x y wm jp) ≠ Term.Stuck :=
    hRightOps.2
  have hOuterConcatNe :
      __eo_typeof_concat
          (__eo_typeof (bvEqExtractElim2High x wm jp))
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
              (Term.Binary 0 0))) ≠ Term.Stuck := by
    exact hRebuildNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract hOuterConcatNe with
    ⟨highWidthTerm, innerWidthTerm, hHighEo, _hInnerEo⟩
  have hHighNe :
      __eo_typeof (bvEqExtractElim2High x wm jp) ≠ Term.Stuck := by
    rw [hHighEo]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x wm jp hXTrans hHighNe with
    ⟨wHigh, hv, lv, _hXTyHigh, hWm, hJp, hwHigh0, hlv0, hhvw,
      hHighWidth0, hXSmtTyHigh⟩
  have hWidthNat : native_int_to_nat w = native_int_to_nat wHigh := by
    rw [hXSmtTy] at hXSmtTyHigh
    simpa using hXSmtTyHigh
  have hwHighEq : wHigh = w :=
    nonneg_int_eq_of_toNat_eq wHigh w hwHigh0 hw0 hWidthNat.symm
  rw [hwHighEq] at hhvw
  let highWidth := native_zplus (native_zplus hv 1) (native_zneg lv)
  have hHighSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim2High x wm jp)) =
        SmtType.BitVec (native_int_to_nat highWidth) := by
    rw [hWm, hJp]
    exact smt_typeof_extract_of_context x w hv lv hXSmtTy hw0 hlv0
      hhvw hHighWidth0
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 := by
    rfl
  have hInnerSmtTy := smt_typeof_concat_bitvec_extract y (Term.Binary 0 0)
    (native_int_to_nat (native_zplus jv 1)) 0 hYSmtTy hEmptyTy
  have hRebuildSmtTy := smt_typeof_concat_bitvec_extract
    (bvEqExtractElim2High x wm jp)
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) (Term.Binary 0 0))
    (native_int_to_nat highWidth)
    (native_int_to_nat
      (native_zplus
        (native_nat_to_int (native_int_to_nat (native_zplus jv 1)))
        (native_nat_to_int 0)))
    hHighSmtTy hInnerSmtTy
  have hRebuildTrans :
      RuleProofs.eo_has_smt_translation (bvEqExtractElim2Rebuild x y wm jp) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt (bvEqExtractElim2Rebuild x y wm jp)) =
        _ by simpa [bvEqExtractElim2Rebuild] using hRebuildSmtTy]
    intro h
    cases h
  have hRightEoEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hRightTy
  have hXBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hRebuildBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvEqExtractElim2Rebuild x y wm jp)
      (__eo_typeof (bvEqExtractElim2Rebuild x y wm jp))
      (__eo_to_smt (bvEqExtractElim2Rebuild x y wm jp)) rfl
      hRebuildTrans rfl
  have hRebuildSame :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim2Rebuild x y wm jp)) =
        __smtx_typeof (__eo_to_smt x) := by
    rw [hRebuildBridge, ← hRightEoEq, ← hXBridge]
  exact ⟨w, jv, highWidth, hv, lv, hJ, hWm, hJp, hw0,
    hD0Simple, hjw, native_zleq_of_zlt_true _ _ hHighWidth0,
    hlv0, hhvw, hXSmtTy, hYSmtTy,
    hHighSmtTy, hRebuildSame⟩

theorem typed_bv_eq_extract_elim2_term
    (x y j wm jp : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim2Term x y j wm jp) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvEqExtractElim2Term x y j wm jp) := by
  intro hXTrans hYTrans hTy
  rcases bv_eq_extract_elim2_smt_context x y j wm jp
      hXTrans hYTrans hTy with
    ⟨w, jv, highWidth, hv, lv, rfl, rfl, rfl, hw0, hD0, hjw,
      hHighWidth0, hlv0, hhvw, hXSmtTy, hYSmtTy, hHighSmtTy,
      hRebuildSame⟩
  have hSliceTy :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim2Slice x (Term.Numeral jv))) =
        SmtType.BitVec (native_int_to_nat (native_zplus jv 1)) := by
    simpa [bvEqExtractElim2Slice, SmtEval.native_zplus,
      SmtEval.native_zneg] using
      (smt_typeof_extract_of_context x w jv 0 hXSmtTy hw0
        (by native_decide) hjw
        (by simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hD0))
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (bvEqExtractElim2LeftEq x y (Term.Numeral jv)) := by
    unfold bvEqExtractElim2LeftEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hSliceTy.trans hYSmtTy.symm) (by rw [hSliceTy]; simp)
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (bvEqExtractElim2RightEq x y (Term.Numeral hv)
          (Term.Numeral lv)) := by
    unfold bvEqExtractElim2RightEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      hRebuildSame.symm (by rw [hXSmtTy]; simp)
  unfold bvEqExtractElim2Term
  have hLeftSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim2LeftEq x y (Term.Numeral jv))) =
        SmtType.Bool := hLeftBool
  have hRightSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim2RightEq x y (Term.Numeral hv)
              (Term.Numeral lv))) =
        SmtType.Bool := hRightBool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftSmt.trans hRightSmt.symm)
    (by rw [hLeftSmt]; simp)

private theorem eval_bvsize_bv_eq_extract_elim
    (M : SmtModel) (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  intro hw0 hXTy
  have hRound := native_int_to_nat_roundtrip w hw0
  have hSize :
      __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)) = w := by
    rw [hXTy]
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

private theorem eval_width_minus_one_bv_eq_extract_elim
    (M : SmtModel) (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))) =
      SmtValue.Numeral (native_zplus w (native_zneg 1)) := by
  intro hw0 hXTy
  change __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (SmtTerm.Numeral 1)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_bv_eq_extract_elim M x w hw0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem eval_successor_bv_eq_extract_elim
    (M : SmtModel) (jv : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
            (Term.Numeral jv))
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
              (Term.Numeral 1)) (Term.Numeral 0)))) =
      SmtValue.Numeral (native_zplus jv 1) := by
  change __smtx_model_eval M
      (SmtTerm.plus (SmtTerm.Numeral jv)
        (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) = _
  simp [__smtx_model_eval, __smtx_model_eval_plus, native_zplus]

private theorem eval_gt_bv_eq_extract_elim
    (M : SmtModel) (a b : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt)
            (Term.Numeral a)) (Term.Numeral b))) =
      SmtValue.Boolean (native_zlt b a) := by
  change __smtx_model_eval M
      (SmtTerm.gt (SmtTerm.Numeral a) (SmtTerm.Numeral b)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval, __smtx_model_eval_gt,
    __smtx_model_eval_lt]

private theorem model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim
    (M : SmtModel) (a b : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b)) =
      SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem bv_eq_extract_elim2_premises_numeric
    (M : SmtModel) (x : Term) (w jv hv lv : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    eo_interprets M
      (bvEqExtractElimWidthMinusOnePrem x (Term.Numeral hv)) true ->
    eo_interprets M
      (bvEqExtractElimSuccessorPrem (Term.Numeral jv)
        (Term.Numeral lv)) true ->
    eo_interprets M
      (bvEqExtractElimHighRoomPrem (Term.Numeral hv)
        (Term.Numeral jv)) true ->
    hv = native_zplus w (native_zneg 1) ∧
      lv = native_zplus jv 1 ∧ native_zlt jv hv = true := by
  intro hw0 hXTy hWidthPrem hSuccPrem hRoomPrem
  have hWidthEq := model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim M
    (Term.Numeral hv)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)) (Term.Numeral 1))
    (by simpa [bvEqExtractElimWidthMinusOnePrem] using hWidthPrem)
  have hSuccEq := model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim M
    (Term.Numeral lv)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral jv))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0)))
    (by simpa [bvEqExtractElimSuccessorPrem] using hSuccPrem)
  have hRoomEq := model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) (Term.Numeral hv))
      (Term.Numeral jv)) (Term.Boolean true)
    (by simpa [bvEqExtractElimHighRoomPrem] using hRoomPrem)
  rw [eval_width_minus_one_bv_eq_extract_elim M x w hw0 hXTy] at hWidthEq
  rw [eval_successor_bv_eq_extract_elim M jv] at hSuccEq
  rw [eval_gt_bv_eq_extract_elim M hv jv] at hRoomEq
  change __smtx_model_eval_eq (SmtValue.Numeral hv)
      (SmtValue.Numeral (native_zplus w (native_zneg 1))) =
    SmtValue.Boolean true at hWidthEq
  change __smtx_model_eval_eq (SmtValue.Numeral lv)
      (SmtValue.Numeral (native_zplus jv 1)) =
    SmtValue.Boolean true at hSuccEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hWidthEq hSuccEq hRoomEq
  exact ⟨hWidthEq, hSuccEq, hRoomEq⟩

private theorem concat_bv_eq_extract_elim_values
    (a : BitVec A) (b : BitVec B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑a.toNat : Int))
        (SmtValue.Binary (↑B : Int) (↑b.toNat : Int)) =
      SmtValue.Binary (↑(A + B) : Int) (↑(a ++ b).toNat : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hWidth : (↑A + ↑B : Int) = ↑(A + B) := by norm_cast
  rw [hWidth, natpow2_eq B, natpow2_eq (A + B),
    show ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (A + B)) = ((2 ^ (A + B) : Nat) : Int) by
      norm_cast]
  norm_cast
  have hbLt : b.toNat < 2 ^ B := b.isLt
  have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hbLt a.toNat
  have hFormula : a.toNat * 2 ^ B + b.toNat = (a ++ b).toNat := by
    rw [BitVec.toNat_append, ← hShiftOr, Nat.shiftLeft_eq]
  rw [hFormula, Nat.mod_eq_of_lt (a ++ b).isLt]

private theorem concat_empty_bv_eq_extract_elim_value (a : BitVec A) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑a.toNat : Int))
        (SmtValue.Binary 0 0) =
      SmtValue.Binary (↑A : Int) (↑a.toNat : Int) := by
  simpa using concat_bv_eq_extract_elim_values a (0#0)

private theorem low_extract_eq_iff_rebuild
    (x : BitVec W) (y : BitVec D) (hD : D ≤ W) :
    x.extractLsb' 0 D = y ↔
      x = (x.extractLsb' D (W - D) ++ y).cast (by omega) := by
  constructor
  · intro hLow
    rw [← hLow]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_cast, BitVec.getElem_append,
      BitVec.getElem_extractLsb', Nat.zero_add]
    by_cases hLowBit : i < D
    · simp only [hLowBit, ↓reduceDIte]
      exact (BitVec.getLsbD_eq_getElem hi).symm
    · simp only [hLowBit, ↓reduceDIte]
      rw [show D + (i - D) = i by omega,
        BitVec.getLsbD_eq_getElem hi]
  · intro hRebuild
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hBit := congrArg (fun z : BitVec W => z[i]) hRebuild
    have hBit' : x[i] = y[i] := by
      simpa [BitVec.getElem_cast, BitVec.getElem_append, hi] using hBit
    rw [BitVec.getElem_extractLsb' hi,
      BitVec.getLsbD_eq_getElem (by omega)]
    simpa using hBit'

private theorem eval_eq_low_extract_eq_rebuild
    (x : BitVec W) (y : BitVec D) (hD : D ≤ W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑D : Int)
          (↑(x.extractLsb' 0 D).toNat : Int))
        (SmtValue.Binary (↑D : Int) (↑y.toNat : Int)) =
      __smtx_model_eval_eq
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int)
          (↑(((x.extractLsb' D (W - D) ++ y).cast (by omega) :
            BitVec W).toNat) : Int)) := by
  have hIff := low_extract_eq_iff_rebuild x y hD
  by_cases hLow : x.extractLsb' 0 D = y
  · have hRebuild := hIff.mp hLow
    have hLowNat := congrArg BitVec.toNat hLow
    have hRebuildNat := congrArg BitVec.toNat hRebuild
    have hLeftValues :
        SmtValue.Binary (↑D : Int)
            (↑(x.extractLsb' 0 D).toNat : Int) =
          SmtValue.Binary (↑D : Int) (↑y.toNat : Int) := by
      rw [hLowNat]
    have hRightValues :
        SmtValue.Binary (↑W : Int) (↑x.toNat : Int) =
          SmtValue.Binary (↑W : Int)
            (↑(((x.extractLsb' D (W - D) ++ y).cast (by omega) :
              BitVec W).toNat) : Int) := by
      rw [hRebuildNat]
    simp only [__smtx_model_eval_eq, native_veq, hLeftValues,
      hRightValues, decide_true]
  · have hRebuild :
        x ≠ (x.extractLsb' D (W - D) ++ y).cast (by omega) := by
      exact fun h => hLow (hIff.mpr h)
    have hLowNat : (x.extractLsb' 0 D).toNat ≠ y.toNat := by
      exact fun h => hLow (BitVec.eq_of_toNat_eq h)
    have hRebuildNat :
        x.toNat ≠
          ((x.extractLsb' D (W - D) ++ y).cast (by omega) :
            BitVec W).toNat := by
      exact fun h => hRebuild (BitVec.eq_of_toNat_eq h)
    have hLeftValues :
        SmtValue.Binary (↑D : Int)
            (↑(x.extractLsb' 0 D).toNat : Int) ≠
          SmtValue.Binary (↑D : Int) (↑y.toNat : Int) := by
      intro h
      injection h with _ hPayload
      exact hLowNat (by exact_mod_cast hPayload)
    have hRightValues :
        SmtValue.Binary (↑W : Int) (↑x.toNat : Int) ≠
          SmtValue.Binary (↑W : Int)
            (↑(((x.extractLsb' D (W - D) ++ y).cast (by omega) :
              BitVec W).toNat) : Int) := by
      intro h
      injection h with _ hPayload
      exact hRebuildNat (by exact_mod_cast hPayload)
    simp only [__smtx_model_eval_eq, native_veq, hLeftValues,
      hRightValues, decide_false]

theorem facts_bv_eq_extract_elim2_term
    (M : SmtModel) (hM : model_wf M)
    (x y j wm jp : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim2Term x y j wm jp) = Term.Bool ->
    eo_interprets M (bvEqExtractElimWidthMinusOnePrem x wm) true ->
    eo_interprets M (bvEqExtractElimSuccessorPrem j jp) true ->
    eo_interprets M (bvEqExtractElimHighRoomPrem wm j) true ->
    eo_interprets M (bvEqExtractElim2Term x y j wm jp) true := by
  intro hXTrans hYTrans hTy hWidthPrem hSuccPrem hRoomPrem
  rcases bv_eq_extract_elim2_smt_context x y j wm jp
      hXTrans hYTrans hTy with
    ⟨w, jv, highWidth, hv, lv, rfl, rfl, rfl, hw0, hD0, hjw,
      _hHighWidth0, _hlv0, _hhvw, hXSmtTy, hYSmtTy, _hHighSmtTy,
      _hRebuildSame⟩
  rcases bv_eq_extract_elim2_premises_numeric M x w jv hv lv hw0
      hXSmtTy hWidthPrem hSuccPrem hRoomPrem with
    ⟨hHv, hLv, _hRoom⟩
  subst hv
  subst lv
  let d : native_Int := native_zplus jv 1
  let W : Nat := native_int_to_nat w
  let D : Nat := native_int_to_nat d
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip d
        (native_zleq_of_zlt_true _ _ (by simpa [d] using hD0))
  have hjwInt : jv < w := by
    simpa [SmtEval.native_zlt] using hjw
  have hdwInt : d ≤ w := by
    dsimp [d]
    simpa [SmtEval.native_zplus] using (Int.add_one_le_iff.mpr hjwInt)
  have hDWInt : (↑D : Int) ≤ (↑W : Int) := by
    rw [hDRound, hWRound]
    exact hdwInt
  have hDW : D ≤ W := by exact_mod_cast hDWInt
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with
    ⟨p, hXEval0, hPCanonical⟩
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval0
  have hWNat0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hPRange := bitvec_payload_range_of_canonical hWNat0 hPCanonical
  have hp0 : (0 : Int) ≤ p := hPRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hPRange.2
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) D
      (by simpa [D, d] using hYSmtTy) with
    ⟨q, hYEval0, hQCanonical⟩
  have hYEval :
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (↑D : Int) q := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hYEval0
  have hDNat0 : native_zleq 0 (native_nat_to_int D) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hQRange := bitvec_payload_range_of_canonical hDNat0 hQCanonical
  have hq0 : (0 : Int) ≤ q := hQRange.1
  have hq1 : q < (2 : Int) ^ D := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hQRange.2
  let X : BitVec W := BitVec.ofInt W p
  let Y : BitVec D := BitVec.ofInt D q
  have hXPayload : (↑X.toNat : Int) = p := by
    have hToNat : X.toNat = p.toNat := by
      simpa [X] using ofInt_toNat_canonical W p hp0 hp1
    rw [hToNat]
    exact Int.toNat_of_nonneg hp0
  have hYPayload : (↑Y.toNat : Int) = q := by
    have hToNat : Y.toNat = q.toNat := by
      simpa [Y] using ofInt_toNat_canonical D q hq0 hq1
    rw [hToNat]
    exact Int.toNat_of_nonneg hq0
  have hXEvalBitVec :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) (↑X.toNat : Int) := by
    rw [hXEval, hXPayload]
  have hYEvalBitVec :
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (↑D : Int) (↑Y.toNat : Int) := by
    rw [hYEval, hYPayload]
  have hLowLen : jv + 1 + -(0 : Int) = (↑D : Int) := by
    rw [hDRound]
    simp [d, SmtEval.native_zplus]
  have hLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2Slice x (Term.Numeral jv))) =
        SmtValue.Binary (↑D : Int)
          (↑(X.extractLsb' 0 D).toNat : Int) := by
    rw [show bvEqExtractElim2Slice x (Term.Numeral jv) =
        bvExtractTerm x (Term.Numeral jv) (Term.Numeral 0) by rfl,
      eval_extract_term, hXEval]
    simpa [X] using
      (extract_val_bitvec_start_len W 0 D p jv 0 hp0 hp1 rfl hLowLen)
  have hSubCast : (↑(W - D) : Int) = w - d := by
    omega
  have hHighLen :
      native_zplus w (native_zneg 1) + 1 + -d =
        (↑(W - D) : Int) := by
    rw [hSubCast]
    change w + (-1 : Int) + 1 + -d = w - d
    have hCancel : w + (-1 : Int) + 1 = w := by
      calc
        w + (-1 : Int) + 1 = w + ((-1 : Int) + 1) :=
          Int.add_assoc w (-1) 1
        _ = w := by simp
    change (w + (-1 : Int) + 1) + -d = w + -d
    exact congrArg (fun z : Int => z + -d) hCancel
  have hHighEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2High x
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral d))) =
        SmtValue.Binary (↑(W - D) : Int)
          (↑(X.extractLsb' D (W - D)).toNat : Int) := by
    rw [show bvEqExtractElim2High x
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral d) =
        bvExtractTerm x
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral d) by rfl,
      eval_extract_term, hXEval]
    simpa [X] using
      (extract_val_bitvec_start_len W D (W - D) p
        (native_zplus w (native_zneg 1)) d hp0 hp1 hDRound.symm
        hHighLen)
  have hInnerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
              (Term.Binary 0 0))) =
        SmtValue.Binary (↑D : Int) (↑Y.toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt y)
          (__eo_to_smt (Term.Binary 0 0))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hYEvalBitVec]
    change __smtx_model_eval_concat
        (SmtValue.Binary (↑D : Int) (↑Y.toNat : Int))
        (SmtValue.Binary 0 0) = _
    exact concat_empty_bv_eq_extract_elim_value Y
  let R : BitVec W :=
    (X.extractLsb' D (W - D) ++ Y).cast (by omega)
  have hRebuildEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2Rebuild x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral d))) =
        SmtValue.Binary (↑W : Int) (↑R.toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat
          (__eo_to_smt
            (bvEqExtractElim2High x
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral d)))
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
              (Term.Binary 0 0)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hHighEval, hInnerEval,
      concat_bv_eq_extract_elim_values]
    simpa [R, Nat.sub_add_cancel hDW]
  have hLeftEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2LeftEq x y (Term.Numeral jv))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑D : Int)
            (↑(X.extractLsb' 0 D).toNat : Int))
          (SmtValue.Binary (↑D : Int) (↑Y.toNat : Int)) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvEqExtractElim2Slice x (Term.Numeral jv)))
          (__eo_to_smt y)) = _
    rw [smtx_eval_eq_term_eq, hLowEval, hYEvalBitVec]
  have hRightEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2RightEq x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral d))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑W : Int) (↑X.toNat : Int))
          (SmtValue.Binary (↑W : Int) (↑R.toNat : Int)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x)
          (__eo_to_smt
            (bvEqExtractElim2Rebuild x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral d)))) = _
    rw [smtx_eval_eq_term_eq, hXEvalBitVec, hRebuildEval]
  have hInnerEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2LeftEq x y (Term.Numeral jv))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim2RightEq x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral d))) := by
    rw [hLeftEqEval, hRightEqEval]
    simpa [R] using eval_eq_low_extract_eq_rebuild X Y hDW
  have hBool := typed_bv_eq_extract_elim2_term x y
    (Term.Numeral jv)
    (Term.Numeral (native_zplus w (native_zneg 1)))
    (Term.Numeral d) hXTrans hYTrans hTy
  unfold bvEqExtractElim2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvEqExtractElim2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvEqExtractElim2LeftEq x y (Term.Numeral jv))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvEqExtractElim2RightEq x y
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral d))))
    rw [hInnerEqEval]
    exact RuleProofs.smt_value_rel_refl _

def bvEqExtractElim2Program
    (x y j wm jp P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_eq_extract_elim2 x y j wm jp
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private theorem bv_eq_extract_elim2_premise_shape
    (x y j wm jp P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> j ≠ Term.Stuck ->
    wm ≠ Term.Stuck -> jp ≠ Term.Stuck ->
    bvEqExtractElim2Program x y j wm jp P1 P2 P3 ≠ Term.Stuck ->
    ∃ wmRef1 xRef jpRef jRef1 wmRef2 jRef2,
      P1 = bvEqExtractElimWidthMinusOnePrem xRef wmRef1 ∧
      P2 = bvEqExtractElimSuccessorPrem jRef1 jpRef ∧
      P3 = bvEqExtractElimHighRoomPrem wmRef2 jRef2 := by
  intro hX hY hJ hWm hJp hProg
  by_cases hShape :
      ∃ wmRef1 xRef jpRef jRef1 wmRef2 jRef2,
        P1 = bvEqExtractElimWidthMinusOnePrem xRef wmRef1 ∧
        P2 = bvEqExtractElimSuccessorPrem jRef1 jpRef ∧
        P3 = bvEqExtractElimHighRoomPrem wmRef2 jRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_eq_extract_elim2.eq_7
      x y j wm jp (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hY hJ hWm hJp (by
        intro wmRef1 xRef jpRef jRef1 wmRef2 jRef2 hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨wmRef1, xRef, jpRef, jRef1, wmRef2, jRef2,
            rfl, rfl, rfl⟩)

private theorem bv_eq_extract_elim2_program_canonical
    (x y j wm jp : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> j ≠ Term.Stuck ->
    wm ≠ Term.Stuck -> jp ≠ Term.Stuck ->
    bvEqExtractElim2Program x y j wm jp
        (bvEqExtractElimWidthMinusOnePrem x wm)
        (bvEqExtractElimSuccessorPrem j jp)
        (bvEqExtractElimHighRoomPrem wm j) =
      bvEqExtractElim2Term x y j wm jp := by
  intro hX hY hJ hWm hJp
  unfold bvEqExtractElim2Program bvEqExtractElimWidthMinusOnePrem
    bvEqExtractElimSuccessorPrem bvEqExtractElimHighRoomPrem
  rw [__eo_prog_bv_eq_extract_elim2.eq_6
    x y j wm jp wm x jp j wm j hX hY hJ hWm hJp]
  simp [bvEqExtractElim2Term, bvEqExtractElim2LeftEq,
    bvEqExtractElim2RightEq, bvEqExtractElim2Rebuild,
    bvEqExtractElim2High, bvEqExtractElim2Slice, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hY, hJ, hWm, hJp]

private theorem bv_eq_extract_elim2_program_normalize
    (x y j wm jp P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation wm ->
    RuleProofs.eo_has_smt_translation jp ->
    bvEqExtractElim2Program x y j wm jp P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvEqExtractElimWidthMinusOnePrem x wm ∧
      P2 = bvEqExtractElimSuccessorPrem j jp ∧
      P3 = bvEqExtractElimHighRoomPrem wm j ∧
      bvEqExtractElim2Program x y j wm jp P1 P2 P3 =
        bvEqExtractElim2Term x y j wm jp := by
  intro hXTrans hYTrans hJTrans hWmTrans hJpTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hWm := RuleProofs.term_ne_stuck_of_has_smt_translation wm hWmTrans
  have hJp := RuleProofs.term_ne_stuck_of_has_smt_translation jp hJpTrans
  rcases bv_eq_extract_elim2_premise_shape x y j wm jp P1 P2 P3
      hX hY hJ hWm hJp hProg with
    ⟨wmRef1, xRef, jpRef, jRef1, wmRef2, jRef2, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvEqExtractElim2Program bvEqExtractElimWidthMinusOnePrem
    bvEqExtractElimSuccessorPrem bvEqExtractElimHighRoomPrem at hReq
  rw [__eo_prog_bv_eq_extract_elim2.eq_6
    x y j wm jp wmRef1 xRef jpRef jRef1 wmRef2 jRef2
    hX hY hJ hWm hJp] at hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hFirst5, hJRef2⟩
  rcases bv_extract_support_and_true hFirst5 with ⟨hFirst4, hWmRef2⟩
  rcases bv_extract_support_and_true hFirst4 with ⟨hFirst3, hJRef1⟩
  rcases bv_extract_support_and_true hFirst3 with ⟨hFirst2, hJpRef⟩
  rcases bv_extract_support_and_true hFirst2 with ⟨hWmRef1, hXRef⟩
  have hWmRef1Eq := bv_extract_support_eq_true hWmRef1
  have hXRefEq := bv_extract_support_eq_true hXRef
  have hJpRefEq := bv_extract_support_eq_true hJpRef
  have hJRef1Eq := bv_extract_support_eq_true hJRef1
  have hWmRef2Eq := bv_extract_support_eq_true hWmRef2
  have hJRef2Eq := bv_extract_support_eq_true hJRef2
  subst wmRef1
  subst xRef
  subst jpRef
  subst jRef1
  subst wmRef2
  subst jRef2
  refine ⟨hP1, hP2, hP3, ?_⟩
  rw [hP1, hP2, hP3]
  exact bv_eq_extract_elim2_program_canonical x y j wm jp
    hX hY hJ hWm hJp

theorem typed_bv_eq_extract_elim2_program
    (x y j wm jp P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation wm ->
    RuleProofs.eo_has_smt_translation jp ->
    __eo_typeof (bvEqExtractElim2Program x y j wm jp P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvEqExtractElim2Program x y j wm jp P1 P2 P3) := by
  intro hXTrans hYTrans hJTrans hWmTrans hJpTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bv_eq_extract_elim2_program_normalize x y j wm jp P1 P2 P3
      hXTrans hYTrans hJTrans hWmTrans hJpTrans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvEqExtractElim2Term x y j wm jp) = Term.Bool := by
    rw [← hProgramEq]
    exact hTy
  rw [hProgramEq]
  exact typed_bv_eq_extract_elim2_term x y j wm jp
    hXTrans hYTrans hTermTy

theorem facts_bv_eq_extract_elim2_program
    (M : SmtModel) (hM : model_wf M)
    (x y j wm jp P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation wm ->
    RuleProofs.eo_has_smt_translation jp ->
    __eo_typeof (bvEqExtractElim2Program x y j wm jp P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M (bvEqExtractElim2Program x y j wm jp P1 P2 P3) true := by
  intro hXTrans hYTrans hJTrans hWmTrans hJpTrans hTy
    hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bv_eq_extract_elim2_program_normalize x y j wm jp P1 P2 P3
      hXTrans hYTrans hJTrans hWmTrans hJpTrans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvEqExtractElim2Term x y j wm jp) = Term.Bool := by
    rw [← hProgramEq]
    exact hTy
  have hPrem1 :
      eo_interprets M (bvEqExtractElimWidthMinusOnePrem x wm) true := by
    simpa [hP1] using hP1True
  have hPrem2 :
      eo_interprets M (bvEqExtractElimSuccessorPrem j jp) true := by
    simpa [hP2] using hP2True
  have hPrem3 :
      eo_interprets M (bvEqExtractElimHighRoomPrem wm j) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_eq_extract_elim2_term M hM x y j wm jp
    hXTrans hYTrans hTermTy hPrem1 hPrem2 hPrem3

/-! Support for the symmetric upper-slice reconstruction rule. -/

def bvEqExtractElim3Slice (x j i : Term) : Term :=
  bvExtractTerm x j i

def bvEqExtractElim3LeftEq (x y i j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvEqExtractElim3Slice x j i)) y

def bvEqExtractElim3Low (x im : Term) : Term :=
  bvExtractTerm x im (Term.Numeral 0)

def bvEqExtractElim3Rebuild (x y im : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvEqExtractElim3Low x im))
      (Term.Binary 0 0))

def bvEqExtractElim3RightEq (x y im : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
    (bvEqExtractElim3Rebuild x y im)

def bvEqExtractElim3Term (x y i j im : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvEqExtractElim3LeftEq x y i j))
    (bvEqExtractElim3RightEq x y im)

def bvEqExtractElimPredecessorPrem (i im : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) im)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) i) (Term.Numeral 1))

def bvEqExtractElimPositivePrem (i : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) i) (Term.Numeral 0)))
    (Term.Boolean true)

private theorem bv_eq_extract_elim3_inner_types
    (x y i j im : Term) :
    __eo_typeof (bvEqExtractElim3Term x y i j im) = Term.Bool ->
    __eo_typeof (bvEqExtractElim3LeftEq x y i j) = Term.Bool ∧
      __eo_typeof (bvEqExtractElim3RightEq x y im) = Term.Bool := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof (bvEqExtractElim3LeftEq x y i j))
      (__eo_typeof (bvEqExtractElim3RightEq x y im)) = Term.Bool at hTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy with
    ⟨hLeft, hRight⟩
  constructor
  · change __eo_typeof_eq
      (__eo_typeof (bvEqExtractElim3Slice x j i)) (__eo_typeof y) =
        Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck_bv_extract
    exact hLeft
  · change __eo_typeof_eq (__eo_typeof x)
      (__eo_typeof (bvEqExtractElim3Rebuild x y im)) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck_bv_extract
    exact hRight

private theorem bv_eq_extract_elim3_smt_context
    (x y i j im : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim3Term x y i j im) = Term.Bool ->
    ∃ w iv sliceWidth jv mv lowWidth,
      i = Term.Numeral iv ∧ j = Term.Numeral jv ∧
      im = Term.Numeral mv ∧
      sliceWidth =
        native_zplus (native_zplus jv 1) (native_zneg iv) ∧
      lowWidth = native_zplus (native_zplus mv 1) (native_zneg 0) ∧
      native_zleq 0 w = true ∧ native_zleq 0 iv = true ∧
      native_zlt jv w = true ∧
      native_zleq 0 sliceWidth = true ∧
      native_zlt mv w = true ∧ native_zleq 0 lowWidth = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim3Slice x j i)) =
        SmtType.BitVec (native_int_to_nat sliceWidth) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat sliceWidth) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim3Low x im)) =
        SmtType.BitVec (native_int_to_nat lowWidth) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim3Rebuild x y im)) =
        __smtx_typeof (__eo_to_smt x) := by
  intro hXTrans hYTrans hTy
  rcases bv_eq_extract_elim3_inner_types x y i j im hTy with
    ⟨hLeftTy, hRightTy⟩
  have hLeftOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftTy
  have hSliceNe : __eo_typeof (bvEqExtractElim3Slice x j i) ≠ Term.Stuck :=
    hLeftOps.1
  rcases bv_extract_context_of_non_stuck x j i hXTrans hSliceNe with
    ⟨w, jv, iv, _hXTy, hJ, hI, hw0, hiv0, hjvw,
      hSliceWidth0, hXSmtTy⟩
  let sliceWidth := native_zplus (native_zplus jv 1) (native_zneg iv)
  have hSliceSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim3Slice x j i)) =
        SmtType.BitVec (native_int_to_nat sliceWidth) := by
    rw [hJ, hI]
    exact smt_typeof_extract_of_context x w jv iv hXSmtTy hw0 hiv0
      hjvw hSliceWidth0
  have hSliceTrans :
      RuleProofs.eo_has_smt_translation (bvEqExtractElim3Slice x j i) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSliceSmtTy]
    intro h
    cases h
  have hLeftEoEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftTy
  have hSliceBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvEqExtractElim3Slice x j i)
      (__eo_typeof (bvEqExtractElim3Slice x j i))
      (__eo_to_smt (bvEqExtractElim3Slice x j i)) rfl hSliceTrans rfl
  have hYBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y (__eo_typeof y) (__eo_to_smt y) rfl hYTrans rfl
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat sliceWidth) := by
    rw [hYBridge, ← hLeftEoEq, ← hSliceBridge]
    exact hSliceSmtTy
  have hRightOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightTy
  have hRebuildNe :
      __eo_typeof (bvEqExtractElim3Rebuild x y im) ≠ Term.Stuck :=
    hRightOps.2
  have hOuterConcatNe :
      __eo_typeof_concat (__eo_typeof y)
          (__eo_typeof
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.concat)
                (bvEqExtractElim3Low x im))
              (Term.Binary 0 0))) ≠ Term.Stuck := by
    exact hRebuildNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract
      hOuterConcatNe with
    ⟨_yWidthTerm, innerWidthTerm, _hYEo, hInnerEo⟩
  have hInnerNe :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.concat)
              (bvEqExtractElim3Low x im))
            (Term.Binary 0 0)) ≠ Term.Stuck := by
    rw [hInnerEo]
    intro h
    cases h
  have hInnerConcatNe :
      __eo_typeof_concat (__eo_typeof (bvEqExtractElim3Low x im))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    exact hInnerNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract
      hInnerConcatNe with
    ⟨lowWidthTerm, _emptyWidthTerm, hLowEo, _hEmptyEo⟩
  have hLowNe : __eo_typeof (bvEqExtractElim3Low x im) ≠ Term.Stuck := by
    rw [hLowEo]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x im (Term.Numeral 0)
      hXTrans hLowNe with
    ⟨wLow, mv, zero, _hXTyLow, hIm, hZero, hwLow0, hzero0,
      hmvw, hLowWidth0, hXSmtTyLow⟩
  have hZeroEq : zero = 0 := by
    simpa using congrArg (fun t => match t with
      | Term.Numeral n => n
      | _ => 0) hZero.symm
  subst zero
  have hWidthNat : native_int_to_nat w = native_int_to_nat wLow := by
    rw [hXSmtTy] at hXSmtTyLow
    simpa using hXSmtTyLow
  have hwLowEq : wLow = w :=
    nonneg_int_eq_of_toNat_eq wLow w hwLow0 hw0 hWidthNat.symm
  rw [hwLowEq] at hmvw
  let lowWidth := native_zplus (native_zplus mv 1) (native_zneg 0)
  have hLowSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim3Low x im)) =
        SmtType.BitVec (native_int_to_nat lowWidth) := by
    rw [hIm]
    exact smt_typeof_extract_of_context x w mv 0 hXSmtTy hw0 hzero0
      hmvw hLowWidth0
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 := by
    rfl
  have hInnerSmtTy := smt_typeof_concat_bitvec_extract
    (bvEqExtractElim3Low x im) (Term.Binary 0 0)
    (native_int_to_nat lowWidth) 0 hLowSmtTy hEmptyTy
  have hRebuildSmtTy := smt_typeof_concat_bitvec_extract y
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvEqExtractElim3Low x im))
      (Term.Binary 0 0))
    (native_int_to_nat sliceWidth)
    (native_int_to_nat
      (native_zplus (native_nat_to_int (native_int_to_nat lowWidth))
        (native_nat_to_int 0)))
    hYSmtTy hInnerSmtTy
  have hRebuildTrans :
      RuleProofs.eo_has_smt_translation (bvEqExtractElim3Rebuild x y im) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof
          (__eo_to_smt (bvEqExtractElim3Rebuild x y im)) = _ by
      simpa [bvEqExtractElim3Rebuild] using hRebuildSmtTy]
    intro h
    cases h
  have hRightEoEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hRightTy
  have hXBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hRebuildBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvEqExtractElim3Rebuild x y im)
      (__eo_typeof (bvEqExtractElim3Rebuild x y im))
      (__eo_to_smt (bvEqExtractElim3Rebuild x y im)) rfl
      hRebuildTrans rfl
  have hRebuildSame :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim3Rebuild x y im)) =
        __smtx_typeof (__eo_to_smt x) := by
    rw [hRebuildBridge, ← hRightEoEq, ← hXBridge]
  exact ⟨w, iv, sliceWidth, jv, mv, lowWidth, hI, hJ, hIm, rfl, rfl, hw0,
    hiv0, hjvw, native_zleq_of_zlt_true _ _ hSliceWidth0, hmvw,
    native_zleq_of_zlt_true _ _ hLowWidth0, hXSmtTy,
    hSliceSmtTy, hYSmtTy, hLowSmtTy, hRebuildSame⟩

theorem typed_bv_eq_extract_elim3_term
    (x y i j im : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim3Term x y i j im) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvEqExtractElim3Term x y i j im) := by
  intro hXTrans hYTrans hTy
  rcases bv_eq_extract_elim3_smt_context x y i j im
      hXTrans hYTrans hTy with
    ⟨w, iv, sliceWidth, jv, mv, lowWidth, rfl, rfl, rfl,
      _hSliceDef, _hLowDef, hw0,
      hiv0, hjvw, hSliceWidth0, hmvw, hLowWidth0, hXSmtTy,
      hSliceTy, hYSmtTy, hLowSmtTy, hRebuildSame⟩
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (bvEqExtractElim3LeftEq x y (Term.Numeral iv)
          (Term.Numeral jv)) := by
    unfold bvEqExtractElim3LeftEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hSliceTy.trans hYSmtTy.symm) (by rw [hSliceTy]; simp)
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (bvEqExtractElim3RightEq x y (Term.Numeral mv)) := by
    unfold bvEqExtractElim3RightEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      hRebuildSame.symm (by rw [hXSmtTy]; simp)
  unfold bvEqExtractElim3Term
  have hLeftSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim3LeftEq x y (Term.Numeral iv)
              (Term.Numeral jv))) = SmtType.Bool := hLeftBool
  have hRightSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim3RightEq x y (Term.Numeral mv))) =
        SmtType.Bool := hRightBool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftSmt.trans hRightSmt.symm) (by rw [hLeftSmt]; simp)

private theorem eval_predecessor_bv_eq_extract_elim
    (M : SmtModel) (iv : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (Term.Numeral iv)) (Term.Numeral 1))) =
      SmtValue.Numeral (native_zplus iv (native_zneg 1)) := by
  change __smtx_model_eval M
      (SmtTerm.neg (SmtTerm.Numeral iv) (SmtTerm.Numeral 1)) = _
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem bv_eq_extract_elim3_premises_numeric
    (M : SmtModel) (x : Term) (w iv jv mv : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    eo_interprets M
      (bvEqExtractElimWidthMinusOnePrem x (Term.Numeral jv)) true ->
    eo_interprets M
      (bvEqExtractElimPredecessorPrem (Term.Numeral iv)
        (Term.Numeral mv)) true ->
    eo_interprets M
      (bvEqExtractElimPositivePrem (Term.Numeral iv)) true ->
    jv = native_zplus w (native_zneg 1) ∧
      mv = native_zplus iv (native_zneg 1) ∧
      native_zlt 0 iv = true := by
  intro hw0 hXTy hWidthPrem hPredPrem hPositivePrem
  have hWidthEq := model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim M
    (Term.Numeral jv)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)) (Term.Numeral 1))
    (by simpa [bvEqExtractElimWidthMinusOnePrem] using hWidthPrem)
  have hPredEq := model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim M
    (Term.Numeral mv)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral iv))
      (Term.Numeral 1))
    (by simpa [bvEqExtractElimPredecessorPrem] using hPredPrem)
  have hPositiveEq := model_eval_eq_true_of_eo_eq_true_bv_eq_extract_elim M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) (Term.Numeral iv))
      (Term.Numeral 0)) (Term.Boolean true)
    (by simpa [bvEqExtractElimPositivePrem] using hPositivePrem)
  rw [eval_width_minus_one_bv_eq_extract_elim M x w hw0 hXTy] at hWidthEq
  rw [eval_predecessor_bv_eq_extract_elim M iv] at hPredEq
  rw [eval_gt_bv_eq_extract_elim M iv 0] at hPositiveEq
  change __smtx_model_eval_eq (SmtValue.Numeral jv)
      (SmtValue.Numeral (native_zplus w (native_zneg 1))) =
    SmtValue.Boolean true at hWidthEq
  change __smtx_model_eval_eq (SmtValue.Numeral mv)
      (SmtValue.Numeral (native_zplus iv (native_zneg 1))) =
    SmtValue.Boolean true at hPredEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hWidthEq hPredEq hPositiveEq
  exact ⟨hWidthEq, hPredEq, hPositiveEq⟩

private theorem upper_extract_eq_iff_rebuild
    (x : BitVec W) (y : BitVec (W - I)) (hI : I ≤ W) :
    x.extractLsb' I (W - I) = y ↔
      x = (y ++ x.extractLsb' 0 I).cast (by omega) := by
  constructor
  · intro hUpper
    rw [← hUpper]
    apply BitVec.eq_of_getElem_eq
    intro k hk
    simp only [BitVec.getElem_cast, BitVec.getElem_append,
      BitVec.getElem_extractLsb', Nat.zero_add]
    by_cases hLowBit : k < I
    · simp only [hLowBit, ↓reduceDIte]
      exact (BitVec.getLsbD_eq_getElem hk).symm
    · simp only [hLowBit, ↓reduceDIte]
      rw [show I + (k - I) = k by omega,
        BitVec.getLsbD_eq_getElem hk]
  · intro hRebuild
    apply BitVec.eq_of_getElem_eq
    intro k hk
    have hFull : I + k < W := by omega
    have hBit := congrArg (fun z : BitVec W => z[I + k]'hFull) hRebuild
    have hBit' : x[I + k] = y[k] := by
      simp only [BitVec.getElem_cast, BitVec.getElem_append] at hBit
      simp only [show ¬ I + k < I by omega, ↓reduceDIte,
        show I + k - I = k by omega] at hBit
      exact hBit
    rw [BitVec.getElem_extractLsb' hk,
      BitVec.getLsbD_eq_getElem hFull]
    exact hBit'

private theorem eval_eq_upper_extract_eq_rebuild
    (x : BitVec W) (y : BitVec (W - I)) (hI : I ≤ W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑(W - I) : Int)
          (↑(x.extractLsb' I (W - I)).toNat : Int))
        (SmtValue.Binary (↑(W - I) : Int) (↑y.toNat : Int)) =
      __smtx_model_eval_eq
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int)
          (↑(((y ++ x.extractLsb' 0 I).cast (by omega) :
            BitVec W).toNat) : Int)) := by
  have hIff := upper_extract_eq_iff_rebuild x y hI
  by_cases hUpper : x.extractLsb' I (W - I) = y
  · have hRebuild := hIff.mp hUpper
    have hUpperNat := congrArg BitVec.toNat hUpper
    have hRebuildNat := congrArg BitVec.toNat hRebuild
    have hLeftValues :
        SmtValue.Binary (↑(W - I) : Int)
            (↑(x.extractLsb' I (W - I)).toNat : Int) =
          SmtValue.Binary (↑(W - I) : Int) (↑y.toNat : Int) := by
      rw [hUpperNat]
    have hRightValues :
        SmtValue.Binary (↑W : Int) (↑x.toNat : Int) =
          SmtValue.Binary (↑W : Int)
            (↑(((y ++ x.extractLsb' 0 I).cast (by omega) :
              BitVec W).toNat) : Int) := by
      rw [hRebuildNat]
    simp only [__smtx_model_eval_eq, native_veq, hLeftValues,
      hRightValues, decide_true]
  · have hRebuild :
        x ≠ (y ++ x.extractLsb' 0 I).cast (by omega) := by
      exact fun h => hUpper (hIff.mpr h)
    have hUpperNat :
        (x.extractLsb' I (W - I)).toNat ≠ y.toNat := by
      exact fun h => hUpper (BitVec.eq_of_toNat_eq h)
    have hRebuildNat :
        x.toNat ≠
          ((y ++ x.extractLsb' 0 I).cast (by omega) : BitVec W).toNat := by
      exact fun h => hRebuild (BitVec.eq_of_toNat_eq h)
    have hLeftValues :
        SmtValue.Binary (↑(W - I) : Int)
            (↑(x.extractLsb' I (W - I)).toNat : Int) ≠
          SmtValue.Binary (↑(W - I) : Int) (↑y.toNat : Int) := by
      intro h
      injection h with _ hPayload
      exact hUpperNat (by exact_mod_cast hPayload)
    have hRightValues :
        SmtValue.Binary (↑W : Int) (↑x.toNat : Int) ≠
          SmtValue.Binary (↑W : Int)
            (↑(((y ++ x.extractLsb' 0 I).cast (by omega) :
              BitVec W).toNat) : Int) := by
      intro h
      injection h with _ hPayload
      exact hRebuildNat (by exact_mod_cast hPayload)
    simp only [__smtx_model_eval_eq, native_veq, hLeftValues,
      hRightValues, decide_false]

theorem facts_bv_eq_extract_elim3_term
    (M : SmtModel) (hM : model_wf M)
    (x y i j im : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim3Term x y i j im) = Term.Bool ->
    eo_interprets M (bvEqExtractElimWidthMinusOnePrem x j) true ->
    eo_interprets M (bvEqExtractElimPredecessorPrem i im) true ->
    eo_interprets M (bvEqExtractElimPositivePrem i) true ->
    eo_interprets M (bvEqExtractElim3Term x y i j im) true := by
  intro hXTrans hYTrans hTy hWidthPrem hPredPrem hPositivePrem
  rcases bv_eq_extract_elim3_smt_context x y i j im
      hXTrans hYTrans hTy with
    ⟨w, iv, sliceWidth, jv, mv, lowWidth, rfl, rfl, rfl,
      hSliceDef, hLowDef, hw0, hiv0, _hjvw, hSliceWidth0, _hmvw,
      _hLowWidth0, hXSmtTy, _hSliceSmtTy, hYSmtTy, _hLowSmtTy,
      _hRebuildSame⟩
  rcases bv_eq_extract_elim3_premises_numeric M x w iv jv mv hw0
      hXSmtTy hWidthPrem hPredPrem hPositivePrem with
    ⟨hJv, hMv, _hPositive⟩
  subst jv
  subst mv
  have hCancel (z : Int) : z + (-1 : Int) + 1 = z := by
    calc
      z + (-1 : Int) + 1 = z + ((-1 : Int) + 1) :=
        Int.add_assoc z (-1) 1
      _ = z := by simp
  have hSliceWidthEq : sliceWidth = w - iv := by
    rw [hSliceDef]
    change w + (-1 : Int) + 1 + -iv = w + -iv
    exact congrArg (fun z : Int => z + -iv) (hCancel w)
  have hLowWidthEq : lowWidth = iv := by
    rw [hLowDef]
    change iv + (-1 : Int) + 1 + -(0 : Int) = iv
    simpa using hCancel iv
  let W : Nat := native_int_to_nat w
  let I : Nat := native_int_to_nat iv
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hIRound : (↑I : Int) = iv := by
    simpa [I, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip iv hiv0
  have hSliceNonneg : (0 : Int) ≤ w - iv := by
    have h := hSliceWidth0
    rw [hSliceWidthEq] at h
    simpa [SmtEval.native_zleq] using h
  have hiwInt : iv ≤ w := Int.sub_nonneg.mp hSliceNonneg
  have hIWInt : (↑I : Int) ≤ (↑W : Int) := by
    rw [hIRound, hWRound]
    exact hiwInt
  have hIW : I ≤ W := by exact_mod_cast hIWInt
  have hSubCast : (↑(W - I) : Int) = w - iv := by
    have hSumNat : W - I + I = W := Nat.sub_add_cancel hIW
    have hSumInt : (↑(W - I) : Int) + (↑I : Int) = (↑W : Int) := by
      exact_mod_cast hSumNat
    rw [hIRound, hWRound] at hSumInt
    exact (Int.sub_eq_iff_eq_add.mpr hSumInt.symm).symm
  have hSliceRound :
      native_nat_to_int (native_int_to_nat sliceWidth) = sliceWidth :=
    native_int_to_nat_roundtrip sliceWidth hSliceWidth0
  have hSliceNat : native_int_to_nat sliceWidth = W - I := by
    have hCast :
        (↑(native_int_to_nat sliceWidth) : Int) =
          (↑(W - I) : Int) := by
      simpa [native_nat_to_int, Smtm.native_nat_to_int,
        hSliceWidthEq, hSubCast] using hSliceRound
    exact_mod_cast hCast
  have hYSmtTyNat :
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec (W - I) := by
    simpa [hSliceNat] using hYSmtTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with
    ⟨p, hXEval0, hPCanonical⟩
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval0
  have hWNat0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hPRange := bitvec_payload_range_of_canonical hWNat0 hPCanonical
  have hp0 : (0 : Int) ≤ p := hPRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hPRange.2
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) (W - I)
      hYSmtTyNat with
    ⟨q, hYEval0, hQCanonical⟩
  have hYEval :
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (↑(W - I) : Int) q := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hYEval0
  have hUNat0 : native_zleq 0 (native_nat_to_int (W - I)) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hQRange := bitvec_payload_range_of_canonical hUNat0 hQCanonical
  have hq0 : (0 : Int) ≤ q := hQRange.1
  have hq1 : q < (2 : Int) ^ (W - I) := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hQRange.2
  let X : BitVec W := BitVec.ofInt W p
  let Y : BitVec (W - I) := BitVec.ofInt (W - I) q
  have hXPayload : (↑X.toNat : Int) = p := by
    have hToNat : X.toNat = p.toNat := by
      simpa [X] using ofInt_toNat_canonical W p hp0 hp1
    rw [hToNat]
    exact Int.toNat_of_nonneg hp0
  have hYPayload : (↑Y.toNat : Int) = q := by
    have hToNat : Y.toNat = q.toNat := by
      simpa [Y] using ofInt_toNat_canonical (W - I) q hq0 hq1
    rw [hToNat]
    exact Int.toNat_of_nonneg hq0
  have hXEvalBitVec :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) (↑X.toNat : Int) := by
    rw [hXEval, hXPayload]
  have hYEvalBitVec :
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (↑(W - I) : Int) (↑Y.toNat : Int) := by
    rw [hYEval, hYPayload]
  have hUpperLen :
      native_zplus w (native_zneg 1) + 1 + -iv =
        (↑(W - I) : Int) := by
    rw [hSubCast]
    change w + (-1 : Int) + 1 + -iv = w + -iv
    exact congrArg (fun z : Int => z + -iv) (hCancel w)
  have hUpperEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3Slice x
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral iv))) =
        SmtValue.Binary (↑(W - I) : Int)
          (↑(X.extractLsb' I (W - I)).toNat : Int) := by
    rw [show bvEqExtractElim3Slice x
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral iv) =
        bvExtractTerm x
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral iv) by rfl,
      eval_extract_term, hXEval]
    simpa [X] using
      (extract_val_bitvec_start_len W I (W - I) p
        (native_zplus w (native_zneg 1)) iv hp0 hp1 hIRound.symm
        hUpperLen)
  have hLowLen :
      native_zplus iv (native_zneg 1) + 1 + -(0 : Int) =
        (↑I : Int) := by
    rw [hIRound]
    change iv + (-1 : Int) + 1 + -(0 : Int) = iv
    simpa using hCancel iv
  have hLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3Low x
              (Term.Numeral (native_zplus iv (native_zneg 1))))) =
        SmtValue.Binary (↑I : Int)
          (↑(X.extractLsb' 0 I).toNat : Int) := by
    rw [show bvEqExtractElim3Low x
          (Term.Numeral (native_zplus iv (native_zneg 1))) =
        bvExtractTerm x
          (Term.Numeral (native_zplus iv (native_zneg 1)))
          (Term.Numeral 0) by rfl,
      eval_extract_term, hXEval]
    simpa [X] using
      (extract_val_bitvec_start_len W 0 I p
        (native_zplus iv (native_zneg 1)) 0 hp0 hp1 rfl hLowLen)
  have hInnerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.concat)
                (bvEqExtractElim3Low x
                  (Term.Numeral (native_zplus iv (native_zneg 1)))))
              (Term.Binary 0 0))) =
        SmtValue.Binary (↑I : Int)
          (↑(X.extractLsb' 0 I).toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat
          (__eo_to_smt
            (bvEqExtractElim3Low x
              (Term.Numeral (native_zplus iv (native_zneg 1)))))
          (__eo_to_smt (Term.Binary 0 0))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hLowEval]
    change __smtx_model_eval_concat
        (SmtValue.Binary (↑I : Int)
          (↑(X.extractLsb' 0 I).toNat : Int))
        (SmtValue.Binary 0 0) = _
    exact concat_empty_bv_eq_extract_elim_value (X.extractLsb' 0 I)
  let R : BitVec W := (Y ++ X.extractLsb' 0 I).cast (by omega)
  have hRebuildEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3Rebuild x y
              (Term.Numeral (native_zplus iv (native_zneg 1))))) =
        SmtValue.Binary (↑W : Int) (↑R.toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt y)
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.concat)
                (bvEqExtractElim3Low x
                  (Term.Numeral (native_zplus iv (native_zneg 1)))))
              (Term.Binary 0 0)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hYEvalBitVec, hInnerEval, concat_bv_eq_extract_elim_values]
    simpa [R, Nat.sub_add_cancel hIW]
  have hLeftEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3LeftEq x y (Term.Numeral iv)
              (Term.Numeral (native_zplus w (native_zneg 1))))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(W - I) : Int)
            (↑(X.extractLsb' I (W - I)).toNat : Int))
          (SmtValue.Binary (↑(W - I) : Int) (↑Y.toNat : Int)) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvEqExtractElim3Slice x
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral iv)))
          (__eo_to_smt y)) = _
    rw [smtx_eval_eq_term_eq, hUpperEval, hYEvalBitVec]
  have hRightEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3RightEq x y
              (Term.Numeral (native_zplus iv (native_zneg 1))))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑W : Int) (↑X.toNat : Int))
          (SmtValue.Binary (↑W : Int) (↑R.toNat : Int)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x)
          (__eo_to_smt
            (bvEqExtractElim3Rebuild x y
              (Term.Numeral (native_zplus iv (native_zneg 1)))))) = _
    rw [smtx_eval_eq_term_eq, hXEvalBitVec, hRebuildEval]
  have hInnerEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3LeftEq x y (Term.Numeral iv)
              (Term.Numeral (native_zplus w (native_zneg 1))))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim3RightEq x y
              (Term.Numeral (native_zplus iv (native_zneg 1))))) := by
    rw [hLeftEqEval, hRightEqEval]
    simpa [R] using eval_eq_upper_extract_eq_rebuild X Y hIW
  have hBool := typed_bv_eq_extract_elim3_term x y
    (Term.Numeral iv)
    (Term.Numeral (native_zplus w (native_zneg 1)))
    (Term.Numeral (native_zplus iv (native_zneg 1)))
    hXTrans hYTrans hTy
  unfold bvEqExtractElim3Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvEqExtractElim3Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvEqExtractElim3LeftEq x y (Term.Numeral iv)
            (Term.Numeral (native_zplus w (native_zneg 1))))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvEqExtractElim3RightEq x y
            (Term.Numeral (native_zplus iv (native_zneg 1))))))
    rw [hInnerEqEval]
    exact RuleProofs.smt_value_rel_refl _

def bvEqExtractElim3Program
    (x y i j im P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_eq_extract_elim3 x y i j im
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private theorem bv_eq_extract_elim3_premise_shape
    (x y i j im P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> i ≠ Term.Stuck ->
    j ≠ Term.Stuck -> im ≠ Term.Stuck ->
    bvEqExtractElim3Program x y i j im P1 P2 P3 ≠ Term.Stuck ->
    ∃ jRef xRef imRef iRef1 iRef2,
      P1 = bvEqExtractElimWidthMinusOnePrem xRef jRef ∧
      P2 = bvEqExtractElimPredecessorPrem iRef1 imRef ∧
      P3 = bvEqExtractElimPositivePrem iRef2 := by
  intro hX hY hI hJ hIm hProg
  by_cases hShape :
      ∃ jRef xRef imRef iRef1 iRef2,
        P1 = bvEqExtractElimWidthMinusOnePrem xRef jRef ∧
        P2 = bvEqExtractElimPredecessorPrem iRef1 imRef ∧
        P3 = bvEqExtractElimPositivePrem iRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_eq_extract_elim3.eq_7
      x y i j im (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hY hI hJ hIm (by
        intro jRef xRef imRef iRef1 iRef2 hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape ⟨jRef, xRef, imRef, iRef1, iRef2,
          rfl, rfl, rfl⟩)

private theorem bv_eq_extract_elim3_program_canonical
    (x y i j im : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> i ≠ Term.Stuck ->
    j ≠ Term.Stuck -> im ≠ Term.Stuck ->
    bvEqExtractElim3Program x y i j im
        (bvEqExtractElimWidthMinusOnePrem x j)
        (bvEqExtractElimPredecessorPrem i im)
        (bvEqExtractElimPositivePrem i) =
      bvEqExtractElim3Term x y i j im := by
  intro hX hY hI hJ hIm
  unfold bvEqExtractElim3Program bvEqExtractElimWidthMinusOnePrem
    bvEqExtractElimPredecessorPrem bvEqExtractElimPositivePrem
  rw [__eo_prog_bv_eq_extract_elim3.eq_6
    x y i j im j x im i i hX hY hI hJ hIm]
  simp [bvEqExtractElim3Term, bvEqExtractElim3LeftEq,
    bvEqExtractElim3RightEq, bvEqExtractElim3Rebuild,
    bvEqExtractElim3Low, bvEqExtractElim3Slice, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hY, hI, hJ, hIm]

private theorem bv_eq_extract_elim3_program_normalize
    (x y i j im P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation im ->
    bvEqExtractElim3Program x y i j im P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvEqExtractElimWidthMinusOnePrem x j ∧
      P2 = bvEqExtractElimPredecessorPrem i im ∧
      P3 = bvEqExtractElimPositivePrem i ∧
      bvEqExtractElim3Program x y i j im P1 P2 P3 =
        bvEqExtractElim3Term x y i j im := by
  intro hXTrans hYTrans hITrans hJTrans hImTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hIm := RuleProofs.term_ne_stuck_of_has_smt_translation im hImTrans
  rcases bv_eq_extract_elim3_premise_shape x y i j im P1 P2 P3
      hX hY hI hJ hIm hProg with
    ⟨jRef, xRef, imRef, iRef1, iRef2, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvEqExtractElim3Program bvEqExtractElimWidthMinusOnePrem
    bvEqExtractElimPredecessorPrem bvEqExtractElimPositivePrem at hReq
  rw [__eo_prog_bv_eq_extract_elim3.eq_6
    x y i j im jRef xRef imRef iRef1 iRef2 hX hY hI hJ hIm] at hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hFirst4, hIRef2⟩
  rcases bv_extract_support_and_true hFirst4 with ⟨hFirst3, hIRef1⟩
  rcases bv_extract_support_and_true hFirst3 with ⟨hFirst2, hImRef⟩
  rcases bv_extract_support_and_true hFirst2 with ⟨hJRef, hXRef⟩
  have hJRefEq := bv_extract_support_eq_true hJRef
  have hXRefEq := bv_extract_support_eq_true hXRef
  have hImRefEq := bv_extract_support_eq_true hImRef
  have hIRef1Eq := bv_extract_support_eq_true hIRef1
  have hIRef2Eq := bv_extract_support_eq_true hIRef2
  subst jRef
  subst xRef
  subst imRef
  subst iRef1
  subst iRef2
  refine ⟨hP1, hP2, hP3, ?_⟩
  rw [hP1, hP2, hP3]
  exact bv_eq_extract_elim3_program_canonical x y i j im
    hX hY hI hJ hIm

theorem typed_bv_eq_extract_elim3_program
    (x y i j im P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation im ->
    __eo_typeof (bvEqExtractElim3Program x y i j im P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvEqExtractElim3Program x y i j im P1 P2 P3) := by
  intro hXTrans hYTrans hITrans hJTrans hImTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bv_eq_extract_elim3_program_normalize x y i j im P1 P2 P3
      hXTrans hYTrans hITrans hJTrans hImTrans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvEqExtractElim3Term x y i j im) = Term.Bool := by
    rw [← hProgramEq]
    exact hTy
  rw [hProgramEq]
  exact typed_bv_eq_extract_elim3_term x y i j im
    hXTrans hYTrans hTermTy

theorem facts_bv_eq_extract_elim3_program
    (M : SmtModel) (hM : model_wf M)
    (x y i j im P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation im ->
    __eo_typeof (bvEqExtractElim3Program x y i j im P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M (bvEqExtractElim3Program x y i j im P1 P2 P3) true := by
  intro hXTrans hYTrans hITrans hJTrans hImTrans hTy
    hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bv_eq_extract_elim3_program_normalize x y i j im P1 P2 P3
      hXTrans hYTrans hITrans hJTrans hImTrans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvEqExtractElim3Term x y i j im) = Term.Bool := by
    rw [← hProgramEq]
    exact hTy
  have hPrem1 :
      eo_interprets M (bvEqExtractElimWidthMinusOnePrem x j) true := by
    simpa [hP1] using hP1True
  have hPrem2 :
      eo_interprets M (bvEqExtractElimPredecessorPrem i im) true := by
    simpa [hP2] using hP2True
  have hPrem3 : eo_interprets M (bvEqExtractElimPositivePrem i) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_eq_extract_elim3_term M hM x y i j im
    hXTrans hYTrans hTermTy hPrem1 hPrem2 hPrem3

/-! The general reconstruction rule replaces a slice strictly inside `x`. -/

def bvEqExtractElim1Slice (x j i : Term) : Term :=
  bvExtractTerm x j i

def bvEqExtractElim1LeftEq (x y i j : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvEqExtractElim1Slice x j i)) y

def bvEqExtractElim1High (x wm jp : Term) : Term :=
  bvExtractTerm x wm jp

def bvEqExtractElim1Low (x im : Term) : Term :=
  bvExtractTerm x im (Term.Numeral 0)

def bvEqExtractElim1Rebuild
    (x y wm jp im : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (bvEqExtractElim1High x wm jp))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) y)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.concat)
          (bvEqExtractElim1Low x im))
        (Term.Binary 0 0)))

def bvEqExtractElim1RightEq
    (x y wm jp im : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
    (bvEqExtractElim1Rebuild x y wm jp im)

def bvEqExtractElim1Term
    (x y i j wm jp im : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvEqExtractElim1LeftEq x y i j))
    (bvEqExtractElim1RightEq x y wm jp im)

private theorem middle_extract_eq_iff_rebuild
    (x : BitVec W) (y : BitVec D) (hFit : I + D <= W) :
    x.extractLsb' I D = y <->
      x =
        (x.extractLsb' (I + D) (W - (I + D)) ++
          (y ++ x.extractLsb' 0 I)).cast (by omega) := by
  constructor
  · intro hMiddle
    rw [← hMiddle]
    apply BitVec.eq_of_getElem_eq
    intro k hk
    simp only [BitVec.getElem_cast, BitVec.getElem_append,
      BitVec.getElem_extractLsb', Nat.zero_add]
    by_cases hBelowMiddle : k < I
    · have hBelowOuter : k < D + I := by omega
      simp only [hBelowOuter, ↓reduceDIte, hBelowMiddle]
      exact (BitVec.getLsbD_eq_getElem hk).symm
    · by_cases hBelowOuter : k < D + I
      · simp only [hBelowOuter, ↓reduceDIte, hBelowMiddle]
        rw [show I + (k - I) = k by omega,
          BitVec.getLsbD_eq_getElem hk]
      · simp only [hBelowOuter, ↓reduceDIte]
        rw [show I + D + (k - (D + I)) = k by omega,
          BitVec.getLsbD_eq_getElem hk]
  · intro hRebuild
    apply BitVec.eq_of_getElem_eq
    intro k hk
    have hFull : I + k < W := by omega
    have hBit := congrArg (fun z : BitVec W => z[I + k]'hFull) hRebuild
    have hBelowOuter : I + k < D + I := by omega
    have hNotBelowMiddle : ¬ I + k < I := by omega
    have hBit' : x[I + k] = y[k] := by
      simp only [BitVec.getElem_cast, BitVec.getElem_append,
        hBelowOuter, ↓reduceDIte, hNotBelowMiddle,
        show I + k - I = k by omega] at hBit
      exact hBit
    rw [BitVec.getElem_extractLsb' hk,
      BitVec.getLsbD_eq_getElem hFull]
    exact hBit'

private theorem eval_eq_middle_extract_eq_rebuild
    (x : BitVec W) (y : BitVec D) (hFit : I + D <= W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑D : Int)
          (↑(x.extractLsb' I D).toNat : Int))
        (SmtValue.Binary (↑D : Int) (↑y.toNat : Int)) =
      __smtx_model_eval_eq
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int)
          (↑(((x.extractLsb' (I + D) (W - (I + D)) ++
            (y ++ x.extractLsb' 0 I)).cast (by omega) :
              BitVec W).toNat) : Int)) := by
  have hIff := middle_extract_eq_iff_rebuild x y hFit
  by_cases hMiddle : x.extractLsb' I D = y
  · have hRebuild := hIff.mp hMiddle
    have hMiddleNat := congrArg BitVec.toNat hMiddle
    have hRebuildNat := congrArg BitVec.toNat hRebuild
    have hLeftValues :
        SmtValue.Binary (↑D : Int)
            (↑(x.extractLsb' I D).toNat : Int) =
          SmtValue.Binary (↑D : Int) (↑y.toNat : Int) := by
      rw [hMiddleNat]
    have hRightValues :
        SmtValue.Binary (↑W : Int) (↑x.toNat : Int) =
          SmtValue.Binary (↑W : Int)
            (↑(((x.extractLsb' (I + D) (W - (I + D)) ++
              (y ++ x.extractLsb' 0 I)).cast (by omega) :
                BitVec W).toNat) : Int) := by
      rw [hRebuildNat]
    simp only [__smtx_model_eval_eq, native_veq, hLeftValues,
      hRightValues, decide_true]
  · have hRebuild :
        x ≠
          (x.extractLsb' (I + D) (W - (I + D)) ++
            (y ++ x.extractLsb' 0 I)).cast (by omega) := by
      exact fun h => hMiddle (hIff.mpr h)
    have hMiddleNat : (x.extractLsb' I D).toNat ≠ y.toNat := by
      exact fun h => hMiddle (BitVec.eq_of_toNat_eq h)
    have hRebuildNat :
        x.toNat ≠
          ((x.extractLsb' (I + D) (W - (I + D)) ++
            (y ++ x.extractLsb' 0 I)).cast (by omega) :
              BitVec W).toNat := by
      exact fun h => hRebuild (BitVec.eq_of_toNat_eq h)
    have hLeftValues :
        SmtValue.Binary (↑D : Int)
            (↑(x.extractLsb' I D).toNat : Int) ≠
          SmtValue.Binary (↑D : Int) (↑y.toNat : Int) := by
      intro h
      injection h with _ hPayload
      exact hMiddleNat (by exact_mod_cast hPayload)
    have hRightValues :
        SmtValue.Binary (↑W : Int) (↑x.toNat : Int) ≠
          SmtValue.Binary (↑W : Int)
            (↑(((x.extractLsb' (I + D) (W - (I + D)) ++
              (y ++ x.extractLsb' 0 I)).cast (by omega) :
                BitVec W).toNat) : Int) := by
      intro h
      injection h with _ hPayload
      exact hRebuildNat (by exact_mod_cast hPayload)
    simp only [__smtx_model_eval_eq, native_veq, hLeftValues,
      hRightValues, decide_false]

private theorem bv_eq_extract_elim1_inner_types
    (x y i j wm jp im : Term) :
    __eo_typeof (bvEqExtractElim1Term x y i j wm jp im) = Term.Bool ->
    __eo_typeof (bvEqExtractElim1LeftEq x y i j) = Term.Bool ∧
      __eo_typeof (bvEqExtractElim1RightEq x y wm jp im) = Term.Bool := by
  intro hTy
  change __eo_typeof_eq
      (__eo_typeof (bvEqExtractElim1LeftEq x y i j))
      (__eo_typeof (bvEqExtractElim1RightEq x y wm jp im)) =
        Term.Bool at hTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy with
    ⟨hLeft, hRight⟩
  constructor
  · change __eo_typeof_eq
      (__eo_typeof (bvEqExtractElim1Slice x j i)) (__eo_typeof y) =
        Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck_bv_extract
    exact hLeft
  · change __eo_typeof_eq (__eo_typeof x)
      (__eo_typeof (bvEqExtractElim1Rebuild x y wm jp im)) = Term.Bool
    apply eo_typeof_eq_bool_of_ne_stuck_bv_extract
    exact hRight

private theorem bv_eq_extract_elim1_smt_context
    (x y i j wm jp im : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim1Term x y i j wm jp im) = Term.Bool ->
    ∃ w iv sliceWidth jv hv lv highWidth mv lowWidth,
      i = Term.Numeral iv ∧ j = Term.Numeral jv ∧
      wm = Term.Numeral hv ∧ jp = Term.Numeral lv ∧
      im = Term.Numeral mv ∧
      sliceWidth =
        native_zplus (native_zplus jv 1) (native_zneg iv) ∧
      highWidth =
        native_zplus (native_zplus hv 1) (native_zneg lv) ∧
      lowWidth =
        native_zplus (native_zplus mv 1) (native_zneg 0) ∧
      native_zleq 0 w = true ∧ native_zleq 0 iv = true ∧
      native_zlt jv w = true ∧ native_zleq 0 sliceWidth = true ∧
      native_zleq 0 lv = true ∧ native_zlt hv w = true ∧
      native_zleq 0 highWidth = true ∧ native_zlt mv w = true ∧
      native_zleq 0 lowWidth = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim1Slice x j i)) =
        SmtType.BitVec (native_int_to_nat sliceWidth) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat sliceWidth) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim1High x wm jp)) =
        SmtType.BitVec (native_int_to_nat highWidth) ∧
      __smtx_typeof (__eo_to_smt (bvEqExtractElim1Low x im)) =
        SmtType.BitVec (native_int_to_nat lowWidth) ∧
      __smtx_typeof
          (__eo_to_smt (bvEqExtractElim1Rebuild x y wm jp im)) =
        __smtx_typeof (__eo_to_smt x) := by
  intro hXTrans hYTrans hTy
  rcases bv_eq_extract_elim1_inner_types x y i j wm jp im hTy with
    ⟨hLeftTy, hRightTy⟩
  have hLeftOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLeftTy
  have hSliceNe :
      __eo_typeof (bvEqExtractElim1Slice x j i) ≠ Term.Stuck :=
    hLeftOps.1
  rcases bv_extract_context_of_non_stuck x j i hXTrans hSliceNe with
    ⟨w, jv, iv, _hXTy, hJ, hI, hw0, hiv0, hjvw,
      hSliceWidth0, hXSmtTy⟩
  let sliceWidth := native_zplus (native_zplus jv 1) (native_zneg iv)
  have hSliceSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim1Slice x j i)) =
        SmtType.BitVec (native_int_to_nat sliceWidth) := by
    rw [hJ, hI]
    exact smt_typeof_extract_of_context x w jv iv hXSmtTy hw0 hiv0
      hjvw hSliceWidth0
  have hSliceTrans :
      RuleProofs.eo_has_smt_translation (bvEqExtractElim1Slice x j i) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hSliceSmtTy]
    intro h
    cases h
  have hLeftEoEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLeftTy
  have hSliceBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvEqExtractElim1Slice x j i)
      (__eo_typeof (bvEqExtractElim1Slice x j i))
      (__eo_to_smt (bvEqExtractElim1Slice x j i)) rfl hSliceTrans rfl
  have hYBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y (__eo_typeof y) (__eo_to_smt y) rfl hYTrans rfl
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat sliceWidth) := by
    rw [hYBridge, ← hLeftEoEq, ← hSliceBridge]
    exact hSliceSmtTy
  have hRightOps :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRightTy
  have hRebuildNe :
      __eo_typeof (bvEqExtractElim1Rebuild x y wm jp im) ≠ Term.Stuck :=
    hRightOps.2
  let lowWithEmpty :=
    Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvEqExtractElim1Low x im))
      (Term.Binary 0 0)
  let middleWithLow :=
    Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) lowWithEmpty
  have hOuterConcatNe :
      __eo_typeof_concat (__eo_typeof (bvEqExtractElim1High x wm jp))
          (__eo_typeof middleWithLow) ≠ Term.Stuck := by
    exact hRebuildNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract
      hOuterConcatNe with
    ⟨_highWidthTerm, _middleWidthTerm, hHighEo, hMiddleEo⟩
  have hHighNe :
      __eo_typeof (bvEqExtractElim1High x wm jp) ≠ Term.Stuck := by
    rw [hHighEo]
    intro h
    cases h
  have hMiddleNe : __eo_typeof middleWithLow ≠ Term.Stuck := by
    rw [hMiddleEo]
    intro h
    cases h
  have hMiddleConcatNe :
      __eo_typeof_concat (__eo_typeof y) (__eo_typeof lowWithEmpty) ≠
        Term.Stuck := by
    exact hMiddleNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract
      hMiddleConcatNe with
    ⟨_yWidthTerm, _lowWithEmptyWidthTerm, _hYEo, hLowWithEmptyEo⟩
  have hLowWithEmptyNe :
      __eo_typeof lowWithEmpty ≠ Term.Stuck := by
    rw [hLowWithEmptyEo]
    intro h
    cases h
  have hLowConcatNe :
      __eo_typeof_concat (__eo_typeof (bvEqExtractElim1Low x im))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    exact hLowWithEmptyNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_bv_extract
      hLowConcatNe with
    ⟨_lowWidthTerm, _emptyWidthTerm, hLowEo, _hEmptyEo⟩
  have hLowNe :
      __eo_typeof (bvEqExtractElim1Low x im) ≠ Term.Stuck := by
    rw [hLowEo]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x wm jp hXTrans hHighNe with
    ⟨wHigh, hv, lv, _hXTyHigh, hWm, hJp, hwHigh0, hlv0, hhvw,
      hHighWidth0, hXSmtTyHigh⟩
  have hHighWidthNat :
      native_int_to_nat w = native_int_to_nat wHigh := by
    rw [hXSmtTy] at hXSmtTyHigh
    simpa using hXSmtTyHigh
  have hwHighEq : wHigh = w :=
    nonneg_int_eq_of_toNat_eq wHigh w hwHigh0 hw0 hHighWidthNat.symm
  rw [hwHighEq] at hhvw
  let highWidth := native_zplus (native_zplus hv 1) (native_zneg lv)
  have hHighSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim1High x wm jp)) =
        SmtType.BitVec (native_int_to_nat highWidth) := by
    rw [hWm, hJp]
    exact smt_typeof_extract_of_context x w hv lv hXSmtTy hw0 hlv0
      hhvw hHighWidth0
  rcases bv_extract_context_of_non_stuck x im (Term.Numeral 0)
      hXTrans hLowNe with
    ⟨wLow, mv, zero, _hXTyLow, hIm, hZero, hwLow0, hzero0,
      hmvw, hLowWidth0, hXSmtTyLow⟩
  have hZeroEq : zero = 0 := by
    simpa using congrArg (fun t => match t with
      | Term.Numeral n => n
      | _ => 0) hZero.symm
  subst zero
  have hLowWidthNat :
      native_int_to_nat w = native_int_to_nat wLow := by
    rw [hXSmtTy] at hXSmtTyLow
    simpa using hXSmtTyLow
  have hwLowEq : wLow = w :=
    nonneg_int_eq_of_toNat_eq wLow w hwLow0 hw0 hLowWidthNat.symm
  rw [hwLowEq] at hmvw
  let lowWidth := native_zplus (native_zplus mv 1) (native_zneg 0)
  have hLowSmtTy :
      __smtx_typeof (__eo_to_smt (bvEqExtractElim1Low x im)) =
        SmtType.BitVec (native_int_to_nat lowWidth) := by
    rw [hIm]
    exact smt_typeof_extract_of_context x w mv 0 hXSmtTy hw0 hzero0
      hmvw hLowWidth0
  have hEmptyTy :
      __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 := by
    rfl
  have hLowWithEmptySmtTy := smt_typeof_concat_bitvec_extract
    (bvEqExtractElim1Low x im) (Term.Binary 0 0)
    (native_int_to_nat lowWidth) 0 hLowSmtTy hEmptyTy
  have hMiddleSmtTy := smt_typeof_concat_bitvec_extract y lowWithEmpty
    (native_int_to_nat sliceWidth)
    (native_int_to_nat
      (native_zplus (native_nat_to_int (native_int_to_nat lowWidth))
        (native_nat_to_int 0)))
    hYSmtTy (by simpa [lowWithEmpty] using hLowWithEmptySmtTy)
  have hRebuildSmtTy := smt_typeof_concat_bitvec_extract
    (bvEqExtractElim1High x wm jp) middleWithLow
    (native_int_to_nat highWidth)
    (native_int_to_nat
      (native_zplus (native_nat_to_int (native_int_to_nat sliceWidth))
        (native_nat_to_int
          (native_int_to_nat
            (native_zplus
              (native_nat_to_int (native_int_to_nat lowWidth))
              (native_nat_to_int 0))))))
    hHighSmtTy (by simpa [middleWithLow] using hMiddleSmtTy)
  have hRebuildTrans :
      RuleProofs.eo_has_smt_translation
        (bvEqExtractElim1Rebuild x y wm jp im) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof
          (__eo_to_smt (bvEqExtractElim1Rebuild x y wm jp im)) = _ by
      simpa [bvEqExtractElim1Rebuild, middleWithLow, lowWithEmpty] using
        hRebuildSmtTy]
    intro h
    cases h
  have hRightEoEq :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hRightTy
  have hXBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x (__eo_typeof x) (__eo_to_smt x) rfl hXTrans rfl
  have hRebuildBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvEqExtractElim1Rebuild x y wm jp im)
      (__eo_typeof (bvEqExtractElim1Rebuild x y wm jp im))
      (__eo_to_smt (bvEqExtractElim1Rebuild x y wm jp im)) rfl
      hRebuildTrans rfl
  have hRebuildSame :
      __smtx_typeof
          (__eo_to_smt (bvEqExtractElim1Rebuild x y wm jp im)) =
        __smtx_typeof (__eo_to_smt x) := by
    rw [hRebuildBridge, ← hRightEoEq, ← hXBridge]
  exact ⟨w, iv, sliceWidth, jv, hv, lv, highWidth, mv, lowWidth,
    hI, hJ, hWm, hJp, hIm, rfl, rfl, rfl, hw0, hiv0, hjvw,
    native_zleq_of_zlt_true _ _ hSliceWidth0, hlv0, hhvw,
    native_zleq_of_zlt_true _ _ hHighWidth0, hmvw,
    native_zleq_of_zlt_true _ _ hLowWidth0,
    hXSmtTy, hSliceSmtTy, hYSmtTy, hHighSmtTy, hLowSmtTy,
    hRebuildSame⟩

theorem typed_bv_eq_extract_elim1_term
    (x y i j wm jp im : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim1Term x y i j wm jp im) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvEqExtractElim1Term x y i j wm jp im) := by
  intro hXTrans hYTrans hTy
  rcases bv_eq_extract_elim1_smt_context x y i j wm jp im
      hXTrans hYTrans hTy with
    ⟨w, iv, sliceWidth, jv, hv, lv, highWidth, mv, lowWidth,
      rfl, rfl, rfl, rfl, rfl, _hSliceDef, _hHighDef, _hLowDef,
      hw0, hiv0, hjvw, hSliceWidth0, hlv0, hhvw, hHighWidth0,
      hmvw, hLowWidth0, hXSmtTy, hSliceTy, hYSmtTy, hHighSmtTy,
      hLowSmtTy, hRebuildSame⟩
  have hLeftBool :
      RuleProofs.eo_has_bool_type
        (bvEqExtractElim1LeftEq x y (Term.Numeral iv)
          (Term.Numeral jv)) := by
    unfold bvEqExtractElim1LeftEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hSliceTy.trans hYSmtTy.symm) (by rw [hSliceTy]; simp)
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (bvEqExtractElim1RightEq x y (Term.Numeral hv)
          (Term.Numeral lv) (Term.Numeral mv)) := by
    unfold bvEqExtractElim1RightEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      hRebuildSame.symm (by rw [hXSmtTy]; simp)
  unfold bvEqExtractElim1Term
  have hLeftSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim1LeftEq x y (Term.Numeral iv)
              (Term.Numeral jv))) = SmtType.Bool := hLeftBool
  have hRightSmt :
      __smtx_typeof
          (__eo_to_smt
            (bvEqExtractElim1RightEq x y (Term.Numeral hv)
              (Term.Numeral lv) (Term.Numeral mv))) = SmtType.Bool :=
    hRightBool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftSmt.trans hRightSmt.symm) (by rw [hLeftSmt]; simp)

private theorem bv_eq_extract_elim1_premises_numeric
    (M : SmtModel) (x : Term)
    (w iv jv hv lv mv : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    eo_interprets M
      (bvEqExtractElimWidthMinusOnePrem x (Term.Numeral hv)) true ->
    eo_interprets M
      (bvEqExtractElimSuccessorPrem (Term.Numeral jv)
        (Term.Numeral lv)) true ->
    eo_interprets M
      (bvEqExtractElimPredecessorPrem (Term.Numeral iv)
        (Term.Numeral mv)) true ->
    eo_interprets M
      (bvEqExtractElimHighRoomPrem (Term.Numeral hv)
        (Term.Numeral jv)) true ->
    eo_interprets M
      (bvEqExtractElimPositivePrem (Term.Numeral iv)) true ->
    hv = native_zplus w (native_zneg 1) ∧
      lv = native_zplus jv 1 ∧
      mv = native_zplus iv (native_zneg 1) ∧
      native_zlt jv hv = true ∧ native_zlt 0 iv = true := by
  intro hw0 hXTy hWidthPrem hSuccPrem hPredPrem hRoomPrem hPositivePrem
  rcases bv_eq_extract_elim2_premises_numeric M x w jv hv lv hw0 hXTy
      hWidthPrem hSuccPrem hRoomPrem with
    ⟨hHv, hLv, hRoom⟩
  rcases bv_eq_extract_elim3_premises_numeric M x w iv hv mv hw0 hXTy
      hWidthPrem hPredPrem hPositivePrem with
    ⟨_hHv, hMv, hPositive⟩
  exact ⟨hHv, hLv, hMv, hRoom, hPositive⟩

theorem facts_bv_eq_extract_elim1_term
    (M : SmtModel) (hM : model_wf M)
    (x y i j wm jp im : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvEqExtractElim1Term x y i j wm jp im) = Term.Bool ->
    eo_interprets M (bvEqExtractElimWidthMinusOnePrem x wm) true ->
    eo_interprets M (bvEqExtractElimSuccessorPrem j jp) true ->
    eo_interprets M (bvEqExtractElimPredecessorPrem i im) true ->
    eo_interprets M (bvEqExtractElimHighRoomPrem wm j) true ->
    eo_interprets M (bvEqExtractElimPositivePrem i) true ->
    eo_interprets M (bvEqExtractElim1Term x y i j wm jp im) true := by
  intro hXTrans hYTrans hTy hWidthPrem hSuccPrem hPredPrem hRoomPrem
    hPositivePrem
  rcases bv_eq_extract_elim1_smt_context x y i j wm jp im
      hXTrans hYTrans hTy with
    ⟨w, iv, sliceWidth, jv, hv, lv, highWidth, mv, lowWidth,
      rfl, rfl, rfl, rfl, rfl, hSliceDef, hHighDef, hLowDef,
      hw0, hiv0, hjvw, hSliceWidth0, _hlv0, _hhvw,
      _hHighWidth0, _hmvw, _hLowWidth0, hXSmtTy, _hSliceSmtTy,
      hYSmtTy, _hHighSmtTy, _hLowSmtTy, _hRebuildSame⟩
  rcases bv_eq_extract_elim1_premises_numeric M x w iv jv hv lv mv
      hw0 hXSmtTy hWidthPrem hSuccPrem hPredPrem hRoomPrem
      hPositivePrem with
    ⟨hHv, hLv, hMv, _hRoom, _hPositive⟩
  subst hv
  subst lv
  subst mv
  let W : Nat := native_int_to_nat w
  let I : Nat := native_int_to_nat iv
  let D : Nat := native_int_to_nat sliceWidth
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hIRound : (↑I : Int) = iv := by
    simpa [I, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip iv hiv0
  have hDRound : (↑D : Int) = sliceWidth := by
    simpa [D, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip sliceWidth hSliceWidth0
  have hEndRound : (↑(I + D) : Int) = jv + 1 := by
    rw [show (↑(I + D) : Int) = (↑I : Int) + (↑D : Int) by
      norm_cast, hIRound, hDRound, hSliceDef]
    change iv + (jv + 1 + -iv) = jv + 1
    calc
      iv + (jv + 1 + -iv) = (iv + (jv + 1)) + -iv :=
        (Int.add_assoc iv (jv + 1) (-iv)).symm
      _ = ((jv + 1) + iv) + -iv := by
        rw [Int.add_comm iv (jv + 1)]
      _ = jv + 1 := Int.add_neg_cancel_right (jv + 1) iv
  have hjwInt : jv < w := by
    simpa [SmtEval.native_zlt] using hjvw
  have hFitInt : (↑(I + D) : Int) ≤ (↑W : Int) := by
    rw [hEndRound, hWRound]
    exact Int.add_one_le_iff.mpr hjwInt
  have hFit : I + D ≤ W := by
    exact_mod_cast hFitInt
  have hHighCast :
      (↑(W - (I + D)) : Int) = w - (jv + 1) := by
    omega
  have hYSmtTyNat :
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec D := by
    simpa [D] using hYSmtTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with
    ⟨p, hXEval0, hPCanonical⟩
  have hXEval :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) p := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hXEval0
  have hWNat0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hPRange := bitvec_payload_range_of_canonical hWNat0 hPCanonical
  have hp0 : (0 : Int) ≤ p := hPRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hPRange.2
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt y) D
      hYSmtTyNat with
    ⟨q, hYEval0, hQCanonical⟩
  have hYEval :
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (↑D : Int) q := by
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hYEval0
  have hDNat0 : native_zleq 0 (native_nat_to_int D) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      Smtm.native_nat_to_int]
  have hQRange := bitvec_payload_range_of_canonical hDNat0 hQCanonical
  have hq0 : (0 : Int) ≤ q := hQRange.1
  have hq1 : q < (2 : Int) ^ D := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hQRange.2
  let X : BitVec W := BitVec.ofInt W p
  let Y : BitVec D := BitVec.ofInt D q
  have hXPayload : (↑X.toNat : Int) = p := by
    have hToNat : X.toNat = p.toNat := by
      simpa [X] using ofInt_toNat_canonical W p hp0 hp1
    rw [hToNat]
    exact Int.toNat_of_nonneg hp0
  have hYPayload : (↑Y.toNat : Int) = q := by
    have hToNat : Y.toNat = q.toNat := by
      simpa [Y] using ofInt_toNat_canonical D q hq0 hq1
    rw [hToNat]
    exact Int.toNat_of_nonneg hq0
  have hXEvalBitVec :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) (↑X.toNat : Int) := by
    rw [hXEval, hXPayload]
  have hYEvalBitVec :
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (↑D : Int) (↑Y.toNat : Int) := by
    rw [hYEval, hYPayload]
  have hMiddleLen : jv + 1 + -iv = (↑D : Int) := by
    rw [hDRound, hSliceDef]
    rfl
  have hMiddleEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1Slice x (Term.Numeral jv)
              (Term.Numeral iv))) =
        SmtValue.Binary (↑D : Int)
          (↑(X.extractLsb' I D).toNat : Int) := by
    rw [show bvEqExtractElim1Slice x (Term.Numeral jv)
          (Term.Numeral iv) =
        bvExtractTerm x (Term.Numeral jv) (Term.Numeral iv) by rfl,
      eval_extract_term, hXEval]
    simpa [X] using
      (extract_val_bitvec_start_len W I D p jv iv hp0 hp1
        hIRound.symm hMiddleLen)
  have hHighLen :
      native_zplus w (native_zneg 1) + 1 + -(jv + 1) =
        (↑(W - (I + D)) : Int) := by
    rw [hHighCast]
    change w + (-1 : Int) + 1 + -(jv + 1) = w - (jv + 1)
    have hCancel : w + (-1 : Int) + 1 = w := by
      calc
        w + (-1 : Int) + 1 = w + ((-1 : Int) + 1) :=
          Int.add_assoc w (-1) 1
        _ = w := by simp
    rw [hCancel]
    rfl
  have hHighEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1High x
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral (native_zplus jv 1)))) =
        SmtValue.Binary (↑(W - (I + D)) : Int)
          (↑(X.extractLsb' (I + D) (W - (I + D))).toNat : Int) := by
    rw [show bvEqExtractElim1High x
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus jv 1)) =
        bvExtractTerm x
          (Term.Numeral (native_zplus w (native_zneg 1)))
          (Term.Numeral (native_zplus jv 1)) by rfl,
      eval_extract_term, hXEval]
    simpa [X, SmtEval.native_zplus] using
      (extract_val_bitvec_start_len W (I + D) (W - (I + D)) p
        (native_zplus w (native_zneg 1)) (native_zplus jv 1)
        hp0 hp1 hEndRound.symm hHighLen)
  have hLowLen :
      native_zplus iv (native_zneg 1) + 1 + -(0 : Int) =
        (↑I : Int) := by
    rw [hIRound]
    change iv + (-1 : Int) + 1 + -(0 : Int) = iv
    have hCancel : iv + (-1 : Int) + 1 = iv := by
      calc
        iv + (-1 : Int) + 1 = iv + ((-1 : Int) + 1) :=
          Int.add_assoc iv (-1) 1
        _ = iv := by simp
    simpa using hCancel
  have hLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1Low x
              (Term.Numeral (native_zplus iv (native_zneg 1))))) =
        SmtValue.Binary (↑I : Int)
          (↑(X.extractLsb' 0 I).toNat : Int) := by
    rw [show bvEqExtractElim1Low x
          (Term.Numeral (native_zplus iv (native_zneg 1))) =
        bvExtractTerm x
          (Term.Numeral (native_zplus iv (native_zneg 1)))
          (Term.Numeral 0) by rfl,
      eval_extract_term, hXEval]
    simpa [X] using
      (extract_val_bitvec_start_len W 0 I p
        (native_zplus iv (native_zneg 1)) 0 hp0 hp1 rfl hLowLen)
  have hLowWithEmptyEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.concat)
                (bvEqExtractElim1Low x
                  (Term.Numeral (native_zplus iv (native_zneg 1)))))
              (Term.Binary 0 0))) =
        SmtValue.Binary (↑I : Int)
          (↑(X.extractLsb' 0 I).toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat
          (__eo_to_smt
            (bvEqExtractElim1Low x
              (Term.Numeral (native_zplus iv (native_zneg 1)))))
          (__eo_to_smt (Term.Binary 0 0))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hLowEval]
    change __smtx_model_eval_concat
        (SmtValue.Binary (↑I : Int)
          (↑(X.extractLsb' 0 I).toNat : Int))
        (SmtValue.Binary 0 0) = _
    exact concat_empty_bv_eq_extract_elim_value (X.extractLsb' 0 I)
  have hYWithLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.concat)
                  (bvEqExtractElim1Low x
                    (Term.Numeral (native_zplus iv (native_zneg 1)))))
                (Term.Binary 0 0)))) =
        SmtValue.Binary (↑(D + I) : Int)
          (↑(Y ++ X.extractLsb' 0 I).toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt y)
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.concat)
                (bvEqExtractElim1Low x
                  (Term.Numeral (native_zplus iv (native_zneg 1)))))
              (Term.Binary 0 0)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hYEvalBitVec, hLowWithEmptyEval,
      concat_bv_eq_extract_elim_values]
  let R : BitVec W :=
    (X.extractLsb' (I + D) (W - (I + D)) ++
      (Y ++ X.extractLsb' 0 I)).cast (by omega)
  have hRebuildEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1Rebuild x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral (native_zplus jv 1))
              (Term.Numeral (native_zplus iv (native_zneg 1))))) =
        SmtValue.Binary (↑W : Int) (↑R.toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.concat
          (__eo_to_smt
            (bvEqExtractElim1High x
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral (native_zplus jv 1))))
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.concat)
                  (bvEqExtractElim1Low x
                    (Term.Numeral (native_zplus iv (native_zneg 1)))))
                (Term.Binary 0 0))))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hHighEval, hYWithLowEval,
      concat_bv_eq_extract_elim_values]
    simpa [R, Nat.add_comm D I, Nat.sub_add_cancel hFit]
  have hLeftEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1LeftEq x y (Term.Numeral iv)
              (Term.Numeral jv))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑D : Int)
            (↑(X.extractLsb' I D).toNat : Int))
          (SmtValue.Binary (↑D : Int) (↑Y.toNat : Int)) := by
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvEqExtractElim1Slice x (Term.Numeral jv)
              (Term.Numeral iv)))
          (__eo_to_smt y)) = _
    rw [smtx_eval_eq_term_eq, hMiddleEval, hYEvalBitVec]
  have hRightEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1RightEq x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral (native_zplus jv 1))
              (Term.Numeral (native_zplus iv (native_zneg 1))))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑W : Int) (↑X.toNat : Int))
          (SmtValue.Binary (↑W : Int) (↑R.toNat : Int)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x)
          (__eo_to_smt
            (bvEqExtractElim1Rebuild x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral (native_zplus jv 1))
              (Term.Numeral (native_zplus iv (native_zneg 1)))))) = _
    rw [smtx_eval_eq_term_eq, hXEvalBitVec, hRebuildEval]
  have hInnerEqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1LeftEq x y (Term.Numeral iv)
              (Term.Numeral jv))) =
        __smtx_model_eval M
          (__eo_to_smt
            (bvEqExtractElim1RightEq x y
              (Term.Numeral (native_zplus w (native_zneg 1)))
              (Term.Numeral (native_zplus jv 1))
              (Term.Numeral (native_zplus iv (native_zneg 1))))) := by
    rw [hLeftEqEval, hRightEqEval]
    simpa [R] using eval_eq_middle_extract_eq_rebuild X Y hFit
  have hBool := typed_bv_eq_extract_elim1_term x y
    (Term.Numeral iv) (Term.Numeral jv)
    (Term.Numeral (native_zplus w (native_zneg 1)))
    (Term.Numeral (native_zplus jv 1))
    (Term.Numeral (native_zplus iv (native_zneg 1)))
    hXTrans hYTrans hTy
  unfold bvEqExtractElim1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvEqExtractElim1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvEqExtractElim1LeftEq x y (Term.Numeral iv)
            (Term.Numeral jv))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvEqExtractElim1RightEq x y
            (Term.Numeral (native_zplus w (native_zneg 1)))
            (Term.Numeral (native_zplus jv 1))
            (Term.Numeral (native_zplus iv (native_zneg 1))))))
    rw [hInnerEqEval]
    exact RuleProofs.smt_value_rel_refl _

def bvEqExtractElim1Program
    (x y i j wm jp im P1 P2 P3 P4 P5 : Term) : Term :=
  __eo_prog_bv_eq_extract_elim1 x y i j wm jp im
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
    (Proof.pf P5)

private theorem bv_eq_extract_elim1_premise_shape
    (x y i j wm jp im P1 P2 P3 P4 P5 : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> i ≠ Term.Stuck ->
    j ≠ Term.Stuck -> wm ≠ Term.Stuck -> jp ≠ Term.Stuck ->
    im ≠ Term.Stuck ->
    bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5 ≠
      Term.Stuck ->
    ∃ wmRef1 xRef jpRef jRef1 imRef iRef1 wmRef2 jRef2 iRef2,
      P1 = bvEqExtractElimWidthMinusOnePrem xRef wmRef1 ∧
      P2 = bvEqExtractElimSuccessorPrem jRef1 jpRef ∧
      P3 = bvEqExtractElimPredecessorPrem iRef1 imRef ∧
      P4 = bvEqExtractElimHighRoomPrem wmRef2 jRef2 ∧
      P5 = bvEqExtractElimPositivePrem iRef2 := by
  intro hX hY hI hJ hWm hJp hIm hProg
  by_cases hShape :
      ∃ wmRef1 xRef jpRef jRef1 imRef iRef1 wmRef2 jRef2 iRef2,
        P1 = bvEqExtractElimWidthMinusOnePrem xRef wmRef1 ∧
        P2 = bvEqExtractElimSuccessorPrem jRef1 jpRef ∧
        P3 = bvEqExtractElimPredecessorPrem iRef1 imRef ∧
        P4 = bvEqExtractElimHighRoomPrem wmRef2 jRef2 ∧
        P5 = bvEqExtractElimPositivePrem iRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_eq_extract_elim1.eq_9
      x y i j wm jp im (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      (Proof.pf P4) (Proof.pf P5) hX hY hI hJ hWm hJp hIm (by
        intro wmRef1 xRef jpRef jRef1 imRef iRef1 wmRef2 jRef2 iRef2
          hP1 hP2 hP3 hP4 hP5
        cases hP1
        cases hP2
        cases hP3
        cases hP4
        cases hP5
        exact hShape ⟨wmRef1, xRef, jpRef, jRef1, imRef, iRef1,
          wmRef2, jRef2, iRef2, rfl, rfl, rfl, rfl, rfl⟩)

private theorem bv_eq_extract_elim1_program_canonical
    (x y i j wm jp im : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> i ≠ Term.Stuck ->
    j ≠ Term.Stuck -> wm ≠ Term.Stuck -> jp ≠ Term.Stuck ->
    im ≠ Term.Stuck ->
    bvEqExtractElim1Program x y i j wm jp im
        (bvEqExtractElimWidthMinusOnePrem x wm)
        (bvEqExtractElimSuccessorPrem j jp)
        (bvEqExtractElimPredecessorPrem i im)
        (bvEqExtractElimHighRoomPrem wm j)
        (bvEqExtractElimPositivePrem i) =
      bvEqExtractElim1Term x y i j wm jp im := by
  intro hX hY hI hJ hWm hJp hIm
  unfold bvEqExtractElim1Program bvEqExtractElimWidthMinusOnePrem
    bvEqExtractElimSuccessorPrem bvEqExtractElimPredecessorPrem
    bvEqExtractElimHighRoomPrem bvEqExtractElimPositivePrem
  rw [__eo_prog_bv_eq_extract_elim1.eq_8
    x y i j wm jp im wm x jp j im i wm j i
    hX hY hI hJ hWm hJp hIm]
  simp [bvEqExtractElim1Term, bvEqExtractElim1LeftEq,
    bvEqExtractElim1RightEq, bvEqExtractElim1Rebuild,
    bvEqExtractElim1High, bvEqExtractElim1Low,
    bvEqExtractElim1Slice, bvExtractTerm, __eo_requires, __eo_and,
    __eo_eq, native_ite, native_teq, native_not, native_and,
    hX, hY, hI, hJ, hWm, hJp, hIm]

private theorem bv_eq_extract_elim1_program_normalize
    (x y i j wm jp im P1 P2 P3 P4 P5 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation wm ->
    RuleProofs.eo_has_smt_translation jp ->
    RuleProofs.eo_has_smt_translation im ->
    bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5 ≠
      Term.Stuck ->
    P1 = bvEqExtractElimWidthMinusOnePrem x wm ∧
      P2 = bvEqExtractElimSuccessorPrem j jp ∧
      P3 = bvEqExtractElimPredecessorPrem i im ∧
      P4 = bvEqExtractElimHighRoomPrem wm j ∧
      P5 = bvEqExtractElimPositivePrem i ∧
      bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5 =
        bvEqExtractElim1Term x y i j wm jp im := by
  intro hXTrans hYTrans hITrans hJTrans hWmTrans hJpTrans hImTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hY := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hI := RuleProofs.term_ne_stuck_of_has_smt_translation i hITrans
  have hJ := RuleProofs.term_ne_stuck_of_has_smt_translation j hJTrans
  have hWm := RuleProofs.term_ne_stuck_of_has_smt_translation wm hWmTrans
  have hJp := RuleProofs.term_ne_stuck_of_has_smt_translation jp hJpTrans
  have hIm := RuleProofs.term_ne_stuck_of_has_smt_translation im hImTrans
  rcases bv_eq_extract_elim1_premise_shape x y i j wm jp im
      P1 P2 P3 P4 P5 hX hY hI hJ hWm hJp hIm hProg with
    ⟨wmRef1, xRef, jpRef, jRef1, imRef, iRef1, wmRef2, jRef2,
      iRef2, hP1, hP2, hP3, hP4, hP5⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4, hP5] at hReq
  unfold bvEqExtractElim1Program bvEqExtractElimWidthMinusOnePrem
    bvEqExtractElimSuccessorPrem bvEqExtractElimPredecessorPrem
    bvEqExtractElimHighRoomPrem bvEqExtractElimPositivePrem at hReq
  rw [__eo_prog_bv_eq_extract_elim1.eq_8
    x y i j wm jp im wmRef1 xRef jpRef jRef1 imRef iRef1
    wmRef2 jRef2 iRef2 hX hY hI hJ hWm hJp hIm] at hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hFirst8, hIRef2⟩
  rcases bv_extract_support_and_true hFirst8 with ⟨hFirst7, hJRef2⟩
  rcases bv_extract_support_and_true hFirst7 with ⟨hFirst6, hWmRef2⟩
  rcases bv_extract_support_and_true hFirst6 with ⟨hFirst5, hIRef1⟩
  rcases bv_extract_support_and_true hFirst5 with ⟨hFirst4, hImRef⟩
  rcases bv_extract_support_and_true hFirst4 with ⟨hFirst3, hJRef1⟩
  rcases bv_extract_support_and_true hFirst3 with ⟨hFirst2, hJpRef⟩
  rcases bv_extract_support_and_true hFirst2 with ⟨hWmRef1, hXRef⟩
  have hWmRef1Eq := bv_extract_support_eq_true hWmRef1
  have hXRefEq := bv_extract_support_eq_true hXRef
  have hJpRefEq := bv_extract_support_eq_true hJpRef
  have hJRef1Eq := bv_extract_support_eq_true hJRef1
  have hImRefEq := bv_extract_support_eq_true hImRef
  have hIRef1Eq := bv_extract_support_eq_true hIRef1
  have hWmRef2Eq := bv_extract_support_eq_true hWmRef2
  have hJRef2Eq := bv_extract_support_eq_true hJRef2
  have hIRef2Eq := bv_extract_support_eq_true hIRef2
  subst wmRef1
  subst xRef
  subst jpRef
  subst jRef1
  subst imRef
  subst iRef1
  subst wmRef2
  subst jRef2
  subst iRef2
  refine ⟨hP1, hP2, hP3, hP4, hP5, ?_⟩
  rw [hP1, hP2, hP3, hP4, hP5]
  exact bv_eq_extract_elim1_program_canonical x y i j wm jp im
    hX hY hI hJ hWm hJp hIm

theorem typed_bv_eq_extract_elim1_program
    (x y i j wm jp im P1 P2 P3 P4 P5 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation wm ->
    RuleProofs.eo_has_smt_translation jp ->
    RuleProofs.eo_has_smt_translation im ->
    __eo_typeof
        (bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5) := by
  intro hXTrans hYTrans hITrans hJTrans hWmTrans hJpTrans hImTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bv_eq_extract_elim1_program_normalize x y i j wm jp im
      P1 P2 P3 P4 P5 hXTrans hYTrans hITrans hJTrans hWmTrans
      hJpTrans hImTrans hProg with
    ⟨_hP1, _hP2, _hP3, _hP4, _hP5, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvEqExtractElim1Term x y i j wm jp im) = Term.Bool := by
    rw [← hProgramEq]
    exact hTy
  rw [hProgramEq]
  exact typed_bv_eq_extract_elim1_term x y i j wm jp im
    hXTrans hYTrans hTermTy

theorem facts_bv_eq_extract_elim1_program
    (M : SmtModel) (hM : model_wf M)
    (x y i j wm jp im P1 P2 P3 P4 P5 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation i ->
    RuleProofs.eo_has_smt_translation j ->
    RuleProofs.eo_has_smt_translation wm ->
    RuleProofs.eo_has_smt_translation jp ->
    RuleProofs.eo_has_smt_translation im ->
    __eo_typeof
        (bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true -> eo_interprets M P4 true ->
    eo_interprets M P5 true ->
    eo_interprets M
      (bvEqExtractElim1Program x y i j wm jp im P1 P2 P3 P4 P5) true := by
  intro hXTrans hYTrans hITrans hJTrans hWmTrans hJpTrans hImTrans hTy
    hP1True hP2True hP3True hP4True hP5True
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bv_eq_extract_elim1_program_normalize x y i j wm jp im
      P1 P2 P3 P4 P5 hXTrans hYTrans hITrans hJTrans hWmTrans
      hJpTrans hImTrans hProg with
    ⟨hP1, hP2, hP3, hP4, hP5, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvEqExtractElim1Term x y i j wm jp im) = Term.Bool := by
    rw [← hProgramEq]
    exact hTy
  have hPrem1 :
      eo_interprets M (bvEqExtractElimWidthMinusOnePrem x wm) true := by
    simpa [hP1] using hP1True
  have hPrem2 :
      eo_interprets M (bvEqExtractElimSuccessorPrem j jp) true := by
    simpa [hP2] using hP2True
  have hPrem3 :
      eo_interprets M (bvEqExtractElimPredecessorPrem i im) true := by
    simpa [hP3] using hP3True
  have hPrem4 :
      eo_interprets M (bvEqExtractElimHighRoomPrem wm j) true := by
    simpa [hP4] using hP4True
  have hPrem5 : eo_interprets M (bvEqExtractElimPositivePrem i) true := by
    simpa [hP5] using hP5True
  rw [hProgramEq]
  exact facts_bv_eq_extract_elim1_term M hM x y i j wm jp im
    hXTrans hYTrans hTermTy hPrem1 hPrem2 hPrem3 hPrem4 hPrem5
