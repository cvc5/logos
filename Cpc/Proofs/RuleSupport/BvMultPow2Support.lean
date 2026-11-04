module

public import Cpc.Proofs.RuleSupport.BvDivPow2Support
import all Cpc.Proofs.RuleSupport.BvDivPow2Support
public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport
public import Cpc.Proofs.RuleSupport.BvSsuboElimSupport
import all Cpc.Proofs.RuleSupport.BvSsuboElimSupport

public section

/-! Support for the list-free multiplication-by-a-power-of-two rewrite. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvMultPow2Diff (size n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.neg)
    (Term.Apply (Term.UOp UserOp.int_pow2) size)) n

def bvMultPow2Const (size n : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv size) n

def bvMultPow2Nil (z : Term) : Term :=
  __eo_nil (Term.UOp UserOp.bvmul) (__eo_typeof z)

def bvMultPow2Lhs (z size n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) z)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
      (bvMultPow2Const size n)) (bvMultPow2Nil z))

def bvMultPow2Zeros (exponent : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat)
    (bvMultPow2Const exponent (Term.Numeral 0))) (Term.Binary 0 0)

def bvMultPow2Rhs (z exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat)
    (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
      u (Term.Numeral 0))) (bvMultPow2Zeros exponent)

def bvMultPow2Term (z size n exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvMultPow2Lhs z size n)) (bvMultPow2Rhs z exponent u)

/-- The multiplication identity without the synthetic n-ary-list identity.
    This form is usable by rules whose source already contains a nonempty
    multiplication list, including widths beyond `__eo_to_bin`'s bound. -/
def bvMultPow2DirectLhs (z size n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) z)
    (bvMultPow2Const size n)

def bvMultPow2DirectTerm (z size n exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvMultPow2DirectLhs z size n)) (bvMultPow2Rhs z exponent u)

def bvMultPow2IspowPrem (size n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (Term.Apply (Term.UOp UserOp.int_ispow2) (bvMultPow2Diff size n)))
    (Term.Boolean true)

def bvMultPow2ExponentPrem (size n exponent : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) exponent)
    (Term.Apply (Term.UOp UserOp.int_log2) (bvMultPow2Diff size n))

def bvMultPow2UpperPrem (size n u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) size)
        (Term.Apply (Term.UOp UserOp.int_log2) (bvMultPow2Diff size n))))
      (Term.Numeral 1))

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck_mult_pow2
    {A B : Term} (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    ∃ n m,
      A = Term.Apply (Term.UOp UserOp.BitVec) n ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) m := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | BitVec =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | BitVec => exact ⟨n, m, rfl, rfl⟩
                      | _ => simp [__eo_typeof_concat] at h
                  | _ => simp [__eo_typeof_concat] at h
              | _ => simp [__eo_typeof_concat] at h
          | _ => simp [__eo_typeof_concat] at h
      | _ => simp [__eo_typeof_concat] at h
  | _ => simp [__eo_typeof_concat] at h

private theorem bv_mult_pow2_context
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool ->
    ∃ W E U D : native_Int,
      size = Term.Numeral W ∧ exponent = Term.Numeral E ∧
      u = Term.Numeral U ∧
      native_zleq 0 W = true ∧ native_zleq 0 E = true ∧
      native_zleq 0 U = true ∧ native_zlt U W = true ∧
      D = native_zplus U 1 ∧ native_zlt 0 D = true ∧
      native_zplus D E = W ∧
      __eo_typeof z =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __smtx_typeof (__eo_to_smt z) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof z)
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
            (bvMultPow2Const size n)) (bvMultPow2Nil z))))
      (__eo_typeof (bvMultPow2Rhs z exponent u)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hLhsNe with
    ⟨widthTerm, hZTy, hInnerTy⟩
  have hInnerEq :
      __eo_typeof_bvand (__eo_typeof (bvMultPow2Const size n))
          (__eo_typeof (bvMultPow2Nil z)) =
        Term.Apply (Term.UOp UserOp.BitVec) widthTerm := by
    have hsimpa := hInnerTy
    try simp [bvMultPow2Lhs] at hsimpa ⊢
    exact hsimpa
  have hInnerNe :
      __eo_typeof_bvand (__eo_typeof (bvMultPow2Const size n))
          (__eo_typeof (bvMultPow2Nil z)) ≠ Term.Stuck := by
    rw [hInnerEq]
    intro h
    cases h
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hInnerNe with
    ⟨innerWidth, hConstTy, _hNilTy⟩
  have hInnerWidthNe : innerWidth ≠ Term.Stuck := by
    intro h
    apply hInnerNe
    rw [hConstTy, _hNilTy, h]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hInnerReduce :
      __eo_typeof_bvand
          (Term.Apply (Term.UOp UserOp.BitVec) innerWidth)
          (Term.Apply (Term.UOp UserOp.BitVec) innerWidth) =
        Term.Apply (Term.UOp UserOp.BitVec) innerWidth := by
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not, hInnerWidthNe]
  have hWidths : innerWidth = widthTerm := by
    rw [hConstTy, _hNilTy] at hInnerEq
    rw [hInnerReduce] at hInnerEq
    injection hInnerEq
  subst innerWidth
  have hSizeNe := RuleProofs.term_ne_stuck_of_has_smt_translation size hSizeTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  rcases bv_all_ones_const_context n size widthTerm hNNe hSizeNe
      (by simpa [bvMultPow2Const, bvAllOnesConst] using hConstTy) with
    ⟨W, hSize, hWidth, hW0, hNTy⟩
  subst widthTerm
  have hZSmtTy :
      __smtx_typeof (__eo_to_smt z) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [__eo_to_smt_type, hW0, native_ite] using
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        z (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt z) rfl hZTrans hZTy)
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNTy
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hLhsTy :
      __eo_typeof_bvand (__eo_typeof z)
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
              (bvMultPow2Const size n)) (bvMultPow2Nil z))) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hZTy, hInnerTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRhsTy :
      __eo_typeof (bvMultPow2Rhs z exponent u) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypeEq
    exact hTypeEq.symm
  change __eo_typeof_concat
      (__eo_typeof
        (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
          u (Term.Numeral 0)))
      (__eo_typeof (bvMultPow2Zeros exponent)) ≠ Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_mult_pow2 hRhsNe with
    ⟨extractWidth, zeroWidth, hExtractTy, hZerosTy⟩
  have hZerosNe : __eo_typeof (bvMultPow2Zeros exponent) ≠ Term.Stuck := by
    rw [hZerosTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof (bvMultPow2Const exponent (Term.Numeral 0)))
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck at hZerosNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_mult_pow2 hZerosNe with
    ⟨exponentWidth, _emptyWidth, hZeroConstTy, _hEmptyTy⟩
  have hExponentNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation exponent hExponentTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) exponent exponentWidth
      (by simp) hExponentNe
      (by simpa [bvMultPow2Const, bvAllOnesConst] using hZeroConstTy) with
    ⟨E, hExponent, hExponentWidth, hE0, _hZeroTy⟩
  subst exponentWidth
  rw [hExponent] at hZeroConstTy
  have hZerosEoTy :
      __eo_typeof (bvMultPow2Zeros (Term.Numeral E)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral E) := by
    change __eo_typeof_concat
        (__eo_typeof (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0)))
        (__eo_typeof (Term.Binary 0 0)) = _
    rw [hZeroConstTy]
    change __eo_typeof_concat
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral E))
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) = _
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus]
  have hZeroWidth : zeroWidth = Term.Numeral E := by
    rw [hExponent, hZerosEoTy] at hZerosTy
    injection hZerosTy with _ h
    exact h.symm
  subst zeroWidth
  have hNegSmtTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) z)) =
        SmtType.BitVec (native_int_to_nat W) :=
    smt_typeof_bvneg_same (__eo_to_smt z) (native_int_to_nat W) hZSmtTy
  have hNegTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.bvneg) z) := by
    intro h
    rw [h] at hNegSmtTy
    cases hNegSmtTy
  have hExtractNe :
      __eo_typeof
          (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
            u (Term.Numeral 0)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (Term.Apply (Term.UOp UserOp.bvneg) z) u (Term.Numeral 0)
      hNegTrans hExtractNe with
    ⟨W', U, L, hNegTy, hU, hL, hW'0, hL0, hUW', hD0,
      hNegSmtTy'⟩
  have hWW' : W' = W := by
    rw [hNegSmtTy] at hNegSmtTy'
    have hNat := (SmtType.BitVec.inj hNegSmtTy').symm
    exact nonneg_int_eq_of_toNat_eq W' W hW'0 hW0 hNat
  subst W'
  have hLZero : L = 0 := by
    injection hL with h
    exact h.symm
  subst L
  let D := native_zplus U 1
  have hDPos : native_zlt 0 D = true := by
    simpa [D, SmtEval.native_zplus, SmtEval.native_zneg] using hD0
  have hDPosRaw : native_zlt 0 (U + 1) = true := by
    simpa [D, SmtEval.native_zplus] using hDPos
  have hExtractEoTy :
      __eo_typeof
          (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
            (Term.Numeral U) (Term.Numeral 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    have hGtZero : native_zlt (-1 : native_Int) 0 = true := by decide
    have hGtD : native_zlt (-1 : native_Int) D = true := by
      have hDInt : (0 : Int) < D := by
        simpa [SmtEval.native_zlt] using hDPos
      simpa [SmtEval.native_zlt] using (show (-1 : Int) < D by omega)
    change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral U)
        (Term.UOp UserOp.Int) (Term.Numeral 0) _ = _
    rw [hNegTy]
    simp [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt,
      __eo_requires, __eo_mk_apply, native_ite, native_teq, native_not,
      hGtZero, hUW', hDPos, hDPosRaw, hGtD, D, SmtEval.native_zplus,
      SmtEval.native_zneg]
  have hExtractWidth : extractWidth = Term.Numeral D := by
    rw [hU, hExtractEoTy] at hExtractTy
    injection hExtractTy with _ h
    exact h.symm
  subst extractWidth
  have hRhsWidth : native_zplus D E = W := by
    have hRhsTy' := hRhsTy
    change __eo_typeof_concat
        (__eo_typeof
          (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
            u (Term.Numeral 0)))
        (__eo_typeof (bvMultPow2Zeros exponent)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) at hRhsTy'
    rw [hU, hExponent, hExtractEoTy, hZerosEoTy] at hRhsTy'
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus] at hRhsTy'
    exact hRhsTy'
  have hU0 : native_zleq 0 U = true := by
    have hDInt : (0 : Int) < D := by
      simpa [SmtEval.native_zlt] using hDPos
    have hUInt : (0 : Int) ≤ U := by
      simp [D, SmtEval.native_zplus] at hDInt
      omega
    simpa [SmtEval.native_zleq] using hUInt
  exact ⟨W, E, U, D, hSize, hExponent, hU, hW0, hE0, hU0,
    hUW', rfl, hDPos, hRhsWidth, hZTy, hZSmtTy, hNSmtTy⟩

private theorem bv_mult_pow2_direct_context
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2DirectTerm z size n exponent u) = Term.Bool ->
    ∃ W E U D : native_Int,
      size = Term.Numeral W ∧ exponent = Term.Numeral E ∧
      u = Term.Numeral U ∧
      native_zleq 0 W = true ∧ native_zleq 0 E = true ∧
      native_zleq 0 U = true ∧ native_zlt U W = true ∧
      D = native_zplus U 1 ∧ native_zlt 0 D = true ∧
      native_zplus D E = W ∧
      __eo_typeof z =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __smtx_typeof (__eo_to_smt z) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof z)
        (__eo_typeof (bvMultPow2Const size n)))
      (__eo_typeof (bvMultPow2Rhs z exponent u)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hLhsNe with
    ⟨widthTerm, hZTy, hConstTy⟩
  have hSizeNe := RuleProofs.term_ne_stuck_of_has_smt_translation size hSizeTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  rcases bv_all_ones_const_context n size widthTerm hNNe hSizeNe
      (by simpa [bvMultPow2Const, bvAllOnesConst] using hConstTy) with
    ⟨W, hSize, hWidth, hW0, hNTy⟩
  subst widthTerm
  have hZSmtTy :
      __smtx_typeof (__eo_to_smt z) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [__eo_to_smt_type, hW0, native_ite] using
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        z (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt z) rfl hZTrans hZTy)
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      n (Term.UOp UserOp.Int) (__eo_to_smt n) rfl hNTrans hNTy
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hLhsTy :
      __eo_typeof_bvand (__eo_typeof z)
          (__eo_typeof (bvMultPow2Const size n)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hZTy, hConstTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRhsTy :
      __eo_typeof (bvMultPow2Rhs z exponent u) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypeEq
    exact hTypeEq.symm
  change __eo_typeof_concat
      (__eo_typeof
        (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
          u (Term.Numeral 0)))
      (__eo_typeof (bvMultPow2Zeros exponent)) ≠ Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_mult_pow2 hRhsNe with
    ⟨extractWidth, zeroWidth, hExtractTy, hZerosTy⟩
  have hZerosNe : __eo_typeof (bvMultPow2Zeros exponent) ≠ Term.Stuck := by
    rw [hZerosTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof (bvMultPow2Const exponent (Term.Numeral 0)))
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck at hZerosNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_mult_pow2 hZerosNe with
    ⟨exponentWidth, _emptyWidth, hZeroConstTy, _hEmptyTy⟩
  have hExponentNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation exponent hExponentTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) exponent exponentWidth
      (by simp) hExponentNe
      (by simpa [bvMultPow2Const, bvAllOnesConst] using hZeroConstTy) with
    ⟨E, hExponent, hExponentWidth, hE0, _hZeroTy⟩
  subst exponentWidth
  rw [hExponent] at hZeroConstTy
  have hZerosEoTy :
      __eo_typeof (bvMultPow2Zeros (Term.Numeral E)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral E) := by
    change __eo_typeof_concat
        (__eo_typeof (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0)))
        (__eo_typeof (Term.Binary 0 0)) = _
    rw [hZeroConstTy]
    change __eo_typeof_concat
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral E))
      (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) = _
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus]
  have hZeroWidth : zeroWidth = Term.Numeral E := by
    rw [hExponent, hZerosEoTy] at hZerosTy
    injection hZerosTy with _ h
    exact h.symm
  subst zeroWidth
  have hNegSmtTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) z)) =
        SmtType.BitVec (native_int_to_nat W) :=
    smt_typeof_bvneg_same (__eo_to_smt z) (native_int_to_nat W) hZSmtTy
  have hNegTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.bvneg) z) := by
    intro h
    rw [h] at hNegSmtTy
    cases hNegSmtTy
  have hExtractNe :
      __eo_typeof
          (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
            u (Term.Numeral 0)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (Term.Apply (Term.UOp UserOp.bvneg) z) u (Term.Numeral 0)
      hNegTrans hExtractNe with
    ⟨W', U, L, hNegTy, hU, hL, hW'0, hL0, hUW', hD0,
      hNegSmtTy'⟩
  have hWW' : W' = W := by
    rw [hNegSmtTy] at hNegSmtTy'
    have hNat := (SmtType.BitVec.inj hNegSmtTy').symm
    exact nonneg_int_eq_of_toNat_eq W' W hW'0 hW0 hNat
  subst W'
  have hLZero : L = 0 := by
    injection hL with h
    exact h.symm
  subst L
  let D := native_zplus U 1
  have hDPos : native_zlt 0 D = true := by
    simpa [D, SmtEval.native_zplus, SmtEval.native_zneg] using hD0
  have hDPosRaw : native_zlt 0 (U + 1) = true := by
    simpa [D, SmtEval.native_zplus] using hDPos
  have hExtractEoTy :
      __eo_typeof
          (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
            (Term.Numeral U) (Term.Numeral 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    have hGtZero : native_zlt (-1 : native_Int) 0 = true := by decide
    have hGtD : native_zlt (-1 : native_Int) D = true := by
      have hDInt : (0 : Int) < D := by
        simpa [SmtEval.native_zlt] using hDPos
      simpa [SmtEval.native_zlt] using (show (-1 : Int) < D by omega)
    change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral U)
        (Term.UOp UserOp.Int) (Term.Numeral 0) _ = _
    rw [hNegTy]
    simp [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt,
      __eo_requires, __eo_mk_apply, native_ite, native_teq, native_not,
      hGtZero, hUW', hDPos, hDPosRaw, hGtD, D, SmtEval.native_zplus,
      SmtEval.native_zneg]
  have hExtractWidth : extractWidth = Term.Numeral D := by
    rw [hU, hExtractEoTy] at hExtractTy
    injection hExtractTy with _ h
    exact h.symm
  subst extractWidth
  have hRhsWidth : native_zplus D E = W := by
    have hRhsTy' := hRhsTy
    change __eo_typeof_concat
        (__eo_typeof
          (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
            u (Term.Numeral 0)))
        (__eo_typeof (bvMultPow2Zeros exponent)) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) at hRhsTy'
    rw [hU, hExponent, hExtractEoTy, hZerosEoTy] at hRhsTy'
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus] at hRhsTy'
    exact hRhsTy'
  have hU0 : native_zleq 0 U = true := by
    have hDInt : (0 : Int) < D := by
      simpa [SmtEval.native_zlt] using hDPos
    have hUInt : (0 : Int) ≤ U := by
      simp [D, SmtEval.native_zplus] at hDInt
      omega
    simpa [SmtEval.native_zleq] using hUInt
  exact ⟨W, E, U, D, hSize, hExponent, hU, hW0, hE0, hU0,
    hUW', rfl, hDPos, hRhsWidth, hZTy, hZSmtTy, hNSmtTy⟩

private theorem bv_mult_pow2_nil_ne
    (z size n exponent u : Term) :
    __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool ->
    bvMultPow2Nil z ≠ Term.Stuck := by
  intro hTy hNil
  have hLhsNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hTy; (try simp [bvMultPow2Term] at hsimpa ⊢); exact hsimpa)).1
  apply hLhsNe
  change __eo_typeof_bvand (__eo_typeof z)
      (__eo_typeof_bvand (__eo_typeof (bvMultPow2Const size n))
        (__eo_typeof (bvMultPow2Nil z))) = Term.Stuck
  rw [hNil]
  change __eo_typeof_bvand (__eo_typeof z)
      (__eo_typeof_bvand (__eo_typeof (bvMultPow2Const size n))
        Term.Stuck) = Term.Stuck
  simp [__eo_typeof_bvand]

private theorem bv_mult_pow2_nil_eq_one
    (z : Term) (W : native_Int) :
    __eo_typeof z =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    native_zlt 0 W = true ->
    bvMultPow2Nil z ≠ Term.Stuck ->
    bvMultPow2Nil z = Term.Binary W 1 := by
  intro hZTy hW0 hWPos hNilNe
  unfold bvMultPow2Nil
  rw [hZTy]
  change __eo_to_bin (Term.Numeral W) (Term.Numeral 1) = Term.Binary W 1
  change
    native_ite (native_zleq W 4294967296)
        (__eo_mk_binary W 1) Term.Stuck = Term.Binary W 1
  cases hBound : native_zleq W 4294967296
  · exfalso
    apply hNilNe
    unfold bvMultPow2Nil
    rw [hZTy]
    change native_ite (native_zleq W 4294967296)
        (__eo_mk_binary W 1) Term.Stuck = Term.Stuck
    rw [hBound]
    rfl
  · simp [native_ite, hBound]
    simp [__eo_mk_binary, native_ite, hW0]
    have hPowGtOne : (1 : Int) < native_int_pow2 W := by
      have hWInt : (0 : Int) < W := by
        simpa [SmtEval.native_zlt] using hWPos
      unfold SmtEval.native_int_pow2 SmtEval.native_zexp_total
      simp [Int.not_lt.mpr (Int.le_of_lt hWInt)]
      have hNatPos : 0 < W.toNat := by
        have hRound := Int.toNat_of_nonneg (Int.le_of_lt hWInt)
        omega
      exact_mod_cast Nat.one_lt_two_pow (by omega : W.toNat ≠ 0)
    have hMod : native_mod_total 1 (native_int_pow2 W) = 1 := by
      exact Int.emod_eq_of_lt (by decide) hPowGtOne
    rw [hMod]

private theorem smtx_typeof_bvmul_term_eq_mult_pow2
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvmul x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem smt_typeof_binary_one_mult_pow2 (W : native_Int) :
    native_zleq 0 W = true ->
    native_zlt 0 W = true ->
    __smtx_typeof (SmtTerm.Binary W 1) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hW0 hWPos
  have hWInt : (0 : Int) < W := by
    simpa [SmtEval.native_zlt] using hWPos
  have hPowGtOne : (1 : Int) < native_int_pow2 W := by
    unfold SmtEval.native_int_pow2 SmtEval.native_zexp_total
    simp [Int.not_lt.mpr (Int.le_of_lt hWInt)]
    have hNatPos : 0 < W.toNat := by
      have hRound := Int.toNat_of_nonneg (Int.le_of_lt hWInt)
      omega
    exact_mod_cast Nat.one_lt_two_pow (by omega : W.toNat ≠ 0)
  have hMod : native_mod_total 1 (native_int_pow2 W) = 1 :=
    Int.emod_eq_of_lt (by decide) hPowGtOne
  simp [__smtx_typeof, SmtEval.native_and, native_ite, hW0,
    native_zeq, hMod]

theorem typed_bv_mult_pow2_term
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvMultPow2Term z size n exponent u) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
  rcases bv_mult_pow2_context z size n exponent u hZTrans hSizeTrans
      hNTrans hExponentTrans hResultTy with
    ⟨W, E, U, D, rfl, rfl, rfl, hW0, hE0, hU0, hUW, hD,
      hDPos, hDE, hZTy, hZSmtTy, hNSmtTy⟩
  have hWPos : native_zlt 0 W = true := by
    have hDInt : (0 : Int) < D := by
      simpa [SmtEval.native_zlt] using hDPos
    have hEInt : (0 : Int) ≤ E := by
      simpa [SmtEval.native_zleq] using hE0
    have hDEInt : D + E = W := by
      simpa [SmtEval.native_zplus] using hDE
    have hWInt : (0 : Int) < W := by
      rw [← hDEInt]
      omega
    simpa [SmtEval.native_zlt] using hWInt
  have hNilNe := bv_mult_pow2_nil_ne z (Term.Numeral W) n
    (Term.Numeral E) (Term.Numeral U) hResultTy
  have hNilEq := bv_mult_pow2_nil_eq_one z W hZTy hW0 hWPos hNilNe
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt (bvMultPow2Const (Term.Numeral W) n)) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hNSmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW0]
  have hNilTy :
      __smtx_typeof (__eo_to_smt (bvMultPow2Nil z)) =
        SmtType.BitVec (native_int_to_nat W) := by
    rw [hNilEq]
    exact smt_typeof_binary_one_mult_pow2 W hW0 hWPos
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
              (bvMultPow2Const (Term.Numeral W) n))
              (bvMultPow2Nil z))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
      (SmtTerm.bvmul
        (__eo_to_smt (bvMultPow2Const (Term.Numeral W) n))
        (__eo_to_smt (bvMultPow2Nil z))) = _
    rw [smtx_typeof_bvmul_term_eq_mult_pow2]
    simp [__smtx_typeof_bv_op_2, hConstTy, hNilTy, native_nateq,
      native_ite]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (bvMultPow2Lhs z (Term.Numeral W) n)) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
      (SmtTerm.bvmul (__eo_to_smt z)
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
            (bvMultPow2Const (Term.Numeral W) n))
            (bvMultPow2Nil z)))) = _
    rw [smtx_typeof_bvmul_term_eq_mult_pow2]
    simp [__smtx_typeof_bv_op_2, hZSmtTy, hInnerTy, native_nateq,
      native_ite]
  have hZeroTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat E) := by
    exact smtx_typeof_int_to_bv_numerals E 0 hE0
  have hEInt : (0 : Int) ≤ E := by
    simpa [SmtEval.native_zleq] using hE0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hDInt : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have hNegTy := smt_typeof_bvneg_same (__eo_to_smt z)
    (native_int_to_nat W) hZSmtTy
  have hExtractTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
              (Term.Numeral U) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat D) := by
    have hSlice :
        native_zplus (native_zplus U 1) (native_zneg 0) = D := by
      simp [hD, SmtEval.native_zplus, SmtEval.native_zneg]
    rw [← hSlice]
    exact smt_typeof_extract_of_context
      (Term.Apply (Term.UOp UserOp.bvneg) z) W U 0 hNegTy
      hW0 (by decide) hUW (by simpa [hSlice] using hDPos)
  have hEmptyTy :
      __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
    simp [__smtx_typeof, SmtEval.native_and, native_ite,
      SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
      native_mod_total, native_int_to_nat, SmtEval.native_int_to_nat]
  have hZerosTy :
      __smtx_typeof
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E))) =
        SmtType.BitVec (native_int_to_nat E) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0)))
          (SmtTerm.Binary 0 0)) = _
    rw [typeof_concat_eq, hZeroTy, hEmptyTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      SmtEval.native_nat_to_int, SmtEval.native_zplus,
      Int.max_eq_left hEInt]
  have hDRound := native_int_to_nat_roundtrip D hDNonneg
  have hERound := native_int_to_nat_roundtrip E hE0
  have hDEInt : D + E = W := by
    simpa [SmtEval.native_zplus] using hDE
  have hWidthNat :
      native_int_to_nat D + native_int_to_nat E = native_int_to_nat W := by
    simp only [native_int_to_nat, SmtEval.native_int_to_nat]
    rw [← Int.toNat_add hDInt hEInt]
    simpa using congrArg Int.toNat hDEInt
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2Rhs z (Term.Numeral E) (Term.Numeral U))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
              (Term.Numeral U) (Term.Numeral 0)))
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E)))) = _
    rw [typeof_concat_eq, hExtractTy, hZerosTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      SmtEval.native_nat_to_int, SmtEval.native_zplus, hWidthNat,
      hDRound, hERound, hDE, hDEInt, Int.max_eq_left hDInt,
      Int.max_eq_left hEInt]
  unfold bvMultPow2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

theorem typed_bv_mult_pow2_direct_term
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2DirectTerm z size n exponent u) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvMultPow2DirectTerm z size n exponent u) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
  rcases bv_mult_pow2_direct_context z size n exponent u hZTrans hSizeTrans
      hNTrans hExponentTrans hResultTy with
    ⟨W, E, U, D, rfl, rfl, rfl, hW0, hE0, hU0, hUW, hD,
      hDPos, hDE, hZTy, hZSmtTy, hNSmtTy⟩
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt (bvMultPow2Const (Term.Numeral W) n)) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hNSmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW0]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (bvMultPow2DirectLhs z (Term.Numeral W) n)) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
      (SmtTerm.bvmul (__eo_to_smt z)
        (__eo_to_smt (bvMultPow2Const (Term.Numeral W) n))) = _
    rw [smtx_typeof_bvmul_term_eq_mult_pow2]
    simp [__smtx_typeof_bv_op_2, hZSmtTy, hConstTy, native_nateq,
      native_ite]
  have hZeroTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat E) := by
    exact smtx_typeof_int_to_bv_numerals E 0 hE0
  have hEInt : (0 : Int) ≤ E := by
    simpa [SmtEval.native_zleq] using hE0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hDInt : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have hNegTy := smt_typeof_bvneg_same (__eo_to_smt z)
    (native_int_to_nat W) hZSmtTy
  have hExtractTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
              (Term.Numeral U) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat D) := by
    have hSlice :
        native_zplus (native_zplus U 1) (native_zneg 0) = D := by
      simp [hD, SmtEval.native_zplus, SmtEval.native_zneg]
    rw [← hSlice]
    exact smt_typeof_extract_of_context
      (Term.Apply (Term.UOp UserOp.bvneg) z) W U 0 hNegTy
      hW0 (by decide) hUW (by simpa [hSlice] using hDPos)
  have hEmptyTy :
      __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
    simp [__smtx_typeof, SmtEval.native_and, native_ite,
      SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
      native_mod_total, native_int_to_nat, SmtEval.native_int_to_nat]
  have hZerosTy :
      __smtx_typeof
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E))) =
        SmtType.BitVec (native_int_to_nat E) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0)))
          (SmtTerm.Binary 0 0)) = _
    rw [typeof_concat_eq, hZeroTy, hEmptyTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      SmtEval.native_nat_to_int, SmtEval.native_zplus,
      Int.max_eq_left hEInt]
  have hDRound := native_int_to_nat_roundtrip D hDNonneg
  have hERound := native_int_to_nat_roundtrip E hE0
  have hDEInt : D + E = W := by
    simpa [SmtEval.native_zplus] using hDE
  have hWidthNat :
      native_int_to_nat D + native_int_to_nat E = native_int_to_nat W := by
    simp only [native_int_to_nat, SmtEval.native_int_to_nat]
    rw [← Int.toNat_add hDInt hEInt]
    simpa using congrArg Int.toNat hDEInt
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2Rhs z (Term.Numeral E) (Term.Numeral U))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
              (Term.Numeral U) (Term.Numeral 0)))
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E)))) = _
    rw [typeof_concat_eq, hExtractTy, hZerosTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      SmtEval.native_nat_to_int, SmtEval.native_zplus, hWidthNat,
      hDRound, hERound, hDE, hDEInt, Int.max_eq_left hDInt,
      Int.max_eq_left hEInt]
  unfold bvMultPow2DirectTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

private theorem model_eval_eq_true_of_eo_eq_true_mult_pow2
    (M : SmtModel) (a b : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem eval_bv_mult_pow2_diff
    (M : SmtModel) (n : Term) (W N : native_Int) :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral N ->
    __smtx_model_eval M
        (__eo_to_smt (bvMultPow2Diff (Term.Numeral W) n)) =
      SmtValue.Numeral (native_zplus (native_int_pow2 W) (native_zneg N)) := by
  intro hNEval
  change __smtx_model_eval M
      (SmtTerm.neg (SmtTerm.int_pow2 (SmtTerm.Numeral W))
        (__eo_to_smt n)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval, hNEval, __smtx_model_eval__,
    __smtx_model_eval_int_pow2]

private theorem bv_mult_pow2_premises_numeric
    (M : SmtModel) (hM : model_wf M)
    (n : Term) (W E : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    eo_interprets M
      (bvMultPow2IspowPrem (Term.Numeral W) n) true ->
    eo_interprets M
      (bvMultPow2ExponentPrem (Term.Numeral W) n (Term.Numeral E)) true ->
    ∃ N : native_Int,
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral N ∧
      N = native_zplus (native_int_pow2 W)
        (native_zneg (native_int_pow2 E)) := by
  intro hNTy hIspPrem hExponentPrem
  rcases CongSupport.smt_eval_int_of_smt_type_int M hM (__eo_to_smt n)
      hNTy with ⟨N, hNEval⟩
  let V := native_zplus (native_int_pow2 W) (native_zneg N)
  have hDiffEval := eval_bv_mult_pow2_diff M n W N hNEval
  have hExponentEq := model_eval_eq_true_of_eo_eq_true_mult_pow2 M
    (Term.Numeral E)
    (Term.Apply (Term.UOp UserOp.int_log2)
      (bvMultPow2Diff (Term.Numeral W) n))
    (by simpa [bvMultPow2ExponentPrem] using hExponentPrem)
  change __smtx_model_eval_eq (SmtValue.Numeral E)
      (__smtx_model_eval_int_log2
        (__smtx_model_eval M
          (__eo_to_smt (bvMultPow2Diff (Term.Numeral W) n)))) =
    SmtValue.Boolean true at hExponentEq
  rw [hDiffEval] at hExponentEq
  have hELog : E = native_int_log2 V := by
    simpa [V, __smtx_model_eval_int_log2, __smtx_model_eval_eq,
      native_veq, SmtEval.native_zeq] using hExponentEq
  have hIspEq := model_eval_eq_true_of_eo_eq_true_mult_pow2 M
    (Term.Apply (Term.UOp UserOp.int_ispow2)
      (bvMultPow2Diff (Term.Numeral W) n))
    (Term.Boolean true)
    (by simpa [bvMultPow2IspowPrem] using hIspPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval_and
        (__smtx_model_eval_geq
          (__smtx_model_eval M
            (__eo_to_smt (bvMultPow2Diff (Term.Numeral W) n)))
          (SmtValue.Numeral 0))
        (__smtx_model_eval_eq
          (__smtx_model_eval M
            (__eo_to_smt (bvMultPow2Diff (Term.Numeral W) n)))
          (__smtx_model_eval_int_pow2
            (__smtx_model_eval_int_log2
              (__smtx_model_eval M
                (__eo_to_smt (bvMultPow2Diff (Term.Numeral W) n)))))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hIspEq
  rw [hDiffEval] at hIspEq
  have hVPow : V = native_int_pow2 (native_int_log2 V) := by
    have hParts :
        (0 : Int) ≤ V ∧ V = native_int_pow2 (native_int_log2 V) := by
      simpa [V, __smtx_model_eval_int_log2, __smtx_model_eval_int_pow2,
        __smtx_model_eval_and, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_zeq, SmtEval.native_zleq, native_and,
        Bool.and_eq_true] using hIspEq
    exact hParts.2
  have hVPowE : V = native_int_pow2 E := by
    rw [hELog]
    exact hVPow
  have hN : N = native_zplus (native_int_pow2 W)
      (native_zneg (native_int_pow2 E)) := by
    change native_int_pow2 W - N = native_int_pow2 E at hVPowE
    change N = native_int_pow2 W - native_int_pow2 E
    symm
    apply Int.sub_eq_iff_eq_add.mpr
    exact (Int.sub_eq_iff_eq_add.mp hVPowE).trans
      (Int.add_comm (native_int_pow2 E) N)
  exact ⟨N, hNEval, hN⟩

private theorem ofInt_pow2_sub_pow2_eq_neg_twoPow_mult_pow2
    (D E : Nat) (hD : 0 < D) :
    BitVec.ofInt (D + E)
        ((2 : Int) ^ (D + E) - (2 : Int) ^ E) =
      -BitVec.twoPow (D + E) E := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_neg,
    BitVec.toNat_twoPow]
  have hPowE : (2 : Int) ^ E = ((2 ^ E : Nat) : Int) := by norm_cast
  have hPowW : (2 : Int) ^ (D + E) = ((2 ^ (D + E) : Nat) : Int) := by
    norm_cast
  rw [hPowE, hPowW]
  have hLe : 2 ^ E ≤ 2 ^ (D + E) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  rw [← Int.natCast_sub hLe]
  have hSubLt : 2 ^ (D + E) - 2 ^ E < 2 ^ (D + E) := by
    have := Nat.two_pow_pos E
    omega
  rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
    (by exact_mod_cast hSubLt)]
  simp only [Int.toNat_natCast]
  have hModE : 2 ^ E % 2 ^ (D + E) = 2 ^ E :=
    Nat.mod_eq_of_lt
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
  rw [hModE, Nat.mod_eq_of_lt hSubLt]

private theorem bitvec_mult_pow2_core
    (D E : Nat) (hD : 0 < D) (x : BitVec (D + E)) :
    x * BitVec.ofInt (D + E)
        ((2 : Int) ^ (D + E) - (2 : Int) ^ E) =
      (-x).extractLsb' 0 D ++ 0#E := by
  rw [ofInt_pow2_sub_pow2_eq_neg_twoPow_mult_pow2 D E hD]
  rw [BitVec.mul_neg, BitVec.mul_twoPow_eq_shiftLeft]
  rw [← BitVec.shiftLeft_neg]
  have hELt : E < D + E := by omega
  rw [BitVec.shiftLeft_eq_concat_of_lt hELt]
  have hLen : D + E - E = D := by omega
  apply BitVec.eq_of_toNat_eq
  simp [hLen]

private theorem bitvec_mult_pow2_core_toNat
    (D E W : Nat) (hWidth : D + E = W) (hD : 0 < D)
    (x : BitVec W) :
    (x * BitVec.ofInt W ((2 : Int) ^ W - (2 : Int) ^ E)).toNat =
      ((-x).extractLsb' 0 D ++ 0#E).toNat := by
  subst W
  exact congrArg BitVec.toNat (bitvec_mult_pow2_core D E hD x)

theorem bvmul_bitvec_values_mult_pow2
    (W : Nat) (x y : BitVec W) :
    __smtx_model_eval_bvmul
        (SmtValue.Binary (native_nat_to_int W) (x.toNat : Int))
        (SmtValue.Binary (native_nat_to_int W) (y.toNat : Int)) =
      SmtValue.Binary (native_nat_to_int W) ((x * y).toNat : Int) := by
  change SmtValue.Binary (native_nat_to_int W)
      (native_mod_total
        (native_zmult (x.toNat : Int) (y.toNat : Int))
        (native_int_pow2 (native_nat_to_int W))) = _
  congr 2

theorem concat_zero_bitvec_value_mult_pow2
    (D E : Nat) (x : BitVec D) :
    __smtx_model_eval_concat
        (SmtValue.Binary (native_nat_to_int D) (x.toNat : Int))
        (SmtValue.Binary (native_nat_to_int E) 0) =
      SmtValue.Binary (native_nat_to_int (D + E))
        ((x ++ 0#E).toNat : Int) := by
  change SmtValue.Binary
      (native_zplus (native_nat_to_int D) (native_nat_to_int E))
      (native_mod_total
        (native_binary_concat (native_nat_to_int D) (x.toNat : Int)
          (native_nat_to_int E) 0)
        (native_int_pow2
          (native_zplus (native_nat_to_int D) (native_nat_to_int E)))) = _
  have hWidth : native_zplus (native_nat_to_int D) (native_nat_to_int E) =
      native_nat_to_int (D + E) := by
    simp [SmtEval.native_zplus, native_nat_to_int,
      SmtEval.native_nat_to_int]
  rw [hWidth]
  congr 2
  simp only [native_binary_concat, native_zmult]
  rw [native_int_pow2_nat E, native_int_pow2_nat (D + E)]
  simp only [BitVec.toNat_append, BitVec.toNat_zero, Nat.or_zero,
    Nat.shiftLeft_eq]
  change ((x.toNat : Int) * (2 ^ E : Int)) % (2 ^ (D + E) : Int) =
    ((x.toNat * 2 ^ E : Nat) : Int)
  have hCast : (x.toNat : Int) * (2 : Int) ^ E =
      ((x.toNat * 2 ^ E : Nat) : Int) := by norm_cast
  rw [hCast]
  apply Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
  have hBoundNat : x.toNat * 2 ^ E < 2 ^ (D + E) := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right x.isLt (Nat.two_pow_pos E)
  exact_mod_cast hBoundNat

private theorem eval_bv_mult_pow2
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2IspowPrem size n) true ->
    eo_interprets M (bvMultPow2ExponentPrem size n exponent) true ->
    __smtx_model_eval M (__eo_to_smt (bvMultPow2Lhs z size n)) =
      __smtx_model_eval M (__eo_to_smt (bvMultPow2Rhs z exponent u)) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
    hIspPrem hExponentPrem
  rcases bv_mult_pow2_context z size n exponent u hZTrans hSizeTrans
      hNTrans hExponentTrans hResultTy with
    ⟨W, E, U, D, rfl, rfl, rfl, hW0, hE0, hU0, hUW, hD,
      hDPos, hDE, hZTy, hZSmtTy, hNSmtTy⟩
  let WN := native_int_to_nat W
  let EN := native_int_to_nat E
  let DN := native_int_to_nat D
  have hD0 : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hWRound : (native_nat_to_int WN : Int) = W := by
    simpa [WN, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip W hW0
  have hERound : (native_nat_to_int EN : Int) = E := by
    simpa [EN, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip E hE0
  have hDRound : (native_nat_to_int DN : Int) = D := by
    simpa [DN, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip D hD0
  have hDInt : (0 : Int) < D := by
    simpa [SmtEval.native_zlt] using hDPos
  have hEInt : (0 : Int) ≤ E := by
    simpa [SmtEval.native_zleq] using hE0
  have hWInt : (0 : Int) ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have hDEInt : D + E = W := by
    simpa [SmtEval.native_zplus] using hDE
  have hWidthNat : DN + EN = WN := by
    change Int.toNat D + Int.toNat E = Int.toNat W
    rw [← Int.toNat_add (Int.le_of_lt hDInt) hEInt, hDEInt]
  have hDNPos : 0 < DN := by
    change 0 < Int.toNat D
    apply Nat.pos_of_ne_zero
    intro hZero
    have hDLe : D ≤ 0 := Int.toNat_eq_zero.mp hZero
    omega
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z) WN
      (by simpa [WN] using hZSmtTy) with
    ⟨p, hZEval, hZCan⟩
  have hWidth0 : native_zleq 0 (native_nat_to_int WN) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, SmtEval.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hZCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ WN := by
    simpa [natpow2_eq, native_nat_to_int,
      SmtEval.native_nat_to_int] using hRange.2
  let Z := p.toNat
  have hZCast : (Z : Int) = p := by
    exact Int.toNat_of_nonneg hp0
  let x := BitVec.ofInt WN (Z : Int)
  have hxNat : x.toNat = Z := by
    exact ofInt_toNat_canonical WN (Z : Int) (Int.natCast_nonneg Z)
      (by simpa [Z, hZCast] using hp1)
  have hZEval' :
      __smtx_model_eval M (__eo_to_smt z) =
        SmtValue.Binary (native_nat_to_int WN) (x.toNat : Int) := by
    rw [hZEval, hxNat, hZCast]
  have hIspPrem' :
      eo_interprets M
        (bvMultPow2IspowPrem (Term.Numeral W) n) true := by
    simpa using hIspPrem
  have hExponentPrem' :
      eo_interprets M
        (bvMultPow2ExponentPrem (Term.Numeral W) n (Term.Numeral E)) true := by
    simpa using hExponentPrem
  rcases bv_mult_pow2_premises_numeric M hM n W E hNSmtTy
      hIspPrem' hExponentPrem' with ⟨N, hNEval, hN⟩
  have hNativePowW : native_int_pow2 W = (2 : Int) ^ WN := by
    rw [← hWRound]
    exact native_int_pow2_nat WN
  have hNativePowE : native_int_pow2 E = (2 : Int) ^ EN := by
    rw [← hERound]
    exact native_int_pow2_nat EN
  have hNPow : N = (2 : Int) ^ WN - (2 : Int) ^ EN := by
    have hsimpa := hN
    try simp [SmtEval.native_zplus, SmtEval.native_zneg, hNativePowW, hNativePowE] at hsimpa ⊢
    exact hsimpa
  have hENLtWN : EN < WN := by
    calc
      EN < DN + EN := Nat.lt_add_of_pos_left hDNPos
      _ = WN := hWidthNat
  have hPowLeNat : 2 ^ EN ≤ 2 ^ WN :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hENLtWN)
  have hPowLe : (2 : Int) ^ EN ≤ (2 : Int) ^ WN := by
    exact_mod_cast hPowLeNat
  have hN0 : (0 : Int) ≤ N := by
    rw [hNPow]
    exact Int.sub_nonneg.mpr hPowLe
  have hNLt : N < (2 : Int) ^ WN := by
    rw [hNPow]
    have hPowPos : (0 : Int) < (2 : Int) ^ EN := by
      exact_mod_cast Nat.two_pow_pos EN
    exact Int.sub_lt_self _ hPowPos
  let nBv := BitVec.ofInt WN N
  have hnBvNat : nBv.toNat = N.toNat :=
    ofInt_toNat_canonical WN N hN0 hNLt
  have hNCast : (N.toNat : Int) = N := Int.toNat_of_nonneg hN0
  have hNMod : native_mod_total N (native_int_pow2 W) = N := by
    rw [hNativePowW]
    exact Int.emod_eq_of_lt hN0 hNLt
  have hConstEval :
      __smtx_model_eval M
          (__eo_to_smt (bvMultPow2Const (Term.Numeral W) n)) =
        SmtValue.Binary (native_nat_to_int WN) (nBv.toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_eval_int_to_bv_term_eq, hNEval]
    change SmtValue.Binary W
        (native_mod_total N (native_int_pow2 W)) = _
    rw [hNMod, hnBvNat, hNCast, hWRound]
  have hWPos : native_zlt 0 W = true := by
    have : (0 : Int) < W := by rw [← hDEInt]; omega
    simpa [SmtEval.native_zlt] using this
  have hNilNe := bv_mult_pow2_nil_ne z (Term.Numeral W) n
    (Term.Numeral E) (Term.Numeral U) hResultTy
  have hNilEq := bv_mult_pow2_nil_eq_one z W hZTy hW0 hWPos hNilNe
  let oneBv := BitVec.ofInt WN (1 : Int)
  have hOneNat : oneBv.toNat = 1 := by
    apply ofInt_toNat_canonical WN 1 (by decide)
    have hWNPos : 0 < WN := by
      rw [← hWidthNat]
      exact Nat.lt_of_lt_of_le hDNPos (Nat.le_add_right DN EN)
    exact_mod_cast Nat.one_lt_two_pow (Nat.ne_of_gt hWNPos)
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt (bvMultPow2Nil z)) =
        SmtValue.Binary (native_nat_to_int WN) (oneBv.toNat : Int) := by
    rw [hNilEq, eval_binary, hOneNat, hWRound]
    simp
  have hInnerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul)
              (bvMultPow2Const (Term.Numeral W) n))
              (bvMultPow2Nil z))) =
        SmtValue.Binary (native_nat_to_int WN) (nBv.toNat : Int) := by
    rw [eval_bvmul_term M _ _ _ _ hConstEval hNilEval]
    rw [bvmul_bitvec_values_mult_pow2]
    congr 2
    simp [oneBv]
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt (bvMultPow2Lhs z (Term.Numeral W) n)) =
        SmtValue.Binary (native_nat_to_int WN) ((x * nBv).toNat : Int) := by
    exact eval_bvmul_term M z _ _ _ hZEval' hInnerEval |>.trans
      (bvmul_bitvec_values_mult_pow2 WN x nBv)
  have hNegEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) z)) =
        SmtValue.Binary (native_nat_to_int WN) ((-x).toNat : Int) := by
    change __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt z)) = _
    rw [_root_.smtx_eval_bvneg_term_eq, hZEval', hxNat]
    simpa [x] using eval_bvneg_canonical_ssubo WN Z
  have hNeg0 : (0 : Int) ≤ ((-x).toNat : Int) := Int.natCast_nonneg _
  have hNeg1 : ((-x).toNat : Int) < (2 : Int) ^ WN := by
    exact_mod_cast (-x).isLt
  have hSliceWidth : U + 1 + -0 = (DN : Int) := by
    calc
      U + 1 + -0 = D := by
        simpa [SmtEval.native_zplus] using hD.symm
      _ = (DN : Int) := by
        simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hDRound.symm
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
              (Term.Numeral U) (Term.Numeral 0))) =
        SmtValue.Binary (native_nat_to_int DN)
          (((-x).extractLsb' 0 DN).toNat : Int) := by
    rw [eval_extract_term, hNegEval]
    have hExtract :=
      extract_val_bitvec_start_len WN 0 DN ((-x).toNat : Int) U 0
        hNeg0 hNeg1 (by simp) hSliceWidth
    have hOf : BitVec.ofInt WN ((-x).toNat : Int) = -x :=
      bitvec_ofInt_natCast_toNat (-x)
    rw [hOf] at hExtract
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hExtract
  have hZeroConstEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0))) =
        SmtValue.Binary (native_nat_to_int EN) 0 := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral E) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_numerals]
    have hMod0 : native_mod_total 0 (native_int_pow2 E) = 0 := by
      simp [native_mod_total]
    rw [hMod0, hERound]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := eval_binary M 0 0
  have hZerosEval :
      __smtx_model_eval M
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E))) =
        SmtValue.Binary (native_nat_to_int EN) 0 := by
    unfold bvMultPow2Zeros
    rw [eval_concat_term M _ _ _ _ hZeroConstEval hEmptyEval]
    exact concat_zero_right_value EN 0 (Nat.two_pow_pos EN)
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultPow2Rhs z (Term.Numeral E) (Term.Numeral U))) =
        SmtValue.Binary (native_nat_to_int WN)
          (((-x).extractLsb' 0 DN ++ 0#EN).toNat : Int) := by
    unfold bvMultPow2Rhs
    rw [eval_concat_term M _ _ _ _ hExtractEval hZerosEval]
    have hConcat := concat_zero_bitvec_value_mult_pow2 DN EN
      ((-x).extractLsb' 0 DN)
    have hWidthInt : native_nat_to_int (DN + EN) = native_nat_to_int WN :=
      congrArg native_nat_to_int hWidthNat
    rw [hWidthInt] at hConcat
    exact hConcat
  rw [hLhsEval, hRhsEval]
  congr 2
  have hNBitVec :
      nBv = BitVec.ofInt WN
        ((2 : Int) ^ WN - (2 : Int) ^ EN) := by
    simp [nBv, hNPow]
  rw [hNBitVec]
  exact bitvec_mult_pow2_core_toNat DN EN WN hWidthNat hDNPos x

theorem eval_bv_mult_pow2_direct
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2DirectTerm z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2IspowPrem size n) true ->
    eo_interprets M (bvMultPow2ExponentPrem size n exponent) true ->
    __smtx_model_eval M (__eo_to_smt (bvMultPow2DirectLhs z size n)) =
      __smtx_model_eval M (__eo_to_smt (bvMultPow2Rhs z exponent u)) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
    hIspPrem hExponentPrem
  rcases bv_mult_pow2_direct_context z size n exponent u hZTrans hSizeTrans
      hNTrans hExponentTrans hResultTy with
    ⟨W, E, U, D, rfl, rfl, rfl, hW0, hE0, hU0, hUW, hD,
      hDPos, hDE, hZTy, hZSmtTy, hNSmtTy⟩
  let WN := native_int_to_nat W
  let EN := native_int_to_nat E
  let DN := native_int_to_nat D
  have hD0 : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hWRound : (native_nat_to_int WN : Int) = W := by
    simpa [WN, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip W hW0
  have hERound : (native_nat_to_int EN : Int) = E := by
    simpa [EN, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip E hE0
  have hDRound : (native_nat_to_int DN : Int) = D := by
    simpa [DN, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip D hD0
  have hDInt : (0 : Int) < D := by
    simpa [SmtEval.native_zlt] using hDPos
  have hEInt : (0 : Int) ≤ E := by
    simpa [SmtEval.native_zleq] using hE0
  have hDEInt : D + E = W := by
    simpa [SmtEval.native_zplus] using hDE
  have hWidthNat : DN + EN = WN := by
    change Int.toNat D + Int.toNat E = Int.toNat W
    rw [← Int.toNat_add (Int.le_of_lt hDInt) hEInt, hDEInt]
  have hDNPos : 0 < DN := by
    change 0 < Int.toNat D
    apply Nat.pos_of_ne_zero
    intro hZero
    have hDLe : D ≤ 0 := Int.toNat_eq_zero.mp hZero
    omega
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt z) WN
      (by simpa [WN] using hZSmtTy) with
    ⟨p, hZEval, hZCan⟩
  have hWidth0 : native_zleq 0 (native_nat_to_int WN) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, SmtEval.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hZCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ WN := by
    simpa [natpow2_eq, native_nat_to_int,
      SmtEval.native_nat_to_int] using hRange.2
  let Z := p.toNat
  have hZCast : (Z : Int) = p := Int.toNat_of_nonneg hp0
  let x := BitVec.ofInt WN (Z : Int)
  have hxNat : x.toNat = Z := by
    exact ofInt_toNat_canonical WN (Z : Int) (Int.natCast_nonneg Z)
      (by simpa [Z, hZCast] using hp1)
  have hZEval' :
      __smtx_model_eval M (__eo_to_smt z) =
        SmtValue.Binary (native_nat_to_int WN) (x.toNat : Int) := by
    rw [hZEval, hxNat, hZCast]
  have hIspPrem' :
      eo_interprets M
        (bvMultPow2IspowPrem (Term.Numeral W) n) true := by
    simpa using hIspPrem
  have hExponentPrem' :
      eo_interprets M
        (bvMultPow2ExponentPrem (Term.Numeral W) n (Term.Numeral E)) true := by
    simpa using hExponentPrem
  rcases bv_mult_pow2_premises_numeric M hM n W E hNSmtTy
      hIspPrem' hExponentPrem' with ⟨N, hNEval, hN⟩
  have hNativePowW : native_int_pow2 W = (2 : Int) ^ WN := by
    rw [← hWRound]
    exact native_int_pow2_nat WN
  have hNativePowE : native_int_pow2 E = (2 : Int) ^ EN := by
    rw [← hERound]
    exact native_int_pow2_nat EN
  have hNPow : N = (2 : Int) ^ WN - (2 : Int) ^ EN := by
    have hsimpa := hN
    try simp [SmtEval.native_zplus, SmtEval.native_zneg, hNativePowW, hNativePowE] at hsimpa ⊢
    exact hsimpa
  have hENLtWN : EN < WN := by
    calc
      EN < DN + EN := Nat.lt_add_of_pos_left hDNPos
      _ = WN := hWidthNat
  have hPowLeNat : 2 ^ EN ≤ 2 ^ WN :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hENLtWN)
  have hPowLe : (2 : Int) ^ EN ≤ (2 : Int) ^ WN := by
    exact_mod_cast hPowLeNat
  have hN0 : (0 : Int) ≤ N := by
    rw [hNPow]
    exact Int.sub_nonneg.mpr hPowLe
  have hNLt : N < (2 : Int) ^ WN := by
    rw [hNPow]
    have hPowPos : (0 : Int) < (2 : Int) ^ EN := by
      exact_mod_cast Nat.two_pow_pos EN
    exact Int.sub_lt_self _ hPowPos
  let nBv := BitVec.ofInt WN N
  have hnBvNat : nBv.toNat = N.toNat :=
    ofInt_toNat_canonical WN N hN0 hNLt
  have hNCast : (N.toNat : Int) = N := Int.toNat_of_nonneg hN0
  have hNMod : native_mod_total N (native_int_pow2 W) = N := by
    rw [hNativePowW]
    exact Int.emod_eq_of_lt hN0 hNLt
  have hConstEval :
      __smtx_model_eval M
          (__eo_to_smt (bvMultPow2Const (Term.Numeral W) n)) =
        SmtValue.Binary (native_nat_to_int WN) (nBv.toNat : Int) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt n)) = _
    rw [smtx_eval_int_to_bv_term_eq, hNEval]
    change SmtValue.Binary W
        (native_mod_total N (native_int_pow2 W)) = _
    rw [hNMod, hnBvNat, hNCast, hWRound]
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt (bvMultPow2DirectLhs z (Term.Numeral W) n)) =
        SmtValue.Binary (native_nat_to_int WN) ((x * nBv).toNat : Int) := by
    exact eval_bvmul_term M z _ _ _ hZEval' hConstEval |>.trans
      (bvmul_bitvec_values_mult_pow2 WN x nBv)
  have hNegEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvneg) z)) =
        SmtValue.Binary (native_nat_to_int WN) ((-x).toNat : Int) := by
    change __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt z)) = _
    rw [_root_.smtx_eval_bvneg_term_eq, hZEval', hxNat]
    simpa [x] using eval_bvneg_canonical_ssubo WN Z
  have hNeg0 : (0 : Int) ≤ ((-x).toNat : Int) := Int.natCast_nonneg _
  have hNeg1 : ((-x).toNat : Int) < (2 : Int) ^ WN := by
    exact_mod_cast (-x).isLt
  have hSliceWidth : U + 1 + -0 = (DN : Int) := by
    calc
      U + 1 + -0 = D := by
        simpa [SmtEval.native_zplus] using hD.symm
      _ = (DN : Int) := by
        simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hDRound.symm
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm (Term.Apply (Term.UOp UserOp.bvneg) z)
              (Term.Numeral U) (Term.Numeral 0))) =
        SmtValue.Binary (native_nat_to_int DN)
          (((-x).extractLsb' 0 DN).toNat : Int) := by
    rw [eval_extract_term, hNegEval]
    have hExtract :=
      extract_val_bitvec_start_len WN 0 DN ((-x).toNat : Int) U 0
        hNeg0 hNeg1 (by simp) hSliceWidth
    have hOf : BitVec.ofInt WN ((-x).toNat : Int) = -x :=
      bitvec_ofInt_natCast_toNat (-x)
    rw [hOf] at hExtract
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hExtract
  have hZeroConstEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0))) =
        SmtValue.Binary (native_nat_to_int EN) 0 := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral E) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_numerals]
    have hMod0 : native_mod_total 0 (native_int_pow2 E) = 0 := by
      simp [native_mod_total]
    rw [hMod0, hERound]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := eval_binary M 0 0
  have hZerosEval :
      __smtx_model_eval M
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E))) =
        SmtValue.Binary (native_nat_to_int EN) 0 := by
    unfold bvMultPow2Zeros
    rw [eval_concat_term M _ _ _ _ hZeroConstEval hEmptyEval]
    exact concat_zero_right_value EN 0 (Nat.two_pow_pos EN)
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultPow2Rhs z (Term.Numeral E) (Term.Numeral U))) =
        SmtValue.Binary (native_nat_to_int WN)
          (((-x).extractLsb' 0 DN ++ 0#EN).toNat : Int) := by
    unfold bvMultPow2Rhs
    rw [eval_concat_term M _ _ _ _ hExtractEval hZerosEval]
    have hConcat := concat_zero_bitvec_value_mult_pow2 DN EN
      ((-x).extractLsb' 0 DN)
    have hWidthInt : native_nat_to_int (DN + EN) = native_nat_to_int WN :=
      congrArg native_nat_to_int hWidthNat
    rw [hWidthInt] at hConcat
    exact hConcat
  rw [hLhsEval, hRhsEval]
  congr 2
  have hNBitVec :
      nBv = BitVec.ofInt WN
        ((2 : Int) ^ WN - (2 : Int) ^ EN) := by
    simp [nBv, hNPow]
  rw [hNBitVec]
  exact bitvec_mult_pow2_core_toNat DN EN WN hWidthNat hDNPos x

theorem facts_bv_mult_pow2_direct_term
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2DirectTerm z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2IspowPrem size n) true ->
    eo_interprets M (bvMultPow2ExponentPrem size n exponent) true ->
    eo_interprets M (bvMultPow2UpperPrem size n u) true ->
    eo_interprets M (bvMultPow2DirectTerm z size n exponent u) true := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
    hIspPrem hExponentPrem _hUpperPrem
  have hBool := typed_bv_mult_pow2_direct_term z size n exponent u hZTrans
    hSizeTrans hNTrans hExponentTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvMultPow2DirectLhs z size n)))
      (__smtx_model_eval M (__eo_to_smt (bvMultPow2Rhs z exponent u)))
    rw [eval_bv_mult_pow2_direct M hM z size n exponent u hZTrans
      hSizeTrans hNTrans hExponentTrans hResultTy hIspPrem hExponentPrem]
    exact RuleProofs.smt_value_rel_refl _

theorem facts_bv_mult_pow2_term
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2IspowPrem size n) true ->
    eo_interprets M (bvMultPow2ExponentPrem size n exponent) true ->
    eo_interprets M (bvMultPow2UpperPrem size n u) true ->
    eo_interprets M (bvMultPow2Term z size n exponent u) true := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
    hIspPrem hExponentPrem _hUpperPrem
  have hBool := typed_bv_mult_pow2_term z size n exponent u hZTrans
    hSizeTrans hNTrans hExponentTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvMultPow2Lhs z size n)))
      (__smtx_model_eval M (__eo_to_smt (bvMultPow2Rhs z exponent u)))
    rw [eval_bv_mult_pow2 M hM z size n exponent u hZTrans hSizeTrans
      hNTrans hExponentTrans hResultTy hIspPrem hExponentPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvMultPow2Program
    (z size n exponent u P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_mult_pow2_2b z size n exponent u
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

def bvMultPow2UpperPremRefs
    (sizeOuter sizeDiff n u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) sizeOuter)
        (Term.Apply (Term.UOp UserOp.int_log2)
          (bvMultPow2Diff sizeDiff n))))
      (Term.Numeral 1))

def bvMultPow2Guard
    (size n exponent u sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef
      sizeRef3 sizeRef4 nRef3 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and (__eo_eq size sizeRef1) (__eo_eq n nRef1))
                (__eo_eq exponent exponentRef))
              (__eo_eq size sizeRef2))
            (__eo_eq n nRef2))
          (__eo_eq u uRef))
        (__eo_eq size sizeRef3))
      (__eo_eq size sizeRef4))
    (__eo_eq n nRef3)

private def bvMultPow2ProgramSkeleton
    (z size n exponent u : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.eq)
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.bvmul) z)
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp.bvmul)
            (bvMultPow2Const size n))
          (bvMultPow2Nil z))))
    (bvMultPow2Rhs z exponent u)

private theorem bv_mult_pow2_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h |-
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h |-

theorem bv_mult_pow2_guard_refs
    {size n exponent u sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef
      sizeRef3 sizeRef4 nRef3 body : Term} :
    __eo_requires
        (bvMultPow2Guard size n exponent u sizeRef1 nRef1 exponentRef
          sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3)
        (Term.Boolean true) body ≠ Term.Stuck ->
    sizeRef1 = size ∧ nRef1 = n ∧ exponentRef = exponent ∧
      sizeRef2 = size ∧ nRef2 = n ∧ uRef = u ∧
      sizeRef3 = size ∧ sizeRef4 = size ∧ nRef3 = n := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvMultPow2Guard at hGuard
  rcases bv_mult_pow2_and_true hGuard with ⟨hG8, hN3⟩
  rcases bv_mult_pow2_and_true hG8 with ⟨hG7, hSize4⟩
  rcases bv_mult_pow2_and_true hG7 with ⟨hG6, hSize3⟩
  rcases bv_mult_pow2_and_true hG6 with ⟨hG5, hU⟩
  rcases bv_mult_pow2_and_true hG5 with ⟨hG4, hN2⟩
  rcases bv_mult_pow2_and_true hG4 with ⟨hG3, hSize2⟩
  rcases bv_mult_pow2_and_true hG3 with ⟨hG2, hExponent⟩
  rcases bv_mult_pow2_and_true hG2 with ⟨hSize1, hN1⟩
  exact ⟨support_eq_of_eo_eq_true size sizeRef1 hSize1,
    support_eq_of_eo_eq_true n nRef1 hN1,
    support_eq_of_eo_eq_true exponent exponentRef hExponent,
    support_eq_of_eo_eq_true size sizeRef2 hSize2,
    support_eq_of_eo_eq_true n nRef2 hN2,
    support_eq_of_eo_eq_true u uRef hU,
    support_eq_of_eo_eq_true size sizeRef3 hSize3,
    support_eq_of_eo_eq_true size sizeRef4 hSize4,
    support_eq_of_eo_eq_true n nRef3 hN3⟩

private theorem bv_mult_pow2_premise_shape
    (z size n exponent u P1 P2 P3 : Term) :
    z ≠ Term.Stuck -> size ≠ Term.Stuck -> n ≠ Term.Stuck ->
    exponent ≠ Term.Stuck -> u ≠ Term.Stuck ->
    bvMultPow2Program z size n exponent u P1 P2 P3 ≠ Term.Stuck ->
    ∃ sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3,
      P1 = bvMultPow2IspowPrem sizeRef1 nRef1 ∧
      P2 = bvMultPow2ExponentPrem sizeRef2 nRef2 exponentRef ∧
      P3 = bvMultPow2UpperPremRefs sizeRef3 sizeRef4 nRef3 uRef := by
  intro hZ hSize hN hExponent hU hProg
  by_cases hShape :
      ∃ sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3,
        P1 = bvMultPow2IspowPrem sizeRef1 nRef1 ∧
        P2 = bvMultPow2ExponentPrem sizeRef2 nRef2 exponentRef ∧
        P3 = bvMultPow2UpperPremRefs sizeRef3 sizeRef4 nRef3 uRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_mult_pow2_2b.eq_7 z size n exponent u
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hZ hSize hN hExponent hU (by
        intro sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef
          sizeRef3 sizeRef4 nRef3 hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨sizeRef1, nRef1, exponentRef, sizeRef2, nRef2, uRef,
            sizeRef3, sizeRef4, nRef3, rfl, rfl, rfl⟩)

private theorem bv_mult_pow2_program_canonical
    (z size n exponent u : Term) :
    z ≠ Term.Stuck -> size ≠ Term.Stuck -> n ≠ Term.Stuck ->
    exponent ≠ Term.Stuck -> u ≠ Term.Stuck ->
    bvMultPow2Program z size n exponent u
        (bvMultPow2IspowPrem size n)
        (bvMultPow2ExponentPrem size n exponent)
        (bvMultPow2UpperPrem size n u) =
      bvMultPow2ProgramSkeleton z size n exponent u := by
  intro hZ hSize hN hExponent hU
  unfold bvMultPow2Program bvMultPow2IspowPrem
    bvMultPow2ExponentPrem bvMultPow2UpperPrem bvMultPow2Diff
  rw [__eo_prog_bv_mult_pow2_2b.eq_6 z size n exponent u
    size n exponent size n u size size n hZ hSize hN hExponent hU]
  simp [bvMultPow2ProgramSkeleton, bvMultPow2Const, bvMultPow2Nil,
    bvMultPow2Rhs, bvMultPow2Zeros, bvExtractTerm, __eo_requires,
    __eo_and, __eo_eq, native_ite, native_teq, native_not, native_and,
    hZ, hSize, hN, hExponent, hU]

private theorem bvMultPow2Program_normalize
    (z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    bvMultPow2Program z size n exponent u P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvMultPow2IspowPrem size n ∧
      P2 = bvMultPow2ExponentPrem size n exponent ∧
      P3 = bvMultPow2UpperPrem size n u ∧
      bvMultPow2Program z size n exponent u P1 P2 P3 =
        bvMultPow2ProgramSkeleton z size n exponent u := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hProg
  have hZ := RuleProofs.term_ne_stuck_of_has_smt_translation z hZTrans
  have hSize := RuleProofs.term_ne_stuck_of_has_smt_translation size hSizeTrans
  have hN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hExponent :=
    RuleProofs.term_ne_stuck_of_has_smt_translation exponent hExponentTrans
  have hU := RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
  rcases bv_mult_pow2_premise_shape z size n exponent u P1 P2 P3
      hZ hSize hN hExponent hU hProg with
    ⟨sizeRef1, nRef1, exponentRef, sizeRef2, nRef2, uRef,
      sizeRef3, sizeRef4, nRef3, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvMultPow2Program bvMultPow2IspowPrem bvMultPow2ExponentPrem
    bvMultPow2UpperPremRefs bvMultPow2Diff at hReq
  rw [__eo_prog_bv_mult_pow2_2b.eq_6 z size n exponent u
    sizeRef1 nRef1 exponentRef sizeRef2 nRef2 uRef sizeRef3 sizeRef4 nRef3
    hZ hSize hN hExponent hU] at hReq
  rcases bv_mult_pow2_guard_refs
      (size := size) (n := n) (exponent := exponent) (u := u)
      (sizeRef1 := sizeRef1) (nRef1 := nRef1)
      (exponentRef := exponentRef) (sizeRef2 := sizeRef2)
      (nRef2 := nRef2) (uRef := uRef) (sizeRef3 := sizeRef3)
      (sizeRef4 := sizeRef4) (nRef3 := nRef3)
      (by simpa [bvMultPow2Guard] using hReq) with
    ⟨hSize1, hN1, hExponentRef, hSize2, hN2, hURef,
      hSize3, hSize4, hN3⟩
  subst sizeRef1
  subst nRef1
  subst exponentRef
  subst sizeRef2
  subst nRef2
  subst uRef
  subst sizeRef3
  subst sizeRef4
  subst nRef3
  refine ⟨hP1, hP2, ?_, ?_⟩
  · simpa [bvMultPow2UpperPrem, bvMultPow2UpperPremRefs] using hP3
  · rw [hP1, hP2, hP3]
    simpa [bvMultPow2UpperPrem, bvMultPow2UpperPremRefs] using
      (bv_mult_pow2_program_canonical z size n exponent u
        hZ hSize hN hExponent hU)

theorem bvMultPow2Program_eq_term_of_type_bool
    (z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (bvMultPow2Program z size n exponent u P1 P2 P3) =
      Term.Bool ->
    P1 = bvMultPow2IspowPrem size n ∧
      P2 = bvMultPow2ExponentPrem size n exponent ∧
      P3 = bvMultPow2UpperPrem size n u ∧
      bvMultPow2Program z size n exponent u P1 P2 P3 =
        bvMultPow2Term z size n exponent u := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hTy
  have hProg := term_ne_stuck_of_typeof_bool hTy
  rcases bvMultPow2Program_normalize z size n exponent u P1 P2 P3
      hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hProg with
    ⟨hP1, hP2, hP3, hSkeleton⟩
  refine ⟨hP1, hP2, hP3, ?_⟩
  by_cases hNil : bvMultPow2Nil z = Term.Stuck
  · have hProgramStuck :
        bvMultPow2Program z size n exponent u P1 P2 P3 = Term.Stuck := by
      rw [hSkeleton]
      simp [bvMultPow2ProgramSkeleton, __eo_mk_apply, hNil]
    rw [hProgramStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
    exact False.elim (hBad hTy)
  · by_cases hRhs : bvMultPow2Rhs z exponent u = Term.Stuck
    · have hProgramStuck :
          bvMultPow2Program z size n exponent u P1 P2 P3 = Term.Stuck := by
        rw [hSkeleton]
        simp [bvMultPow2ProgramSkeleton, __eo_mk_apply, hNil, hRhs]
      rw [hProgramStuck] at hTy
      have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
      exact False.elim (hBad hTy)
    · rw [hSkeleton]
      simp [bvMultPow2ProgramSkeleton, bvMultPow2Term, bvMultPow2Lhs,
        __eo_mk_apply, hNil, hRhs]

theorem typed_bv_mult_pow2_program
    (z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (bvMultPow2Program z size n exponent u P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvMultPow2Program z size n exponent u P1 P2 P3) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hResultTy
  rcases bvMultPow2Program_eq_term_of_type_bool z size n exponent u P1 P2 P3
      hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hResultTy with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_mult_pow2_term z size n exponent u hZTrans hSizeTrans
    hNTrans hExponentTrans hTermTy

theorem facts_bv_mult_pow2_program
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    RuleProofs.eo_has_smt_translation u ->
    __eo_typeof (bvMultPow2Program z size n exponent u P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvMultPow2Program z size n exponent u P1 P2 P3) true := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hResultTy
    hP1True hP2True hP3True
  rcases bvMultPow2Program_eq_term_of_type_bool z size n exponent u P1 P2 P3
      hZTrans hSizeTrans hNTrans hExponentTrans hUTrans hResultTy with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvMultPow2Term z size n exponent u) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hIspPrem : eo_interprets M (bvMultPow2IspowPrem size n) true := by
    simpa [hP1] using hP1True
  have hExponentPrem :
      eo_interprets M (bvMultPow2ExponentPrem size n exponent) true := by
    simpa [hP2] using hP2True
  have hUpperPrem :
      eo_interprets M (bvMultPow2UpperPrem size n u) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_mult_pow2_term M hM z size n exponent u hZTrans
    hSizeTrans hNTrans hExponentTrans hTermTy hIspPrem hExponentPrem hUpperPrem
