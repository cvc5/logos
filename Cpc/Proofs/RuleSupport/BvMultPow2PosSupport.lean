module

public import Cpc.Proofs.RuleSupport.BvMultPow2Support
import all Cpc.Proofs.RuleSupport.BvMultPow2Support

public section

/-! Support for multiplication by a positive power of two. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace BvMultPow2PosSupport

def bvMultPow2PosRhs (z exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat)
    (bvExtractTerm z u (Term.Numeral 0))) (bvMultPow2Zeros exponent)

def bvMultPow2PosDirectTerm (z size n exponent u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvMultPow2DirectLhs z size n))
    (bvMultPow2PosRhs z exponent u)

def bvMultPow2PosIspowPrem (n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (Term.Apply (Term.UOp UserOp.int_ispow2) n))
    (Term.Boolean true)

def bvMultPow2PosExponentPrem (n exponent : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) exponent)
    (Term.Apply (Term.UOp UserOp.int_log2) n)

def bvMultPow2PosUpperPrem (size n u : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) u)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) size)
        (Term.Apply (Term.UOp UserOp.int_log2) n)))
      (Term.Numeral 1))

private theorem concat_args_bitvec_of_ne_stuck
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

private theorem direct_context
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2PosDirectTerm z size n exponent u) = Term.Bool ->
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
      (__eo_typeof (bvMultPow2PosRhs z exponent u)) = Term.Bool at hResultTy
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
      __eo_typeof (bvMultPow2PosRhs z exponent u) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypeEq
    exact hTypeEq.symm
  change __eo_typeof_concat
      (__eo_typeof (bvExtractTerm z u (Term.Numeral 0)))
      (__eo_typeof (bvMultPow2Zeros exponent)) ≠ Term.Stuck at hRhsNe
  rcases concat_args_bitvec_of_ne_stuck hRhsNe with
    ⟨extractWidth, zeroWidth, hExtractTy, hZerosTy⟩
  have hZerosNe : __eo_typeof (bvMultPow2Zeros exponent) ≠ Term.Stuck := by
    rw [hZerosTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof (bvMultPow2Const exponent (Term.Numeral 0)))
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck at hZerosNe
  rcases concat_args_bitvec_of_ne_stuck hZerosNe with
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
  have hExtractNe : __eo_typeof (bvExtractTerm z u (Term.Numeral 0)) ≠
      Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck z u (Term.Numeral 0)
      hZTrans hExtractNe with
    ⟨W', U, L, hZTy', hU, hL, hW'0, hL0, hUW', hD0, hZSmtTy'⟩
  have hWW' : W' = W := by
    rw [hZSmtTy] at hZSmtTy'
    have hNat := (SmtType.BitVec.inj hZSmtTy').symm
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
      __eo_typeof (bvExtractTerm z (Term.Numeral U) (Term.Numeral 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    have hGtZero : native_zlt (-1 : native_Int) 0 = true := by decide
    have hGtD : native_zlt (-1 : native_Int) D = true := by
      have hDInt : (0 : Int) < D := by
        simpa [SmtEval.native_zlt] using hDPos
      simpa [SmtEval.native_zlt] using (show (-1 : Int) < D by omega)
    change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral U)
        (Term.UOp UserOp.Int) (Term.Numeral 0) _ = _
    rw [hZTy']
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
        (__eo_typeof (bvExtractTerm z u (Term.Numeral 0)))
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

private theorem smtx_typeof_bvmul_term_eq_pos
    (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.bvmul x y) =
      __smtx_typeof_bv_op_2 (__smtx_typeof x) (__smtx_typeof y) := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem typed_direct_term
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2PosDirectTerm z size n exponent u) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvMultPow2PosDirectTerm z size n exponent u) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
  rcases direct_context z size n exponent u hZTrans hSizeTrans hNTrans
      hExponentTrans hResultTy with
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
    rw [smtx_typeof_bvmul_term_eq_pos]
    simp [__smtx_typeof_bv_op_2, hZSmtTy, hConstTy, native_nateq,
      native_ite]
  have hZeroTy :
      __smtx_typeof
          (__eo_to_smt
            (bvMultPow2Const (Term.Numeral E) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat E) :=
    smtx_typeof_int_to_bv_numerals E 0 hE0
  have hEInt : (0 : Int) ≤ E := by
    simpa [SmtEval.native_zleq] using hE0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hDInt : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have hExtractTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm z (Term.Numeral U) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat D) := by
    have hSlice :
        native_zplus (native_zplus U 1) (native_zneg 0) = D := by
      simp [hD, SmtEval.native_zplus, SmtEval.native_zneg]
    rw [← hSlice]
    exact smt_typeof_extract_of_context z W U 0 hZSmtTy hW0 (by decide)
      hUW (by simpa [hSlice] using hDPos)
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
      Smtm.native_nat_to_int, SmtEval.native_zplus,
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
            (bvMultPow2PosRhs z (Term.Numeral E) (Term.Numeral U))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm z (Term.Numeral U) (Term.Numeral 0)))
          (__eo_to_smt (bvMultPow2Zeros (Term.Numeral E)))) = _
    rw [typeof_concat_eq, hExtractTy, hZerosTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int, SmtEval.native_zplus, hWidthNat,
      hDRound, hERound, hDE, hDEInt, Int.max_eq_left hDInt,
      Int.max_eq_left hEInt]
  unfold bvMultPow2PosDirectTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

private theorem model_eval_eq_true_of_eo_eq_true
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

private theorem premises_numeric
    (M : SmtModel) (hM : model_wf M)
    (n : Term) (E : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    eo_interprets M (bvMultPow2PosIspowPrem n) true ->
    eo_interprets M
      (bvMultPow2PosExponentPrem n (Term.Numeral E)) true ->
    ∃ N : native_Int,
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral N ∧
      N = native_int_pow2 E := by
  intro hNTy hIspPrem hExponentPrem
  rcases CongSupport.smt_eval_int_of_smt_type_int M hM (__eo_to_smt n)
      hNTy with ⟨N, hNEval⟩
  have hExponentEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral E) (Term.Apply (Term.UOp UserOp.int_log2) n)
    (by simpa [bvMultPow2PosExponentPrem] using hExponentPrem)
  change __smtx_model_eval_eq (SmtValue.Numeral E)
      (__smtx_model_eval_int_log2
        (__smtx_model_eval M (__eo_to_smt n))) =
    SmtValue.Boolean true at hExponentEq
  rw [hNEval] at hExponentEq
  have hELog : E = native_int_log2 N := by
    simpa [__smtx_model_eval_int_log2, __smtx_model_eval_eq,
      native_veq, SmtEval.native_zeq] using hExponentEq
  have hIspEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.UOp UserOp.int_ispow2) n) (Term.Boolean true)
    (by simpa [bvMultPow2PosIspowPrem] using hIspPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval_and
        (__smtx_model_eval_geq
          (__smtx_model_eval M (__eo_to_smt n)) (SmtValue.Numeral 0))
        (__smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt n))
          (__smtx_model_eval_int_pow2
            (__smtx_model_eval_int_log2
              (__smtx_model_eval M (__eo_to_smt n))))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hIspEq
  rw [hNEval] at hIspEq
  have hNPow : N = native_int_pow2 (native_int_log2 N) := by
    have hParts :
        (0 : Int) ≤ N ∧ N = native_int_pow2 (native_int_log2 N) := by
      simpa [__smtx_model_eval_int_log2, __smtx_model_eval_int_pow2,
        __smtx_model_eval_and, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_zeq, SmtEval.native_zleq, native_and,
        Bool.and_eq_true] using hIspEq
    exact hParts.2
  exact ⟨N, hNEval, by rw [hELog]; exact hNPow⟩

private theorem ofInt_pow2_eq_twoPow
    (D E : Nat) (hD : 0 < D) :
    BitVec.ofInt (D + E) ((2 : Int) ^ E) =
      BitVec.twoPow (D + E) E := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_twoPow]
  have hPowE : (2 : Int) ^ E = ((2 ^ E : Nat) : Int) := by norm_cast
  rw [hPowE]
  have hLt : 2 ^ E < 2 ^ (D + E) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le _)
    (by exact_mod_cast hLt)]
  rw [Int.toNat_natCast, Nat.mod_eq_of_lt hLt]

private theorem bitvec_mult_pow2_pos_core_toNat
    (D E W : Nat) (hWidth : D + E = W) (hD : 0 < D)
    (x : BitVec W) :
    (x * BitVec.ofInt W ((2 : Int) ^ E)).toNat =
      (x.extractLsb' 0 D ++ 0#E).toNat := by
  subst W
  have hELt : E < D + E := by omega
  have hEq :
      x * BitVec.ofInt (D + E) ((2 : Int) ^ E) =
        x.extractLsb' 0 D ++ 0#E := by
    rw [ofInt_pow2_eq_twoPow D E hD]
    rw [BitVec.mul_twoPow_eq_shiftLeft]
    rw [BitVec.shiftLeft_eq_concat_of_lt hELt]
    have hLen : D + E - E = D := by omega
    apply BitVec.eq_of_toNat_eq
    simp [hLen]
  exact congrArg BitVec.toNat hEq

theorem eval_direct
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2PosDirectTerm z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2PosIspowPrem n) true ->
    eo_interprets M (bvMultPow2PosExponentPrem n exponent) true ->
    __smtx_model_eval M (__eo_to_smt (bvMultPow2DirectLhs z size n)) =
      __smtx_model_eval M (__eo_to_smt (bvMultPow2PosRhs z exponent u)) := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
    hIspPrem hExponentPrem
  rcases direct_context z size n exponent u hZTrans hSizeTrans hNTrans
      hExponentTrans hResultTy with
    ⟨W, E, U, D, rfl, rfl, rfl, hW0, hE0, hU0, hUW, hD,
      hDPos, hDE, hZTy, hZSmtTy, hNSmtTy⟩
  let WN := native_int_to_nat W
  let EN := native_int_to_nat E
  let DN := native_int_to_nat D
  have hD0 : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hWRound : (native_nat_to_int WN : Int) = W := by
    simpa [WN, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip W hW0
  have hERound : (native_nat_to_int EN : Int) = E := by
    simpa [EN, native_nat_to_int, Smtm.native_nat_to_int] using
      native_int_to_nat_roundtrip E hE0
  have hDRound : (native_nat_to_int DN : Int) = D := by
    simpa [DN, native_nat_to_int, Smtm.native_nat_to_int] using
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
    simp [SmtEval.native_zleq, native_nat_to_int, Smtm.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hZCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ WN := by
    simpa [natpow2_eq, native_nat_to_int,
      Smtm.native_nat_to_int] using hRange.2
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
      eo_interprets M (bvMultPow2PosIspowPrem n) true := by
    simpa using hIspPrem
  have hExponentPrem' :
      eo_interprets M
        (bvMultPow2PosExponentPrem n (Term.Numeral E)) true := by
    simpa using hExponentPrem
  rcases premises_numeric M hM n E hNSmtTy hIspPrem' hExponentPrem' with
    ⟨N, hNEval, hN⟩
  have hNativePowW : native_int_pow2 W = (2 : Int) ^ WN := by
    rw [← hWRound]
    exact native_int_pow2_nat WN
  have hNativePowE : native_int_pow2 E = (2 : Int) ^ EN := by
    rw [← hERound]
    exact native_int_pow2_nat EN
  have hNPow : N = (2 : Int) ^ EN := by
    simpa [hNativePowE] using hN
  have hENLtWN : EN < WN := by
    calc
      EN < DN + EN := Nat.lt_add_of_pos_left hDNPos
      _ = WN := hWidthNat
  have hN0 : (0 : Int) ≤ N := by
    rw [hNPow]
    exact_mod_cast Nat.zero_le (2 ^ EN)
  have hNLt : N < (2 : Int) ^ WN := by
    rw [hNPow]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) hENLtWN
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
  have hSliceWidth : U + 1 + -0 = (DN : Int) := by
    calc
      U + 1 + -0 = D := by
        simpa [SmtEval.native_zplus] using hD.symm
      _ = (DN : Int) := by
        simpa [native_nat_to_int, Smtm.native_nat_to_int] using hDRound.symm
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm z (Term.Numeral U) (Term.Numeral 0))) =
        SmtValue.Binary (native_nat_to_int DN)
          ((x.extractLsb' 0 DN).toNat : Int) := by
    rw [eval_extract_term, hZEval']
    have hExtract := extract_val_bitvec_start_len WN 0 DN (x.toNat : Int)
      U 0 (Int.natCast_nonneg _) (by exact_mod_cast x.isLt) (by simp)
      hSliceWidth
    have hOf : BitVec.ofInt WN (x.toNat : Int) = x :=
      bitvec_ofInt_natCast_toNat x
    rw [hOf] at hExtract
    simpa [native_nat_to_int, Smtm.native_nat_to_int] using hExtract
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
            (bvMultPow2PosRhs z (Term.Numeral E) (Term.Numeral U))) =
        SmtValue.Binary (native_nat_to_int WN)
          ((x.extractLsb' 0 DN ++ 0#EN).toNat : Int) := by
    unfold bvMultPow2PosRhs
    rw [eval_concat_term M _ _ _ _ hExtractEval hZerosEval]
    have hConcat := concat_zero_bitvec_value_mult_pow2 DN EN
      (x.extractLsb' 0 DN)
    have hWidthInt : native_nat_to_int (DN + EN) = native_nat_to_int WN :=
      congrArg native_nat_to_int hWidthNat
    rw [hWidthInt] at hConcat
    exact hConcat
  rw [hLhsEval, hRhsEval]
  congr 2
  have hNBitVec : nBv = BitVec.ofInt WN ((2 : Int) ^ EN) := by
    simp [nBv, hNPow]
  rw [hNBitVec]
  exact bitvec_mult_pow2_pos_core_toNat DN EN WN hWidthNat hDNPos x

theorem facts_direct_term
    (M : SmtModel) (hM : model_wf M)
    (z size n exponent u : Term) :
    RuleProofs.eo_has_smt_translation z ->
    RuleProofs.eo_has_smt_translation size ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation exponent ->
    __eo_typeof (bvMultPow2PosDirectTerm z size n exponent u) = Term.Bool ->
    eo_interprets M (bvMultPow2PosIspowPrem n) true ->
    eo_interprets M (bvMultPow2PosExponentPrem n exponent) true ->
    eo_interprets M (bvMultPow2PosUpperPrem size n u) true ->
    eo_interprets M (bvMultPow2PosDirectTerm z size n exponent u) true := by
  intro hZTrans hSizeTrans hNTrans hExponentTrans hResultTy
    hIspPrem hExponentPrem _hUpperPrem
  have hBool := typed_direct_term z size n exponent u hZTrans hSizeTrans
    hNTrans hExponentTrans hResultTy
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvMultPow2DirectLhs z size n)))
      (__smtx_model_eval M (__eo_to_smt (bvMultPow2PosRhs z exponent u)))
    rw [eval_direct M hM z size n exponent u hZTrans hSizeTrans hNTrans
      hExponentTrans hResultTy hIspPrem hExponentPrem]
    exact RuleProofs.smt_value_rel_refl _

end BvMultPow2PosSupport
