module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.BvSdivElimSupport
import all Cpc.Proofs.RuleSupport.BvSdivElimSupport
public import Cpc.Proofs.RuleSupport.Cong.Core
import all Cpc.Proofs.RuleSupport.Cong.Core

public section

/-! Support for the unsigned division/remainder by a nontrivial power of two. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvPow2Const (v n : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv n) v

def bvUdivPow2Lhs (x v n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) x) (bvPow2Const v n)

def bvUdivPow2Rhs (x power nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat)
    (bvPow2Const (Term.Numeral 0) power))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x nm power)) (Term.Binary 0 0))

def bvUdivPow2Term (x v n power nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvUdivPow2Lhs x v n)) (bvUdivPow2Rhs x power nm)

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck
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

private theorem bv_udiv_pow2_context
    (x v n power nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    __eo_typeof (bvUdivPow2Term x v n power nm) = Term.Bool ->
    ∃ W P N D : native_Int,
      n = Term.Numeral W ∧ power = Term.Numeral P ∧
      nm = Term.Numeral N ∧
      native_zleq 0 W = true ∧ native_zleq 0 P = true ∧
      native_zlt N W = true ∧
      D = native_zplus (native_zplus N 1) (native_zneg P) ∧
      native_zlt 0 D = true ∧ native_zplus P D = W ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt v) = SmtType.Int := by
  intro hXTrans hVTrans hNTrans hPowerTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x) (__eo_typeof (bvPow2Const v n)))
      (__eo_typeof (bvUdivPow2Rhs x power nm)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hLhsNe with
    ⟨widthTerm, hXTy, hConstTy⟩
  have hVNe := RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  rcases bv_all_ones_const_context v n widthTerm hVNe hNNe
      (by simpa [bvPow2Const, bvAllOnesConst] using hConstTy) with
    ⟨W, hN, hWidth, hW0, hVTy⟩
  subst widthTerm
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [__eo_to_smt_type, hW0, native_ite] using
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt x) rfl hXTrans hXTy)
  have hVSmtTy : __smtx_typeof (__eo_to_smt v) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      v (Term.UOp UserOp.Int) (__eo_to_smt v) rfl hVTrans hVTy
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hLhsTy :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof (bvPow2Const v n)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hXTy, hConstTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRhsTy :
      __eo_typeof (bvUdivPow2Rhs x power nm) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypeEq
    exact hTypeEq.symm
  change __eo_typeof_concat
      (__eo_typeof (bvPow2Const (Term.Numeral 0) power))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x nm power)) (Term.Binary 0 0))) ≠
    Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck hRhsNe with
    ⟨pWidth, tailWidth, hZeroTy, hTailTy⟩
  have hPowerNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation power hPowerTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) power pWidth
      (by simp) hPowerNe
      (by simpa [bvPow2Const, bvAllOnesConst] using hZeroTy) with
    ⟨P, hPower, hpWidth, hP0, _hZeroArgTy⟩
  subst pWidth
  have hTailNe :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x nm power)) (Term.Binary 0 0)) ≠
        Term.Stuck := by
    rw [hTailTy]
    intro h
    cases h
  change __eo_typeof_concat (__eo_typeof (bvExtractTerm x nm power))
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck at hTailNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck hTailNe with
    ⟨extractWidth, emptyWidth, hExtractTy, _hEmptyTy⟩
  have hExtractNe : __eo_typeof (bvExtractTerm x nm power) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x nm power hXTrans hExtractNe with
    ⟨W', N, P', hXTy', hNm, hPower', hW'0, hP'0, hNW', hD0,
      hXSmtTy'⟩
  have hWW' : W' = W := by
    rw [hXSmtTy] at hXSmtTy'
    have hNat := (SmtType.BitVec.inj hXSmtTy').symm
    exact nonneg_int_eq_of_toNat_eq W' W hW'0 hW0 hNat
  subst W'
  have hPP' : P' = P := by
    rw [hPower] at hPower'
    injection hPower' with h
    exact h.symm
  subst P'
  let D := native_zplus (native_zplus N 1) (native_zneg P)
  have hDPos : native_zlt 0 D = true := by
    simpa [D] using hD0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hDPos
  have hGtP : native_zlt (-1 : native_Int) P = true := by
    have hPInt : (0 : Int) ≤ P := by
      simpa [SmtEval.native_zleq] using hP'0
    have : (-1 : Int) < P := by omega
    simpa [SmtEval.native_zlt] using this
  have hDForm :
      native_zplus (native_zplus N (native_zneg P)) 1 = D := by
    simp [D, SmtEval.native_zplus, SmtEval.native_zneg,
      Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have hGtDDirect : native_zlt (-1 : native_Int) D = true := by
    have hDInt : (0 : Int) ≤ D := by
      simpa [SmtEval.native_zleq] using hDNonneg
    have : (-1 : Int) < D := by omega
    simpa [SmtEval.native_zlt] using this
  have hGtD :
      native_zlt (-1 : native_Int)
        (native_zplus (native_zplus N (native_zneg P)) 1) = true := by
    have hDInt : (0 : Int) ≤ D := by
      simpa [SmtEval.native_zleq] using hDNonneg
    have : (-1 : Int) <
        native_zplus (native_zplus N (native_zneg P)) 1 := by
      rw [hDForm]
      omega
    simpa [SmtEval.native_zlt] using this
  have hExtractEoTy :
      __eo_typeof (bvExtractTerm x (Term.Numeral N) (Term.Numeral P)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral N)
        (Term.UOp UserOp.Int) (Term.Numeral P) (__eo_typeof x) = _
    rw [hXTy']
    simp [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt,
      __eo_requires, __eo_mk_apply, native_ite, native_teq, native_not,
      hGtP, hNW', hDPos, hGtD, hGtDDirect, hDForm, D]
  have hExtractWidth : extractWidth = Term.Numeral D := by
    rw [hNm, hPower', hExtractEoTy] at hExtractTy
    injection hExtractTy with _ h
    exact h.symm
  subst extractWidth
  have hTailTyD :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x nm power))
            (Term.Binary 0 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    change __eo_typeof_concat (__eo_typeof (bvExtractTerm x nm power))
        (__eo_typeof (Term.Binary 0 0)) = _
    rw [hNm, hPower', hExtractEoTy]
    change __eo_typeof_concat
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D))
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) = _
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus]
  have hRhsWidth : native_zplus P D = W := by
    have hRhsTy' := hRhsTy
    change __eo_typeof_concat
        (__eo_typeof (bvPow2Const (Term.Numeral 0) power))
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x nm power)) (Term.Binary 0 0))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) at hRhsTy'
    rw [hZeroTy, hTailTyD] at hRhsTy'
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus] at hRhsTy'
    exact hRhsTy'
  exact ⟨W, P, N, D, hN, hPower, hNm, hW0, hP0, hNW',
    rfl, hDPos, hRhsWidth, hXSmtTy, hVSmtTy⟩

private theorem typed_bv_udiv_pow2_term
    (x v n power nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    __eo_typeof (bvUdivPow2Term x v n power nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvUdivPow2Term x v n power nm) := by
  intro hXTrans hVTrans hNTrans hPowerTrans hResultTy
  rcases bv_udiv_pow2_context x v n power nm hXTrans hVTrans hNTrans
      hPowerTrans hResultTy with
    ⟨W, P, N, D, rfl, rfl, rfl, hW0, hP0, hNW, hD, hD0, hPD,
      hXSmtTy, hVSmtTy⟩
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt (bvPow2Const v (Term.Numeral W))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt v)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hVSmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW0]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvUdivPow2Lhs x v (Term.Numeral W))) =
        SmtType.BitVec (native_int_to_nat W) := by
    exact smt_typeof_bvbin_same SmtTerm.bvudiv
      (by intro a b; rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ _ hXSmtTy hConstTy
  have hZeroTy :
      __smtx_typeof
          (__eo_to_smt
            (bvPow2Const (Term.Numeral 0) (Term.Numeral P))) =
        SmtType.BitVec (native_int_to_nat P) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral P) (SmtTerm.Numeral 0)) = _
    exact smtx_typeof_int_to_bv_numerals P 0 hP0
  have hExtractTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral P))) =
        SmtType.BitVec (native_int_to_nat D) := by
    simpa [hD] using smt_typeof_extract_of_context x W N P hXSmtTy
      hW0 hP0 hNW (by simpa [hD] using hD0)
  have hPInt : (0 : Int) ≤ P := by
    simpa [SmtEval.native_zleq] using hP0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hD0
  have hDInt : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have hTailTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
              (bvExtractTerm x (Term.Numeral N) (Term.Numeral P)))
              (Term.Binary 0 0))) =
        SmtType.BitVec (native_int_to_nat D) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral P)))
          (SmtTerm.Binary 0 0)) = _
    rw [typeof_concat_eq, hExtractTy]
    have hEmptyTy :
        __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
      simp [__smtx_typeof, SmtEval.native_and, native_ite,
        SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
        native_mod_total, native_int_to_nat, SmtEval.native_int_to_nat]
    rw [hEmptyTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int, SmtEval.native_zplus,
      Int.max_eq_left hDInt]
  have hPRound := native_int_to_nat_roundtrip P hP0
  have hDRound := native_int_to_nat_roundtrip D hDNonneg
  have hPDInt : P + D = W := by
    simpa [SmtEval.native_zplus] using hPD
  have hWidthNat :
      native_int_to_nat P + native_int_to_nat D = native_int_to_nat W := by
    simp only [native_int_to_nat, SmtEval.native_int_to_nat]
    rw [← Int.toNat_add hPInt hDInt]
    simpa [SmtEval.native_zplus] using congrArg Int.toNat hPD
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvUdivPow2Rhs x (Term.Numeral P) (Term.Numeral N))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvPow2Const (Term.Numeral 0) (Term.Numeral P)))
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
              (bvExtractTerm x (Term.Numeral N) (Term.Numeral P)))
              (Term.Binary 0 0)))) = _
    rw [typeof_concat_eq, hZeroTy, hTailTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int, SmtEval.native_zplus, hWidthNat,
      hPRound, hDRound, hPD, hPDInt, Int.max_eq_left hPInt,
      Int.max_eq_left hDInt]
  unfold bvUdivPow2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

def bvPow2IspowPrem (v : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (Term.Apply (Term.UOp UserOp.int_ispow2) v)) (Term.Boolean true)

def bvPow2GtOnePrem (v : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) v) (Term.Numeral 1)))
    (Term.Boolean true)

def bvPow2PowerPrem (v power : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) power)
    (Term.Apply (Term.UOp UserOp.int_log2) v)

def bvUdivPow2NmPrem (n nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) (Term.Numeral 1))

private theorem model_eval_eq_true_of_eo_eq_true_pow2
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

private theorem bv_udiv_pow2_premises_numeric
    (M : SmtModel) (hM : model_wf M)
    (v : Term) (W P N : native_Int) :
    __smtx_typeof (__eo_to_smt v) = SmtType.Int ->
    eo_interprets M (bvPow2IspowPrem v) true ->
    eo_interprets M (bvPow2GtOnePrem v) true ->
    eo_interprets M (bvPow2PowerPrem v (Term.Numeral P)) true ->
    eo_interprets M
      (bvUdivPow2NmPrem (Term.Numeral W) (Term.Numeral N)) true ->
    ∃ V : native_Int,
      __smtx_model_eval M (__eo_to_smt v) = SmtValue.Numeral V ∧
      V = native_int_pow2 P ∧ 1 < V ∧
      N = native_zplus W (native_zneg 1) := by
  intro hVTy hIspPrem hGtPrem hPowerPrem hNmPrem
  rcases CongSupport.smt_eval_int_of_smt_type_int M hM (__eo_to_smt v)
      hVTy with ⟨V, hVEval⟩
  have hPowerEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Numeral P) (Term.Apply (Term.UOp UserOp.int_log2) v)
    (by simpa [bvPow2PowerPrem] using hPowerPrem)
  change __smtx_model_eval_eq (SmtValue.Numeral P)
      (__smtx_model_eval_int_log2
        (__smtx_model_eval M (__eo_to_smt v))) =
    SmtValue.Boolean true at hPowerEq
  rw [hVEval] at hPowerEq
  change __smtx_model_eval_eq (SmtValue.Numeral P)
      (__smtx_model_eval_int_log2 (SmtValue.Numeral V)) =
    SmtValue.Boolean true at hPowerEq
  have hPLog : P = native_int_log2 V := by
    simpa [__smtx_model_eval_int_log2, __smtx_model_eval_eq,
      native_veq, SmtEval.native_zeq] using hPowerEq
  have hIspEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Apply (Term.UOp UserOp.int_ispow2) v) (Term.Boolean true)
    (by simpa [bvPow2IspowPrem] using hIspPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval_and
        (__smtx_model_eval_geq (__smtx_model_eval M (__eo_to_smt v))
          (SmtValue.Numeral 0))
        (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt v))
          (__smtx_model_eval_int_pow2
            (__smtx_model_eval_int_log2
              (__smtx_model_eval M (__eo_to_smt v))))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hIspEq
  rw [hVEval] at hIspEq
  have hVPowLog : V = native_int_pow2 (native_int_log2 V) := by
    have hParts :
        (0 : Int) ≤ V ∧ V = native_int_pow2 (native_int_log2 V) := by
      simpa [__smtx_model_eval_int_log2, __smtx_model_eval_int_pow2,
        __smtx_model_eval_and, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_zeq, SmtEval.native_zleq, native_and,
        Bool.and_eq_true] using hIspEq
    exact hParts.2
  have hVPow : V = native_int_pow2 P := by
    rw [hPLog]
    exact hVPowLog
  have hGtEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) v) (Term.Numeral 1))
    (Term.Boolean true) (by simpa [bvPow2GtOnePrem] using hGtPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval_gt (__smtx_model_eval M (__eo_to_smt v))
        (SmtValue.Numeral 1))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hGtEq
  rw [hVEval] at hGtEq
  change __smtx_model_eval_eq
      (__smtx_model_eval_gt (SmtValue.Numeral V) (SmtValue.Numeral 1))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hGtEq
  have hVOne : 1 < V := by
    simpa [__smtx_model_eval_gt, __smtx_model_eval_lt,
      __smtx_model_eval_eq, native_veq, SmtEval.native_zeq,
      SmtEval.native_zlt] using hGtEq
  have hNmEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Numeral N)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral W))
      (Term.Numeral 1))
    (by simpa [bvUdivPow2NmPrem] using hNmPrem)
  change __smtx_model_eval_eq (SmtValue.Numeral N)
      (__smtx_model_eval__
        (SmtValue.Numeral W) (SmtValue.Numeral 1)) =
    SmtValue.Boolean true at hNmEq
  have hNW : N = native_zplus W (native_zneg 1) := by
    simpa [__smtx_model_eval__, __smtx_model_eval_eq,
      native_veq, SmtEval.native_zeq, SmtEval.native_zplus,
      SmtEval.native_zneg] using hNmEq
  exact ⟨V, hVEval, hVPow, hVOne, hNW⟩

def bvUremPow2Lhs (x v n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) x) (bvPow2Const v n)

def bvUremPow2Rhs (x nmp pm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat)
    (bvPow2Const (Term.Numeral 0) nmp))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x pm (Term.Numeral 0))) (Term.Binary 0 0))

def bvUremPow2Term (x v n nmp pm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvUremPow2Lhs x v n)) (bvUremPow2Rhs x nmp pm)

def bvUremPow2NmpPrem (v n nmp : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nmp)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n)
      (Term.Apply (Term.UOp UserOp.int_log2) v))

def bvUremPow2PmPrem (v pm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) pm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp.int_log2) v)) (Term.Numeral 1))

private theorem bv_urem_pow2_context
    (x v n nmp pm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    __eo_typeof (bvUremPow2Term x v n nmp pm) = Term.Bool ->
    ∃ W A Q D : native_Int,
      n = Term.Numeral W ∧ nmp = Term.Numeral A ∧
      pm = Term.Numeral Q ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zlt Q W = true ∧
      D = native_zplus Q 1 ∧ native_zlt 0 D = true ∧
      native_zplus A D = W ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt v) = SmtType.Int := by
  intro hXTrans hVTrans hNTrans hNmpTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x) (__eo_typeof (bvPow2Const v n)))
      (__eo_typeof (bvUremPow2Rhs x nmp pm)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hLhsNe with
    ⟨widthTerm, hXTy, hConstTy⟩
  have hVNe := RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
  have hNNe := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  rcases bv_all_ones_const_context v n widthTerm hVNe hNNe
      (by simpa [bvPow2Const, bvAllOnesConst] using hConstTy) with
    ⟨W, hN, hWidth, hW0, hVTy⟩
  subst widthTerm
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [__eo_to_smt_type, hW0, native_ite] using
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt x) rfl hXTrans hXTy)
  have hVSmtTy : __smtx_typeof (__eo_to_smt v) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      v (Term.UOp UserOp.Int) (__eo_to_smt v) rfl hVTrans hVTy
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hLhsTy :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof (bvPow2Const v n)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hXTy, hConstTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRhsTy :
      __eo_typeof (bvUremPow2Rhs x nmp pm) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypeEq
    exact hTypeEq.symm
  change __eo_typeof_concat
      (__eo_typeof (bvPow2Const (Term.Numeral 0) nmp))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x pm (Term.Numeral 0))) (Term.Binary 0 0))) ≠
    Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck hRhsNe with
    ⟨aWidth, tailWidth, hZeroTy, hTailTy⟩
  have hNmpNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmp hNmpTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) nmp aWidth
      (by simp) hNmpNe
      (by simpa [bvPow2Const, bvAllOnesConst] using hZeroTy) with
    ⟨A, hNmp, haWidth, hA0, _hZeroArgTy⟩
  subst aWidth
  have hTailNe :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x pm (Term.Numeral 0))) (Term.Binary 0 0)) ≠
        Term.Stuck := by
    rw [hTailTy]
    intro h
    cases h
  change __eo_typeof_concat
      (__eo_typeof (bvExtractTerm x pm (Term.Numeral 0)))
      (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck at hTailNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck hTailNe with
    ⟨extractWidth, emptyWidth, hExtractTy, _hEmptyTy⟩
  have hExtractNe :
      __eo_typeof (bvExtractTerm x pm (Term.Numeral 0)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x pm (Term.Numeral 0)
      hXTrans hExtractNe with
    ⟨W', Q, L, hXTy', hPm, hLow, hW'0, hL0, hQW', hD0Raw,
      hXSmtTy'⟩
  have hL : L = 0 := by
    injection hLow with h
    exact h.symm
  subst L
  have hWW' : W' = W := by
    rw [hXSmtTy] at hXSmtTy'
    have hNat := (SmtType.BitVec.inj hXSmtTy').symm
    exact nonneg_int_eq_of_toNat_eq W' W hW'0 hW0 hNat
  subst W'
  let D := native_zplus Q 1
  have hDForm :
      native_zplus (native_zplus Q 1) (native_zneg 0) = D := by
    simp [D, SmtEval.native_zplus, SmtEval.native_zneg]
  have hD0 : native_zlt 0 D = true := by
    simpa [hDForm] using hD0Raw
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hD0
  have hGtZero : native_zlt (-1 : native_Int) 0 = true := by native_decide
  have hGtD : native_zlt (-1 : native_Int) D = true := by
    have hDInt : (0 : Int) ≤ D := by
      simpa [SmtEval.native_zleq] using hDNonneg
    have : (-1 : Int) < D := by omega
    simpa [SmtEval.native_zlt] using this
  have hGtD' :
      native_zlt (-1 : native_Int) (native_zplus Q 1) = true := by
    simpa [D] using hGtD
  have hGtDInt : native_zlt (-1 : native_Int) (Q + 1) = true := by
    simpa [SmtEval.native_zplus] using hGtD'
  have hDPosInt : native_zlt 0 (Q + 1) = true := by
    simpa [D, SmtEval.native_zplus] using hD0
  have hExtractEoTy :
      __eo_typeof (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    change __eo_typeof_extract (Term.UOp UserOp.Int) (Term.Numeral Q)
        (Term.UOp UserOp.Int) (Term.Numeral 0) (__eo_typeof x) = _
    rw [hXTy']
    simp [__eo_typeof_extract, __eo_add, __eo_neg, __eo_gt,
      __eo_requires, __eo_mk_apply, native_ite, native_teq, native_not,
      hGtZero, hQW', hD0, hDPosInt, hGtD, hGtD', hGtDInt, hDForm, D,
      SmtEval.native_zplus,
      SmtEval.native_zneg]
  have hExtractWidth : extractWidth = Term.Numeral D := by
    rw [hPm, hExtractEoTy] at hExtractTy
    injection hExtractTy with _ h
    exact h.symm
  subst extractWidth
  have hTailTyD :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x pm (Term.Numeral 0))) (Term.Binary 0 0)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D) := by
    change __eo_typeof_concat
        (__eo_typeof (bvExtractTerm x pm (Term.Numeral 0)))
        (__eo_typeof (Term.Binary 0 0)) = _
    rw [hPm, hExtractEoTy]
    change __eo_typeof_concat
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral D))
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 0)) = _
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus]
  have hRhsWidth : native_zplus A D = W := by
    have hRhsTy' := hRhsTy
    change __eo_typeof_concat
        (__eo_typeof (bvPow2Const (Term.Numeral 0) nmp))
        (__eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x pm (Term.Numeral 0))) (Term.Binary 0 0))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) at hRhsTy'
    rw [hZeroTy, hTailTyD] at hRhsTy'
    simp [__eo_typeof_concat, __eo_add, __eo_mk_apply,
      SmtEval.native_zplus] at hRhsTy'
    exact hRhsTy'
  exact ⟨W, A, Q, D, hN, hNmp, hPm, hW0, hA0, hQW', rfl,
    hD0, hRhsWidth, hXSmtTy, hVSmtTy⟩

private theorem typed_bv_urem_pow2_term
    (x v n nmp pm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    __eo_typeof (bvUremPow2Term x v n nmp pm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvUremPow2Term x v n nmp pm) := by
  intro hXTrans hVTrans hNTrans hNmpTrans hResultTy
  rcases bv_urem_pow2_context x v n nmp pm hXTrans hVTrans hNTrans
      hNmpTrans hResultTy with
    ⟨W, A, Q, D, rfl, rfl, rfl, hW0, hA0, hQW, hD, hD0, hAD,
      hXSmtTy, hVSmtTy⟩
  have hConstTy :
      __smtx_typeof
          (__eo_to_smt (bvPow2Const v (Term.Numeral W))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt v)) = _
    rw [smtx_typeof_int_to_bv_term_eq, hVSmtTy]
    simp [__smtx_typeof_int_to_bv, native_ite, hW0]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (bvUremPow2Lhs x v (Term.Numeral W))) =
        SmtType.BitVec (native_int_to_nat W) := by
    exact smt_typeof_bvbin_same SmtTerm.bvurem
      (by intro a b; rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ _ hXSmtTy hConstTy
  have hZeroTy :
      __smtx_typeof
          (__eo_to_smt
            (bvPow2Const (Term.Numeral 0) (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat A) := by
    change __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral A) (SmtTerm.Numeral 0)) = _
    exact smtx_typeof_int_to_bv_numerals A 0 hA0
  have hZero0 : native_zleq 0 (0 : native_Int) = true := by native_decide
  have hExtractTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0))) =
        SmtType.BitVec (native_int_to_nat D) := by
    simpa [hD, SmtEval.native_zplus, SmtEval.native_zneg] using
      smt_typeof_extract_of_context x W Q 0 hXSmtTy hW0 hZero0 hQW
        (by simpa [hD, SmtEval.native_zplus, SmtEval.native_zneg] using hD0)
  have hAInt : (0 : Int) ≤ A := by
    simpa [SmtEval.native_zleq] using hA0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hD0
  have hDInt : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have hTailTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
              (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0)))
              (Term.Binary 0 0))) =
        SmtType.BitVec (native_int_to_nat D) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0)))
          (SmtTerm.Binary 0 0)) = _
    rw [typeof_concat_eq, hExtractTy]
    have hEmptyTy :
        __smtx_typeof (SmtTerm.Binary 0 0) = SmtType.BitVec 0 := by
      simp [__smtx_typeof, SmtEval.native_and, native_ite,
        SmtEval.native_zleq, native_zeq, SmtEval.native_zeq,
        native_mod_total, native_int_to_nat, SmtEval.native_int_to_nat]
    rw [hEmptyTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int, SmtEval.native_zplus,
      Int.max_eq_left hDInt]
  have hWidthNat :
      native_int_to_nat A + native_int_to_nat D = native_int_to_nat W := by
    simp only [native_int_to_nat, SmtEval.native_int_to_nat]
    rw [← Int.toNat_add hAInt hDInt]
    simpa [SmtEval.native_zplus] using congrArg Int.toNat hAD
  have hARound := native_int_to_nat_roundtrip A hA0
  have hDRound := native_int_to_nat_roundtrip D hDNonneg
  have hADInt : A + D = W := by
    simpa [SmtEval.native_zplus] using hAD
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvUremPow2Rhs x (Term.Numeral A) (Term.Numeral Q))) =
        SmtType.BitVec (native_int_to_nat W) := by
    change __smtx_typeof
        (SmtTerm.concat
          (__eo_to_smt
            (bvPow2Const (Term.Numeral 0) (Term.Numeral A)))
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
              (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0)))
              (Term.Binary 0 0)))) = _
    rw [typeof_concat_eq, hZeroTy, hTailTy]
    simp [__smtx_typeof_concat, native_int_to_nat,
      SmtEval.native_int_to_nat, native_nat_to_int,
      Smtm.native_nat_to_int, SmtEval.native_zplus, hWidthNat,
      hARound, hDRound, hAD, hADInt, Int.max_eq_left hAInt,
      Int.max_eq_left hDInt]
  unfold bvUremPow2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

private theorem bv_urem_pow2_premises_numeric
    (M : SmtModel) (hM : model_wf M)
    (v : Term) (W A Q : native_Int) :
    __smtx_typeof (__eo_to_smt v) = SmtType.Int ->
    eo_interprets M (bvPow2IspowPrem v) true ->
    eo_interprets M (bvPow2GtOnePrem v) true ->
    eo_interprets M
      (bvUremPow2NmpPrem v (Term.Numeral W) (Term.Numeral A)) true ->
    eo_interprets M
      (bvUremPow2PmPrem v (Term.Numeral Q)) true ->
    ∃ V P : native_Int,
      __smtx_model_eval M (__eo_to_smt v) = SmtValue.Numeral V ∧
      P = native_int_log2 V ∧ V = native_int_pow2 P ∧ 1 < V ∧
      A = native_zplus W (native_zneg P) ∧
      Q = native_zplus P (native_zneg 1) := by
  intro hVTy hIspPrem hGtPrem hNmpPrem hPmPrem
  rcases CongSupport.smt_eval_int_of_smt_type_int M hM (__eo_to_smt v)
      hVTy with ⟨V, hVEval⟩
  let P := native_int_log2 V
  have hIspEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Apply (Term.UOp UserOp.int_ispow2) v) (Term.Boolean true)
    (by simpa [bvPow2IspowPrem] using hIspPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval_and
        (__smtx_model_eval_geq (__smtx_model_eval M (__eo_to_smt v))
          (SmtValue.Numeral 0))
        (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt v))
          (__smtx_model_eval_int_pow2
            (__smtx_model_eval_int_log2
              (__smtx_model_eval M (__eo_to_smt v))))))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hIspEq
  rw [hVEval] at hIspEq
  have hVPow : V = native_int_pow2 P := by
    have hParts :
        (0 : Int) ≤ V ∧ V = native_int_pow2 (native_int_log2 V) := by
      simpa [__smtx_model_eval_int_log2, __smtx_model_eval_int_pow2,
        __smtx_model_eval_and, __smtx_model_eval_geq,
        __smtx_model_eval_leq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_zeq, SmtEval.native_zleq, native_and,
        Bool.and_eq_true] using hIspEq
    simpa [P] using hParts.2
  have hGtEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) v) (Term.Numeral 1))
    (Term.Boolean true) (by simpa [bvPow2GtOnePrem] using hGtPrem)
  change __smtx_model_eval_eq
      (__smtx_model_eval_gt (__smtx_model_eval M (__eo_to_smt v))
        (SmtValue.Numeral 1))
      (SmtValue.Boolean true) = SmtValue.Boolean true at hGtEq
  rw [hVEval] at hGtEq
  have hVOne : 1 < V := by
    simpa [__smtx_model_eval_gt, __smtx_model_eval_lt,
      __smtx_model_eval_eq, native_veq, SmtEval.native_zeq,
      SmtEval.native_zlt] using hGtEq
  have hNmpEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Numeral A)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral W))
      (Term.Apply (Term.UOp UserOp.int_log2) v))
    (by simpa [bvUremPow2NmpPrem] using hNmpPrem)
  change __smtx_model_eval_eq (SmtValue.Numeral A)
      (__smtx_model_eval__ (SmtValue.Numeral W)
        (__smtx_model_eval_int_log2
          (__smtx_model_eval M (__eo_to_smt v)))) =
    SmtValue.Boolean true at hNmpEq
  rw [hVEval] at hNmpEq
  have hA : A = native_zplus W (native_zneg P) := by
    simpa [P, __smtx_model_eval_int_log2, __smtx_model_eval__,
      __smtx_model_eval_eq, native_veq, SmtEval.native_zeq,
      SmtEval.native_zplus, SmtEval.native_zneg] using hNmpEq
  have hPmEq := model_eval_eq_true_of_eo_eq_true_pow2 M
    (Term.Numeral Q)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp.int_log2) v)) (Term.Numeral 1))
    (by simpa [bvUremPow2PmPrem] using hPmPrem)
  change __smtx_model_eval_eq (SmtValue.Numeral Q)
      (__smtx_model_eval__
        (__smtx_model_eval_int_log2
          (__smtx_model_eval M (__eo_to_smt v)))
        (SmtValue.Numeral 1)) = SmtValue.Boolean true at hPmEq
  rw [hVEval] at hPmEq
  have hQ : Q = native_zplus P (native_zneg 1) := by
    simpa [P, __smtx_model_eval_int_log2, __smtx_model_eval__,
      __smtx_model_eval_eq, native_veq, SmtEval.native_zeq,
      SmtEval.native_zplus, SmtEval.native_zneg] using hPmEq
  exact ⟨V, P, hVEval, rfl, hVPow, hVOne, hA, hQ⟩

private theorem native_int_pow2_pos_of_nonneg_div
    {w : native_Int} (hw : 0 ≤ w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem native_int_pow2_lt_of_lt_nonneg_div
    {w k : native_Int} (hw : 0 ≤ w) (hlt : w < k) :
    native_int_pow2 w < native_int_pow2 k := by
  have hk : 0 ≤ k := Int.le_trans hw (Int.le_of_lt hlt)
  have hnotW : ¬ w < 0 := Int.not_lt_of_ge hw
  have hnotK : ¬ k < 0 := Int.not_lt_of_ge hk
  have hkPos : 0 < k := Int.lt_of_le_of_lt hw hlt
  have hNat : Int.toNat w < Int.toNat k :=
    (Int.toNat_lt_toNat hkPos).2 hlt
  have hPowNat : (2 : Nat) ^ Int.toNat w < 2 ^ Int.toNat k :=
    Nat.pow_lt_pow_right (by decide) hNat
  rw [native_int_pow2, native_int_pow2, native_zexp_total,
    native_zexp_total, if_neg hnotW, if_neg hnotK]
  exact_mod_cast hPowNat

private theorem native_int_pow2_add_of_nonneg_div
    {a b : native_Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    native_int_pow2 (a + b) =
      native_int_pow2 a * native_int_pow2 b := by
  have hna : ¬ a < 0 := Int.not_lt_of_ge ha
  have hnb : ¬ b < 0 := Int.not_lt_of_ge hb
  have hab : ¬ a + b < 0 := Int.not_lt_of_ge (Int.add_nonneg ha hb)
  have hto : Int.toNat (a + b) = Int.toNat a + Int.toNat b :=
    Int.toNat_add ha hb
  rw [native_int_pow2, native_int_pow2, native_int_pow2,
    native_zexp_total, native_zexp_total, native_zexp_total]
  simp [hna, hnb, hab, hto]
  exact Int.pow_add 2 (Int.toNat a) (Int.toNat b)

private theorem bv_udiv_pow2_value_local
    (W P N D p : native_Int)
    (hW0 : 0 ≤ W) (hP0 : 0 ≤ P) (hD0 : 0 ≤ D)
    (hDPos : 0 < D) (hPD : P + D = W) (hN : N = W - 1)
    (hp0 : 0 ≤ p) (hpW : p < native_int_pow2 W) :
    __smtx_model_eval_bvudiv
        (SmtValue.Binary W p)
        (__smtx_model_eval_int_to_bv
          (SmtValue.Numeral W)
          (SmtValue.Numeral (native_int_pow2 P))) =
      __smtx_model_eval_concat
        (__smtx_model_eval_int_to_bv
          (SmtValue.Numeral P) (SmtValue.Numeral 0))
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral P)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) := by
  let q : native_Int := native_div_total p (native_int_pow2 P)
  have hPW : P < W := by
    calc
      P < P + D := Int.lt_add_of_pos_right P hDPos
      _ = W := hPD
  have hPowPPos : 0 < native_int_pow2 P :=
    native_int_pow2_pos_of_nonneg_div hP0
  have hPowWPos : 0 < native_int_pow2 W :=
    native_int_pow2_pos_of_nonneg_div hW0
  have hPow : native_int_pow2 W =
      native_int_pow2 P * native_int_pow2 D := by
    rw [← hPD]
    exact native_int_pow2_add_of_nonneg_div hP0 hD0
  have hPowPLtW : native_int_pow2 P < native_int_pow2 W :=
    native_int_pow2_lt_of_lt_nonneg_div hP0 hPW
  have hPowPModW :
      native_mod_total (native_int_pow2 P) (native_int_pow2 W) =
        native_int_pow2 P := by
    exact Int.emod_eq_of_lt (Int.le_of_lt hPowPPos) hPowPLtW
  have hq0 : 0 ≤ q := by
    dsimp [q, native_div_total]
    exact Int.ediv_nonneg hp0 (Int.le_of_lt hPowPPos)
  have hqD : q < native_int_pow2 D := by
    dsimp [q, native_div_total]
    apply Int.ediv_lt_of_lt_mul hPowPPos
    rw [Int.mul_comm, ← hPow]
    exact hpW
  have hqW : q < native_int_pow2 W := by
    have hDW : D ≤ W := by
      calc
        D ≤ P + D := Int.le_add_of_nonneg_left hP0
        _ = W := hPD
    exact Int.lt_of_lt_of_le hqD
      (native_int_pow2_le_of_le_nonneg hD0 hDW)
  have hqModD : native_mod_total q (native_int_pow2 D) = q := by
    exact Int.emod_eq_of_lt hq0 hqD
  have hqModW : native_mod_total q (native_int_pow2 W) = q := by
    exact Int.emod_eq_of_lt hq0 hqW
  have hZeroModP : native_mod_total 0 (native_int_pow2 P) = 0 := by
    simp [native_mod_total]
  have hPowZero : native_int_pow2 0 = 1 := by native_decide
  have hWidthExtract : N + 1 + -P = D := by
    rw [hN]
    rw [Int.sub_add_cancel]
    rw [← hPD]
    calc
      (P + D) + -P = (P + -P) + D := by ac_rfl
      _ = 0 + D := by rw [Int.add_right_neg]
      _ = D := Int.zero_add D
  have hPowPNe : native_int_pow2 P ≠ 0 := Int.ne_of_gt hPowPPos
  simp only [__smtx_model_eval_int_to_bv, __smtx_model_eval_bvudiv,
    __smtx_model_eval_extract, __smtx_model_eval_concat,
    native_binary_extract, native_binary_concat]
  simp [native_ite, native_zeq, hPowPModW, hPowPNe, q,
    native_zplus, native_zneg, native_zmult, hWidthExtract, hPD,
    hPowZero, hZeroModP, hqModD, hqModW]

private theorem smtx_eval_bvudiv_term_eq_div
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvudiv x y) =
      __smtx_model_eval_bvudiv
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_udiv_pow2_term
    (M : SmtModel) (hM : model_wf M)
    (x v n power nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    __eo_typeof (bvUdivPow2Term x v n power nm) = Term.Bool ->
    eo_interprets M (bvPow2IspowPrem v) true ->
    eo_interprets M (bvPow2GtOnePrem v) true ->
    eo_interprets M (bvPow2PowerPrem v power) true ->
    eo_interprets M (bvUdivPow2NmPrem n nm) true ->
    __smtx_model_eval M (__eo_to_smt (bvUdivPow2Lhs x v n)) =
      __smtx_model_eval M (__eo_to_smt (bvUdivPow2Rhs x power nm)) := by
  intro hXTrans hVTrans hNTrans hPowerTrans hResultTy
    hIspPrem hGtPrem hPowerPrem hNmPrem
  rcases bv_udiv_pow2_context x v n power nm hXTrans hVTrans hNTrans
      hPowerTrans hResultTy with
    ⟨W, P, N, D, rfl, rfl, rfl, hW0, hP0, hNW, hD, hD0, hPD,
      hXSmtTy, hVSmtTy⟩
  rcases bv_udiv_pow2_premises_numeric M hM v W P N hVSmtTy
      hIspPrem hGtPrem hPowerPrem hNmPrem with
    ⟨V, hVEval, hVPow, hVOne, hN⟩
  have hw0 : (0 : Int) ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have hp0 : (0 : Int) ≤ P := by
    simpa [SmtEval.native_zleq] using hP0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hD0
  have hd0 : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have hdPos : (0 : Int) < D := by
    simpa [SmtEval.native_zlt] using hD0
  have hpd : P + D = W := by
    simpa [SmtEval.native_zplus] using hPD
  have hn : N = W - 1 := by
    have hsimpa := hN
    try simp [SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact hsimpa
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x)
      (native_int_to_nat W) hXSmtTy with ⟨p, hXEval, hCanonical⟩
  have hRound := native_int_to_nat_roundtrip W hW0
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary W p := by
    simpa [hRound] using hXEval
  have hCanonical' :
      native_zeq p (native_mod_total p (native_int_pow2 W)) = true := by
    simpa [hRound] using hCanonical
  have hRange := bitvec_payload_range_of_canonical hW0 hCanonical'
  have hConstEval :
      __smtx_model_eval M
          (__eo_to_smt (bvPow2Const v (Term.Numeral W))) =
        __smtx_model_eval_int_to_bv
          (SmtValue.Numeral W)
          (SmtValue.Numeral (native_int_pow2 P)) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt v)) = _
    rw [smtx_eval_int_to_bv_term_eq, hVEval, hVPow]
    simp only [__smtx_model_eval]
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvPow2Const (Term.Numeral 0) (Term.Numeral P))) =
        __smtx_model_eval_int_to_bv
          (SmtValue.Numeral P) (SmtValue.Numeral 0) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral P) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_term_eq]
    simp only [__smtx_model_eval]
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral P))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral P)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval']
  change __smtx_model_eval M
      (SmtTerm.bvudiv (__eo_to_smt x)
        (__eo_to_smt (bvPow2Const v (Term.Numeral W)))) =
    __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt
          (bvPow2Const (Term.Numeral 0) (Term.Numeral P)))
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral P)))
          (SmtTerm.Binary 0 0)))
  rw [smtx_eval_bvudiv_term_eq_div, hXEval', hConstEval,
    _root_.smtx_eval_concat_term_eq, hZeroEval, _root_.smtx_eval_concat_term_eq,
    hExtractEval]
  simp only [__smtx_model_eval]
  exact bv_udiv_pow2_value_local W P N D p hw0 hp0 hd0 hdPos hpd hn
    hRange.1 hRange.2

private theorem facts_bv_udiv_pow2_term
    (M : SmtModel) (hM : model_wf M)
    (x v n power nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    __eo_typeof (bvUdivPow2Term x v n power nm) = Term.Bool ->
    eo_interprets M (bvPow2IspowPrem v) true ->
    eo_interprets M (bvPow2GtOnePrem v) true ->
    eo_interprets M (bvPow2PowerPrem v power) true ->
    eo_interprets M (bvUdivPow2NmPrem n nm) true ->
    eo_interprets M (bvUdivPow2Term x v n power nm) true := by
  intro hXTrans hVTrans hNTrans hPowerTrans hResultTy
    hIspPrem hGtPrem hPowerPrem hNmPrem
  have hBool := typed_bv_udiv_pow2_term x v n power nm hXTrans hVTrans
    hNTrans hPowerTrans hResultTy
  unfold bvUdivPow2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvUdivPow2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvUdivPow2Lhs x v n)))
      (__smtx_model_eval M (__eo_to_smt (bvUdivPow2Rhs x power nm)))
    rw [eval_bv_udiv_pow2_term M hM x v n power nm hXTrans hVTrans
      hNTrans hPowerTrans hResultTy hIspPrem hGtPrem hPowerPrem hNmPrem]
    exact RuleProofs.smt_value_rel_refl _

private theorem bv_urem_pow2_value_local
    (W A D Q p : native_Int)
    (hW0 : 0 ≤ W) (hA0 : 0 ≤ A) (hD0 : 0 ≤ D)
    (hAD : A + D = W) (hQD : Q + 1 = D)
    (hp0 : 0 ≤ p) (hpW : p < native_int_pow2 W) :
    __smtx_model_eval_bvurem
        (SmtValue.Binary W p)
        (__smtx_model_eval_int_to_bv
          (SmtValue.Numeral W)
          (SmtValue.Numeral (native_int_pow2 D))) =
      __smtx_model_eval_concat
        (__smtx_model_eval_int_to_bv
          (SmtValue.Numeral A) (SmtValue.Numeral 0))
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral Q) (SmtValue.Numeral 0)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) := by
  have hPowWPos := native_int_pow2_pos_of_nonneg_div hW0
  have hPowDPos := native_int_pow2_pos_of_nonneg_div hD0
  have hPModW : native_mod_total p (native_int_pow2 W) = p := by
    exact Int.emod_eq_of_lt hp0 hpW
  have hZeroModA : native_mod_total 0 (native_int_pow2 A) = 0 := by
    simp [native_mod_total]
  have hPowZero : native_int_pow2 0 = 1 := by native_decide
  have hDivOne : native_div_total p (native_int_pow2 0) = p := by
    simp [native_div_total, hPowZero]
  have hDivOne' : native_div_total p 1 = p := by
    simp [native_div_total]
  by_cases hA : A = 0
  · have hDW : D = W := by
      calc
        D = 0 + D := (Int.zero_add D).symm
        _ = A + D := by rw [hA]
        _ = W := hAD
    subst A
    subst W
    have hPowModSelf :
        native_mod_total (native_int_pow2 D) (native_int_pow2 D) = 0 := by
      exact Int.emod_self
    simp only [__smtx_model_eval_int_to_bv, __smtx_model_eval_bvurem,
      __smtx_model_eval_extract, __smtx_model_eval_concat,
      native_binary_extract, native_binary_concat]
    simp [native_zplus, native_zneg, native_zmult, hQD, hPowZero,
      hDivOne, hPowModSelf, hPModW, hZeroModA, native_mod_total,
      native_ite, native_zeq, hDivOne']
  · have hAPos : 0 < A :=
      (Int.lt_or_eq_of_le hA0).resolve_right (Ne.symm hA)
    have hDW : D < W := by
      calc
        D < A + D := Int.lt_add_of_pos_left D hAPos
        _ = W := hAD
    have hPowLt := native_int_pow2_lt_of_lt_nonneg_div hD0 hDW
    have hPowMod :
        native_mod_total (native_int_pow2 D) (native_int_pow2 W) =
          native_int_pow2 D := by
      exact Int.emod_eq_of_lt (Int.le_of_lt hPowDPos) hPowLt
    let r := native_mod_total p (native_int_pow2 D)
    have hr0 : 0 ≤ r := by
      exact Int.emod_nonneg p (Int.ne_of_gt hPowDPos)
    have hrD : r < native_int_pow2 D := by
      exact Int.emod_lt_of_pos p hPowDPos
    have hrW : r < native_int_pow2 W := Int.lt_trans hrD hPowLt
    have hrModD : native_mod_total r (native_int_pow2 D) = r := by
      exact Int.emod_eq_of_lt hr0 hrD
    have hrModW : native_mod_total r (native_int_pow2 W) = r := by
      exact Int.emod_eq_of_lt hr0 hrW
    simp only [__smtx_model_eval_int_to_bv, __smtx_model_eval_bvurem,
      __smtx_model_eval_extract, __smtx_model_eval_concat,
      native_binary_extract, native_binary_concat]
    change SmtValue.Binary W
        (native_mod_total
          (native_ite (native_zeq (native_mod_total
            (native_int_pow2 D) (native_int_pow2 W)) 0) p
            (native_mod_total p (native_mod_total
              (native_int_pow2 D) (native_int_pow2 W))))
          (native_int_pow2 W)) = _
    rw [hPowMod]
    have hPowDNe : native_int_pow2 D ≠ 0 := Int.ne_of_gt hPowDPos
    simp [native_zeq, hPowDNe, native_ite, native_zplus, native_zneg,
      native_zmult, hQD, hAD, hPowZero, hDivOne, hDivOne', hZeroModA,
      r, hrModD, hrModW]

private theorem smtx_eval_bvurem_term_eq_div
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvurem x y) =
      __smtx_model_eval_bvurem
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_urem_pow2_term
    (M : SmtModel) (hM : model_wf M)
    (x v n nmp pm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    __eo_typeof (bvUremPow2Term x v n nmp pm) = Term.Bool ->
    eo_interprets M (bvPow2IspowPrem v) true ->
    eo_interprets M (bvPow2GtOnePrem v) true ->
    eo_interprets M (bvUremPow2NmpPrem v n nmp) true ->
    eo_interprets M (bvUremPow2PmPrem v pm) true ->
    __smtx_model_eval M (__eo_to_smt (bvUremPow2Lhs x v n)) =
      __smtx_model_eval M (__eo_to_smt (bvUremPow2Rhs x nmp pm)) := by
  intro hXTrans hVTrans hNTrans hNmpTrans hResultTy
    hIspPrem hGtPrem hNmpPrem hPmPrem
  rcases bv_urem_pow2_context x v n nmp pm hXTrans hVTrans hNTrans
      hNmpTrans hResultTy with
    ⟨W, A, Q, D, rfl, rfl, rfl, hW0, hA0, hQW, hD, hD0, hAD,
      hXSmtTy, hVSmtTy⟩
  rcases bv_urem_pow2_premises_numeric M hM v W A Q hVSmtTy
      hIspPrem hGtPrem hNmpPrem hPmPrem with
    ⟨V, P, hVEval, hPLog, hVPow, hVOne, hA, hQ⟩
  have hDP : D = P := by
    rw [hD, hQ]
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      Int.sub_eq_add_neg] using Int.sub_add_cancel P 1
  have hw0 : (0 : Int) ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have ha0 : (0 : Int) ≤ A := by
    simpa [SmtEval.native_zleq] using hA0
  have hDNonneg : native_zleq 0 D = true :=
    native_zleq_of_zlt_true _ _ hD0
  have hd0 : (0 : Int) ≤ D := by
    simpa [SmtEval.native_zleq] using hDNonneg
  have had : A + D = W := by
    simpa [SmtEval.native_zplus] using hAD
  have hqd : Q + 1 = D := by
    simpa [hD, SmtEval.native_zplus]
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x)
      (native_int_to_nat W) hXSmtTy with ⟨p, hXEval, hCanonical⟩
  have hRound := native_int_to_nat_roundtrip W hW0
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary W p := by
    simpa [hRound] using hXEval
  have hCanonical' :
      native_zeq p (native_mod_total p (native_int_pow2 W)) = true := by
    simpa [hRound] using hCanonical
  have hRange := bitvec_payload_range_of_canonical hW0 hCanonical'
  have hConstEval :
      __smtx_model_eval M
          (__eo_to_smt (bvPow2Const v (Term.Numeral W))) =
        __smtx_model_eval_int_to_bv
          (SmtValue.Numeral W)
          (SmtValue.Numeral (native_int_pow2 D)) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt v)) = _
    rw [smtx_eval_int_to_bv_term_eq, hVEval, hVPow, ← hDP]
    simp only [__smtx_model_eval]
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvPow2Const (Term.Numeral 0) (Term.Numeral A))) =
        __smtx_model_eval_int_to_bv
          (SmtValue.Numeral A) (SmtValue.Numeral 0) := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral A) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_term_eq]
    simp only [__smtx_model_eval]
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral Q) (SmtValue.Numeral 0)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval']
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by rfl
  change __smtx_model_eval M
      (SmtTerm.bvurem (__eo_to_smt x)
        (__eo_to_smt (bvPow2Const v (Term.Numeral W)))) =
    __smtx_model_eval M
      (SmtTerm.concat
        (__eo_to_smt
          (bvPow2Const (Term.Numeral 0) (Term.Numeral A)))
        (SmtTerm.concat
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral Q) (Term.Numeral 0)))
          (SmtTerm.Binary 0 0)))
  rw [smtx_eval_bvurem_term_eq_div, hXEval', hConstEval,
    _root_.smtx_eval_concat_term_eq, hZeroEval, _root_.smtx_eval_concat_term_eq,
    hExtractEval]
  simp only [__smtx_model_eval]
  exact bv_urem_pow2_value_local W A D Q p hw0 ha0 hd0 had hqd
    hRange.1 hRange.2

private theorem facts_bv_urem_pow2_term
    (M : SmtModel) (hM : model_wf M)
    (x v n nmp pm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    __eo_typeof (bvUremPow2Term x v n nmp pm) = Term.Bool ->
    eo_interprets M (bvPow2IspowPrem v) true ->
    eo_interprets M (bvPow2GtOnePrem v) true ->
    eo_interprets M (bvUremPow2NmpPrem v n nmp) true ->
    eo_interprets M (bvUremPow2PmPrem v pm) true ->
    eo_interprets M (bvUremPow2Term x v n nmp pm) true := by
  intro hXTrans hVTrans hNTrans hNmpTrans hResultTy
    hIspPrem hGtPrem hNmpPrem hPmPrem
  have hBool := typed_bv_urem_pow2_term x v n nmp pm hXTrans hVTrans
    hNTrans hNmpTrans hResultTy
  unfold bvUremPow2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvUremPow2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvUremPow2Lhs x v n)))
      (__smtx_model_eval M (__eo_to_smt (bvUremPow2Rhs x nmp pm)))
    rw [eval_bv_urem_pow2_term M hM x v n nmp pm hXTrans hVTrans
      hNTrans hNmpTrans hResultTy hIspPrem hGtPrem hNmpPrem hPmPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvUremPow2Program
    (x v n nmp pm P1 P2 P3 P4 : Term) : Term :=
  __eo_prog_bv_urem_pow2_not_one x v n nmp pm
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)

private theorem pow2_and_true {a b : Term} :
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

private def bvUremPow2Guard
    (x v n nmp pm vRef1 vRef2 nmpRef nRef vRef3 pmRef vRef4 : Term) :
    Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq v vRef1) (__eo_eq v vRef2))
            (__eo_eq nmp nmpRef))
          (__eo_eq n nRef))
        (__eo_eq v vRef3))
      (__eo_eq pm pmRef))
    (__eo_eq v vRef4)

private theorem bv_urem_pow2_guard_refs
    {x v n nmp pm vRef1 vRef2 nmpRef nRef vRef3 pmRef vRef4 body :
      Term} :
    __eo_requires
        (bvUremPow2Guard x v n nmp pm vRef1 vRef2 nmpRef nRef vRef3
          pmRef vRef4)
        (Term.Boolean true) body ≠ Term.Stuck ->
    vRef1 = v ∧ vRef2 = v ∧ nmpRef = nmp ∧ nRef = n ∧
      vRef3 = v ∧ pmRef = pm ∧ vRef4 = v := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvUremPow2Guard at hGuard
  rcases pow2_and_true hGuard with ⟨hG6, hV4⟩
  rcases pow2_and_true hG6 with ⟨hG5, hPm⟩
  rcases pow2_and_true hG5 with ⟨hG4, hV3⟩
  rcases pow2_and_true hG4 with ⟨hG3, hN⟩
  rcases pow2_and_true hG3 with ⟨hG2, hNmp⟩
  rcases pow2_and_true hG2 with ⟨hV1, hV2⟩
  exact ⟨support_eq_of_eo_eq_true v vRef1 hV1,
    support_eq_of_eo_eq_true v vRef2 hV2,
    support_eq_of_eo_eq_true nmp nmpRef hNmp,
    support_eq_of_eo_eq_true n nRef hN,
    support_eq_of_eo_eq_true v vRef3 hV3,
    support_eq_of_eo_eq_true pm pmRef hPm,
    support_eq_of_eo_eq_true v vRef4 hV4⟩

private theorem bv_urem_pow2_premise_shape
    (x v n nmp pm P1 P2 P3 P4 : Term) :
    x ≠ Term.Stuck -> v ≠ Term.Stuck -> n ≠ Term.Stuck ->
    nmp ≠ Term.Stuck -> pm ≠ Term.Stuck ->
    bvUremPow2Program x v n nmp pm P1 P2 P3 P4 ≠ Term.Stuck ->
    ∃ vRef1 vRef2 nmpRef nRef vRef3 pmRef vRef4,
      P1 = bvPow2IspowPrem vRef1 ∧
      P2 = bvPow2GtOnePrem vRef2 ∧
      P3 = bvUremPow2NmpPrem vRef3 nRef nmpRef ∧
      P4 = bvUremPow2PmPrem vRef4 pmRef := by
  intro hX hV hN hNmp hPm hProg
  by_cases hShape :
      ∃ vRef1 vRef2 nmpRef nRef vRef3 pmRef vRef4,
        P1 = bvPow2IspowPrem vRef1 ∧
        P2 = bvPow2GtOnePrem vRef2 ∧
        P3 = bvUremPow2NmpPrem vRef3 nRef nmpRef ∧
        P4 = bvUremPow2PmPrem vRef4 pmRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_urem_pow2_not_one.eq_7 x v n nmp pm
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
      hX hV hN hNmp hPm (by
        intro vRef1 vRef2 nmpRef nRef vRef3 pmRef vRef4
          hP1 hP2 hP3 hP4
        cases hP1
        cases hP2
        cases hP3
        cases hP4
        exact hShape
          ⟨vRef1, vRef2, nmpRef, nRef, vRef3, pmRef, vRef4,
            rfl, rfl, rfl, rfl⟩)

private theorem bv_urem_pow2_program_canonical
    (x v n nmp pm : Term) :
    x ≠ Term.Stuck -> v ≠ Term.Stuck -> n ≠ Term.Stuck ->
    nmp ≠ Term.Stuck -> pm ≠ Term.Stuck ->
    bvUremPow2Program x v n nmp pm
        (bvPow2IspowPrem v) (bvPow2GtOnePrem v)
        (bvUremPow2NmpPrem v n nmp) (bvUremPow2PmPrem v pm) =
      bvUremPow2Term x v n nmp pm := by
  intro hX hV hN hNmp hPm
  unfold bvUremPow2Program bvPow2IspowPrem bvPow2GtOnePrem
    bvUremPow2NmpPrem bvUremPow2PmPrem
  rw [__eo_prog_bv_urem_pow2_not_one.eq_6 x v n nmp pm
    v v nmp n v pm v hX hV hN hNmp hPm]
  simp [bvUremPow2Term, bvUremPow2Lhs, bvUremPow2Rhs, bvPow2Const,
    bvExtractTerm, __eo_requires, __eo_and, __eo_eq, native_ite,
    native_teq, native_not, native_and, hX, hV, hN, hNmp, hPm]

private theorem bvUremPow2Program_normalize
    (x v n nmp pm P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    RuleProofs.eo_has_smt_translation pm ->
    bvUremPow2Program x v n nmp pm P1 P2 P3 P4 ≠ Term.Stuck ->
    P1 = bvPow2IspowPrem v ∧
      P2 = bvPow2GtOnePrem v ∧
      P3 = bvUremPow2NmpPrem v n nmp ∧
      P4 = bvUremPow2PmPrem v pm ∧
      bvUremPow2Program x v n nmp pm P1 P2 P3 P4 =
        bvUremPow2Term x v n nmp pm := by
  intro hXTrans hVTrans hNTrans hNmpTrans hPmTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hV := RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
  have hN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hNmp := RuleProofs.term_ne_stuck_of_has_smt_translation nmp hNmpTrans
  have hPm := RuleProofs.term_ne_stuck_of_has_smt_translation pm hPmTrans
  rcases bv_urem_pow2_premise_shape x v n nmp pm P1 P2 P3 P4
      hX hV hN hNmp hPm hProg with
    ⟨vRef1, vRef2, nmpRef, nRef, vRef3, pmRef, vRef4,
      hP1, hP2, hP3, hP4⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4] at hReq
  unfold bvUremPow2Program bvPow2IspowPrem bvPow2GtOnePrem
    bvUremPow2NmpPrem bvUremPow2PmPrem at hReq
  rw [__eo_prog_bv_urem_pow2_not_one.eq_6 x v n nmp pm
    vRef1 vRef2 nmpRef nRef vRef3 pmRef vRef4
    hX hV hN hNmp hPm] at hReq
  rcases bv_urem_pow2_guard_refs
      (x := x) (v := v) (n := n) (nmp := nmp) (pm := pm)
      (vRef1 := vRef1) (vRef2 := vRef2) (nmpRef := nmpRef)
      (nRef := nRef) (vRef3 := vRef3) (pmRef := pmRef)
      (vRef4 := vRef4)
      (by simpa [bvUremPow2Guard] using hReq) with
    ⟨hv1, hv2, hnmp, hn, hv3, hpm, hv4⟩
  subst vRef1
  subst vRef2
  subst nmpRef
  subst nRef
  subst vRef3
  subst pmRef
  subst vRef4
  refine ⟨hP1, hP2, hP3, hP4, ?_⟩
  rw [hP1, hP2, hP3, hP4]
  exact bv_urem_pow2_program_canonical x v n nmp pm hX hV hN hNmp hPm

theorem typed_bv_urem_pow2_program
    (x v n nmp pm P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    RuleProofs.eo_has_smt_translation pm ->
    __eo_typeof (bvUremPow2Program x v n nmp pm P1 P2 P3 P4) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvUremPow2Program x v n nmp pm P1 P2 P3 P4) := by
  intro hXTrans hVTrans hNTrans hNmpTrans hPmTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvUremPow2Program_normalize x v n nmp pm P1 P2 P3 P4
      hXTrans hVTrans hNTrans hNmpTrans hPmTrans hProg with
    ⟨_hP1, _hP2, _hP3, _hP4, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvUremPow2Term x v n nmp pm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_urem_pow2_term x v n nmp pm hXTrans hVTrans
    hNTrans hNmpTrans hTermTy

theorem facts_bv_urem_pow2_program
    (M : SmtModel) (hM : model_wf M)
    (x v n nmp pm P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation nmp ->
    RuleProofs.eo_has_smt_translation pm ->
    __eo_typeof (bvUremPow2Program x v n nmp pm P1 P2 P3 P4) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true -> eo_interprets M P4 true ->
    eo_interprets M (bvUremPow2Program x v n nmp pm P1 P2 P3 P4) true := by
  intro hXTrans hVTrans hNTrans hNmpTrans hPmTrans hResultTy
    hP1True hP2True hP3True hP4True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvUremPow2Program_normalize x v n nmp pm P1 P2 P3 P4
      hXTrans hVTrans hNTrans hNmpTrans hPmTrans hProg with
    ⟨hP1, hP2, hP3, hP4, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvUremPow2Term x v n nmp pm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hIspPrem : eo_interprets M (bvPow2IspowPrem v) true := by
    simpa [hP1] using hP1True
  have hGtPrem : eo_interprets M (bvPow2GtOnePrem v) true := by
    simpa [hP2] using hP2True
  have hNmpPrem : eo_interprets M (bvUremPow2NmpPrem v n nmp) true := by
    simpa [hP3] using hP3True
  have hPmPrem : eo_interprets M (bvUremPow2PmPrem v pm) true := by
    simpa [hP4] using hP4True
  rw [hProgramEq]
  exact facts_bv_urem_pow2_term M hM x v n nmp pm hXTrans hVTrans
    hNTrans hNmpTrans hTermTy hIspPrem hGtPrem hNmpPrem hPmPrem

def bvUdivPow2Program
    (x v n power nm P1 P2 P3 P4 : Term) : Term :=
  __eo_prog_bv_udiv_pow2_not_one x v n power nm
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)

private def bvUdivPow2Guard
    (x v n power nm vRef1 vRef2 powerRef vRef3 nmRef nRef : Term) :
    Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and (__eo_eq v vRef1) (__eo_eq v vRef2))
          (__eo_eq power powerRef))
        (__eo_eq v vRef3))
      (__eo_eq nm nmRef))
    (__eo_eq n nRef)

private theorem bv_udiv_pow2_guard_refs
    {x v n power nm vRef1 vRef2 powerRef vRef3 nmRef nRef body : Term} :
    __eo_requires
        (bvUdivPow2Guard x v n power nm vRef1 vRef2 powerRef vRef3
          nmRef nRef)
        (Term.Boolean true) body ≠ Term.Stuck ->
    vRef1 = v ∧ vRef2 = v ∧ powerRef = power ∧ vRef3 = v ∧
      nmRef = nm ∧ nRef = n := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvUdivPow2Guard at hGuard
  rcases pow2_and_true hGuard with ⟨hG5, hN⟩
  rcases pow2_and_true hG5 with ⟨hG4, hNm⟩
  rcases pow2_and_true hG4 with ⟨hG3, hV3⟩
  rcases pow2_and_true hG3 with ⟨hG2, hPower⟩
  rcases pow2_and_true hG2 with ⟨hV1, hV2⟩
  exact ⟨support_eq_of_eo_eq_true v vRef1 hV1,
    support_eq_of_eo_eq_true v vRef2 hV2,
    support_eq_of_eo_eq_true power powerRef hPower,
    support_eq_of_eo_eq_true v vRef3 hV3,
    support_eq_of_eo_eq_true nm nmRef hNm,
    support_eq_of_eo_eq_true n nRef hN⟩

private theorem bv_udiv_pow2_premise_shape
    (x v n power nm P1 P2 P3 P4 : Term) :
    x ≠ Term.Stuck -> v ≠ Term.Stuck -> n ≠ Term.Stuck ->
    power ≠ Term.Stuck -> nm ≠ Term.Stuck ->
    bvUdivPow2Program x v n power nm P1 P2 P3 P4 ≠ Term.Stuck ->
    ∃ vRef1 vRef2 powerRef vRef3 nmRef nRef,
      P1 = bvPow2IspowPrem vRef1 ∧
      P2 = bvPow2GtOnePrem vRef2 ∧
      P3 = bvPow2PowerPrem vRef3 powerRef ∧
      P4 = bvUdivPow2NmPrem nRef nmRef := by
  intro hX hV hN hPower hNm hProg
  by_cases hShape :
      ∃ vRef1 vRef2 powerRef vRef3 nmRef nRef,
        P1 = bvPow2IspowPrem vRef1 ∧
        P2 = bvPow2GtOnePrem vRef2 ∧
        P3 = bvPow2PowerPrem vRef3 powerRef ∧
        P4 = bvUdivPow2NmPrem nRef nmRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_udiv_pow2_not_one.eq_7 x v n power nm
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)
      hX hV hN hPower hNm (by
        intro vRef1 vRef2 powerRef vRef3 nmRef nRef hP1 hP2 hP3 hP4
        cases hP1
        cases hP2
        cases hP3
        cases hP4
        exact hShape
          ⟨vRef1, vRef2, powerRef, vRef3, nmRef, nRef,
            rfl, rfl, rfl, rfl⟩)

private theorem bv_udiv_pow2_program_canonical
    (x v n power nm : Term) :
    x ≠ Term.Stuck -> v ≠ Term.Stuck -> n ≠ Term.Stuck ->
    power ≠ Term.Stuck -> nm ≠ Term.Stuck ->
    bvUdivPow2Program x v n power nm
        (bvPow2IspowPrem v) (bvPow2GtOnePrem v)
        (bvPow2PowerPrem v power) (bvUdivPow2NmPrem n nm) =
      bvUdivPow2Term x v n power nm := by
  intro hX hV hN hPower hNm
  unfold bvUdivPow2Program bvPow2IspowPrem bvPow2GtOnePrem
    bvPow2PowerPrem bvUdivPow2NmPrem
  rw [__eo_prog_bv_udiv_pow2_not_one.eq_6 x v n power nm
    v v power v nm n hX hV hN hPower hNm]
  simp [bvUdivPow2Term, bvUdivPow2Lhs, bvUdivPow2Rhs, bvPow2Const,
    bvExtractTerm, __eo_requires, __eo_and, __eo_eq, native_ite,
    native_teq, native_not, native_and, hX, hV, hN, hPower, hNm]

private theorem bvUdivPow2Program_normalize
    (x v n power nm P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    RuleProofs.eo_has_smt_translation nm ->
    bvUdivPow2Program x v n power nm P1 P2 P3 P4 ≠ Term.Stuck ->
    P1 = bvPow2IspowPrem v ∧
      P2 = bvPow2GtOnePrem v ∧
      P3 = bvPow2PowerPrem v power ∧
      P4 = bvUdivPow2NmPrem n nm ∧
      bvUdivPow2Program x v n power nm P1 P2 P3 P4 =
        bvUdivPow2Term x v n power nm := by
  intro hXTrans hVTrans hNTrans hPowerTrans hNmTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hV := RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
  have hN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hPower :=
    RuleProofs.term_ne_stuck_of_has_smt_translation power hPowerTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_udiv_pow2_premise_shape x v n power nm P1 P2 P3 P4
      hX hV hN hPower hNm hProg with
    ⟨vRef1, vRef2, powerRef, vRef3, nmRef, nRef,
      hP1, hP2, hP3, hP4⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4] at hReq
  unfold bvUdivPow2Program bvPow2IspowPrem bvPow2GtOnePrem
    bvPow2PowerPrem bvUdivPow2NmPrem at hReq
  rw [__eo_prog_bv_udiv_pow2_not_one.eq_6 x v n power nm
    vRef1 vRef2 powerRef vRef3 nmRef nRef
    hX hV hN hPower hNm] at hReq
  rcases bv_udiv_pow2_guard_refs
      (x := x) (v := v) (n := n) (power := power) (nm := nm)
      (vRef1 := vRef1) (vRef2 := vRef2) (powerRef := powerRef)
      (vRef3 := vRef3) (nmRef := nmRef) (nRef := nRef)
      (by simpa [bvUdivPow2Guard] using hReq) with
    ⟨hv1, hv2, hpower, hv3, hnm, hn⟩
  subst vRef1
  subst vRef2
  subst powerRef
  subst vRef3
  subst nmRef
  subst nRef
  refine ⟨hP1, hP2, hP3, hP4, ?_⟩
  rw [hP1, hP2, hP3, hP4]
  exact bv_udiv_pow2_program_canonical x v n power nm
    hX hV hN hPower hNm

theorem typed_bv_udiv_pow2_program
    (x v n power nm P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvUdivPow2Program x v n power nm P1 P2 P3 P4) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvUdivPow2Program x v n power nm P1 P2 P3 P4) := by
  intro hXTrans hVTrans hNTrans hPowerTrans hNmTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvUdivPow2Program_normalize x v n power nm P1 P2 P3 P4
      hXTrans hVTrans hNTrans hPowerTrans hNmTrans hProg with
    ⟨_hP1, _hP2, _hP3, _hP4, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvUdivPow2Term x v n power nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_udiv_pow2_term x v n power nm hXTrans hVTrans
    hNTrans hPowerTrans hTermTy

theorem facts_bv_udiv_pow2_program
    (M : SmtModel) (hM : model_wf M)
    (x v n power nm P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation v ->
    RuleProofs.eo_has_smt_translation n ->
    RuleProofs.eo_has_smt_translation power ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvUdivPow2Program x v n power nm P1 P2 P3 P4) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true -> eo_interprets M P4 true ->
    eo_interprets M (bvUdivPow2Program x v n power nm P1 P2 P3 P4) true := by
  intro hXTrans hVTrans hNTrans hPowerTrans hNmTrans hResultTy
    hP1True hP2True hP3True hP4True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvUdivPow2Program_normalize x v n power nm P1 P2 P3 P4
      hXTrans hVTrans hNTrans hPowerTrans hNmTrans hProg with
    ⟨hP1, hP2, hP3, hP4, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvUdivPow2Term x v n power nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hIspPrem : eo_interprets M (bvPow2IspowPrem v) true := by
    simpa [hP1] using hP1True
  have hGtPrem : eo_interprets M (bvPow2GtOnePrem v) true := by
    simpa [hP2] using hP2True
  have hPowerPrem : eo_interprets M (bvPow2PowerPrem v power) true := by
    simpa [hP3] using hP3True
  have hNmPrem : eo_interprets M (bvUdivPow2NmPrem n nm) true := by
    simpa [hP4] using hP4True
  rw [hProgramEq]
  exact facts_bv_udiv_pow2_term M hM x v n power nm hXTrans hVTrans
    hNTrans hPowerTrans hTermTy hIspPrem hGtPrem hPowerPrem hNmPrem
