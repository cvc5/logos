module

public import Cpc.Proofs.RuleSupport.BvShiftByConst2Support
import all Cpc.Proofs.RuleSupport.BvShiftByConst2Support

public section

/-! Shared support for the in-range constant `bvshl` and `bvlshr` rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvShiftByConst1LtPrem (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) amount)
        (bvShiftByConst2Bvsize x)))
    (Term.Boolean true)

def bvShlByConst1EnPrem (x amount en : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) en)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg) (bvShiftByConst2Bvsize x))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) amount)
          (Term.Numeral 0))))

def bvLshrByConst1NmPrem (x nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvShiftByConst2Bvsize x)) (Term.Numeral 1))

def bvShiftByConst1Zero (amount : Term) : Term :=
  bvShiftByConst2Const (Term.Numeral 0) amount

def bvShlByConst1Rhs (x amount en : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x en (Term.Numeral 0)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvShiftByConst1Zero amount))
      (Term.Binary 0 0))

def bvLshrByConst1Rhs (x amount nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat) (bvShiftByConst1Zero amount))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvExtractTerm x nm amount))
      (Term.Binary 0 0))

def bvShlByConst1Term (x amount sz en : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvShlByConst2Lhs x amount sz)) (bvShlByConst1Rhs x amount en)

def bvLshrByConst1Term (x amount sz nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvLshrByConst2Lhs x amount sz)) (bvLshrByConst1Rhs x amount nm)

private theorem typeof_bvand_arg_types_of_ne_stuck_local1
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    exists width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width /\
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A <;> cases B <;> simp [__eo_typeof_bvand] at h |-
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvand] at h |-
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvand] at h |-
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvand] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem shift_operand_context1
    (x amount sz : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)) ≠ Term.Stuck ->
    exists W : native_Int,
      sz = Term.Numeral W /\ native_zleq 0 W = true /\
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) /\
      __eo_typeof amount = Term.UOp UserOp.Int /\
      __eo_typeof (bvShiftByConst2Const amount sz) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) /\
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) /\
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int := by
  intro hXTrans hAmountTrans hSzTrans hLeftNe
  rcases typeof_bvand_arg_types_of_ne_stuck_local1 hLeftNe with
    ⟨width, hXTy, hConstTy⟩
  have hAmountNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSzNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  rcases bv_all_ones_const_context amount sz width hAmountNe hSzNe
      (by simpa [bvAllOnesConst, bvShiftByConst2Const] using hConstTy) with
    ⟨W, hSz, hWidth, hW0, hAmountTy⟩
  subst width
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) := by
    have h :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt x) rfl hXTrans hXTy
    simpa [__eo_to_smt_type, hW0, native_ite] using h
  have hAmountSmtTy :
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      amount (Term.UOp UserOp.Int) (__eo_to_smt amount) rfl
      hAmountTrans hAmountTy
  exact ⟨W, hSz, hW0, hXTy, hAmountTy, hConstTy,
    hXSmtTy, hAmountSmtTy⟩

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck_local
    {A B : Term} (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    exists wa wb,
      A = Term.Apply (Term.UOp UserOp.BitVec) wa /\
      B = Term.Apply (Term.UOp UserOp.BitVec) wb := by
  cases A <;> cases B <;> simp [__eo_typeof_concat] at h |-
  case Apply.Apply f a g b =>
    cases f <;> cases g <;> simp [__eo_typeof_concat] at h |-
    case UOp.UOp op op' =>
      cases op <;> cases op' <;> simp [__eo_typeof_concat] at h |-

private theorem smt_typeof_concat_bitvec
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

private theorem smt_typeof_empty_bitvec :
    __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 := by
  native_decide

private theorem shift_lhs_eo_type
    (x amount : Term) (W : native_Int) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    __eo_typeof (bvShiftByConst2Const amount (Term.Numeral W)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount (Term.Numeral W))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
  intro hXTy hConstTy
  rw [hXTy, hConstTy]
  simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

private theorem smt_typeof_bvshl_same1
    (x amount : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt amount) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt (bvShlByConst2Lhs x amount
      (Term.Numeral W))) = SmtType.BitVec (native_int_to_nat W) := by
  intro hXTy hAmountTy hW0
  have hConstTy := smt_typeof_bv_const_of_int_type amount W hAmountTy hW0
  have hConstTy' :
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount)) =
        SmtType.BitVec (native_int_to_nat W) := by
    have hsimpa := hConstTy
    try simp [bvShiftByConst2Const] at hsimpa ⊢
    exact hsimpa
  change __smtx_typeof
      (SmtTerm.bvshl (__eo_to_smt x)
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem smt_typeof_bvlshr_same1
    (x amount : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt amount) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt (bvLshrByConst2Lhs x amount
      (Term.Numeral W))) = SmtType.BitVec (native_int_to_nat W) := by
  intro hXTy hAmountTy hW0
  have hConstTy := smt_typeof_bv_const_of_int_type amount W hAmountTy hW0
  have hConstTy' :
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount)) =
        SmtType.BitVec (native_int_to_nat W) := by
    have hsimpa := hConstTy
    try simp [bvShiftByConst2Const] at hsimpa ⊢
    exact hsimpa
  change __smtx_typeof
      (SmtTerm.bvlshr (__eo_to_smt x)
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem rhs_smt_type_of_eo_bitvec_type
    (rhs : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation rhs ->
    __eo_typeof rhs =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt rhs) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hTrans hEoTy hW0
  have h := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    rhs (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
    (__eo_to_smt rhs) rfl hTrans hEoTy
  simpa [__eo_to_smt_type, hW0, native_ite] using h

private theorem bv_lshr_by_const_1_context
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    exists W A N : native_Int,
      sz = Term.Numeral W /\ amount = Term.Numeral A /\
      nm = Term.Numeral N /\
      native_zleq 0 W = true /\ native_zleq 0 A = true /\
      native_zlt N W = true /\
      native_zleq 0
        (native_zplus (native_zplus N 1) (native_zneg A)) = true /\
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) /\
      __smtx_typeof (__eo_to_smt (bvLshrByConst1Rhs x amount nm)) =
        SmtType.BitVec (native_int_to_nat W) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvLshrByConst1Rhs x amount nm)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases shift_operand_context1 x amount sz hXTrans hAmountTrans
      hSzTrans hLhsNe with
    ⟨W, rfl, hW0, hXTy, _hAmountTy, hConstTy, hXSmtTy, hAmountSmtTy⟩
  change __eo_typeof_concat (__eo_typeof (bvShiftByConst1Zero amount))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x nm amount)) (Term.Binary 0 0))) ≠
      Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsNe with
    ⟨wz, wi, hZeroTy, hInnerTy⟩
  have hAmountNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) amount wz
      (by simp) hAmountNe
      (by simpa [bvAllOnesConst, bvShiftByConst1Zero,
          bvShiftByConst2Const] using hZeroTy) with
    ⟨A, hAmount, hWz, hA0, _hZeroValueTy⟩
  subst wz
  subst amount
  have hInnerNe :
      __eo_typeof_concat
          (__eo_typeof (bvExtractTerm x nm (Term.Numeral A)))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hsimpa := (show
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x nm (Term.Numeral A))) (Term.Binary 0 0)) ≠
        Term.Stuck by
      rw [hInnerTy]
      intro h
      cases h)
    try simp at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerNe with
    ⟨we, w0, hExtractTy, _hEmptyTy⟩
  have hExtractNe :
      __eo_typeof (bvExtractTerm x nm (Term.Numeral A)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x nm (Term.Numeral A)
      hXTrans hExtractNe with
    ⟨W', N, A', hXTy', hNm, hAmount', _hW'0, _hA'0, hNW', hD0,
      _hXSmtTy'⟩
  have hWW' : W' = W := by
    rw [hXTy] at hXTy'
    injection hXTy' with _ hNum
    injection hNum with hEq
    exact hEq.symm
  subst W'
  have hAA' : A' = A := by
    injection hAmount' with hEq
    exact hEq.symm
  subst A'
  subst nm
  have hExtSmtTy := smt_typeof_extract_of_context x W N A hXSmtTy
    hW0 hA0 hNW' hD0
  have hZeroSmtTy :=
    smt_typeof_bv_const_of_int_type (Term.Numeral 0) A rfl hA0
  have hInnerSmtTy := smt_typeof_concat_bitvec
    (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))
    (Term.Binary 0 0)
    _ _
    hExtSmtTy smt_typeof_empty_bitvec
  have hRhsRawTy := smt_typeof_concat_bitvec
    (bvShiftByConst1Zero (Term.Numeral A))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x (Term.Numeral N) (Term.Numeral A)))
      (Term.Binary 0 0))
    _ _
    hZeroSmtTy hInnerSmtTy
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)) := by
    unfold RuleProofs.eo_has_smt_translation bvLshrByConst1Rhs
    rw [hRhsRawTy]
    intro h
    cases h
  have hLhsTy := shift_lhs_eo_type x (Term.Numeral A) W hXTy hConstTy
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRhsEoTy :
      __eo_typeof (bvLshrByConst1Rhs x (Term.Numeral A)
          (Term.Numeral N)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypes
    exact hTypes.symm
  have hRhsSmtTy := rhs_smt_type_of_eo_bitvec_type
    (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)) W
    hRhsTrans hRhsEoTy hW0
  have hD0' := native_zleq_of_zlt_true 0 _ hD0
  exact ⟨W, A, N, rfl, rfl, rfl, hW0, hA0, hNW', hD0',
    hXSmtTy, hRhsSmtTy⟩

private theorem bv_shl_by_const_1_context
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    exists W A E : native_Int,
      sz = Term.Numeral W /\ amount = Term.Numeral A /\
      en = Term.Numeral E /\
      native_zleq 0 W = true /\ native_zleq 0 A = true /\
      native_zlt E W = true /\
      native_zleq 0 (native_zplus E 1) = true /\
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) /\
      __smtx_typeof (__eo_to_smt (bvShlByConst1Rhs x amount en)) =
        SmtType.BitVec (native_int_to_nat W) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvShlByConst1Rhs x amount en)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases shift_operand_context1 x amount sz hXTrans hAmountTrans
      hSzTrans hLhsNe with
    ⟨W, rfl, hW0, hXTy, _hAmountTy, hConstTy, hXSmtTy, hAmountSmtTy⟩
  change __eo_typeof_concat (__eo_typeof (bvExtractTerm x en (Term.Numeral 0)))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvShiftByConst1Zero amount)) (Term.Binary 0 0))) ≠
      Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsNe with
    ⟨we, wi, hExtractTy, hInnerTy⟩
  have hInnerNe :
      __eo_typeof_concat (__eo_typeof (bvShiftByConst1Zero amount))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hsimpa := (show
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvShiftByConst1Zero amount)) (Term.Binary 0 0)) ≠
        Term.Stuck by
      rw [hInnerTy]
      intro h
      cases h)
    try simp at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerNe with
    ⟨wz, w0, hZeroTy, _hEmptyTy⟩
  have hAmountNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) amount wz
      (by simp) hAmountNe
      (by simpa [bvAllOnesConst, bvShiftByConst1Zero,
          bvShiftByConst2Const] using hZeroTy) with
    ⟨A, hAmount, hWz, hA0, _hZeroValueTy⟩
  subst wz
  subst amount
  have hExtractNe :
      __eo_typeof (bvExtractTerm x en (Term.Numeral 0)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x en (Term.Numeral 0)
      hXTrans hExtractNe with
    ⟨W', E, Z, hXTy', hEn, hZero, _hW'0, hZ0, hEW', hD0,
      _hXSmtTy'⟩
  have hWW' : W' = W := by
    rw [hXTy] at hXTy'
    injection hXTy' with _ hNum
    injection hNum with hEq
    exact hEq.symm
  subst W'
  have hZ : Z = 0 := by
    injection hZero with hEq
    exact hEq.symm
  subst Z
  subst en
  have hD0' : native_zleq 0 (native_zplus E 1) = true := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using
      (native_zleq_of_zlt_true 0 _ hD0)
  have hExtSmtTy := smt_typeof_extract_of_context x W E 0 hXSmtTy
    hW0 hZ0 hEW' hD0
  have hZeroSmtTy :=
    smt_typeof_bv_const_of_int_type (Term.Numeral 0) A rfl hA0
  have hInnerSmtTy := smt_typeof_concat_bitvec
    (bvShiftByConst1Zero (Term.Numeral A)) (Term.Binary 0 0)
    _ _ hZeroSmtTy smt_typeof_empty_bitvec
  have hRhsRawTy := smt_typeof_concat_bitvec
    (bvExtractTerm x (Term.Numeral E) (Term.Numeral 0))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvShiftByConst1Zero (Term.Numeral A))) (Term.Binary 0 0))
    _ _ hExtSmtTy hInnerSmtTy
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E)) := by
    unfold RuleProofs.eo_has_smt_translation bvShlByConst1Rhs
    rw [hRhsRawTy]
    intro h
    cases h
  have hLhsTy := shift_lhs_eo_type x (Term.Numeral A) W hXTy hConstTy
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRhsEoTy :
      __eo_typeof (bvShlByConst1Rhs x (Term.Numeral A)
          (Term.Numeral E)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypes
    exact hTypes.symm
  have hRhsSmtTy := rhs_smt_type_of_eo_bitvec_type
    (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E)) W
    hRhsTrans hRhsEoTy hW0
  exact ⟨W, A, E, rfl, rfl, rfl, hW0, hA0, hEW', hD0',
    hXSmtTy, hRhsSmtTy⟩

private theorem typed_bv_lshr_by_const_1_term
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvLshrByConst1Term x amount sz nm) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  rcases bv_lshr_by_const_1_context x amount sz nm hXTrans hAmountTrans
      hSzTrans hNmTrans hResultTy with
    ⟨W, A, N, rfl, rfl, rfl, hW0, _hA0, _hNW, _hD0,
      hXSmtTy, hRhsSmtTy⟩
  have hLhsSmtTy := smt_typeof_bvlshr_same1 x (Term.Numeral A) W
    hXSmtTy rfl hW0
  unfold bvLshrByConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsSmtTy.trans hRhsSmtTy.symm)
    (by rw [hLhsSmtTy]; intro h; cases h)

private theorem typed_bv_shl_by_const_1_term
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvShlByConst1Term x amount sz en) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  rcases bv_shl_by_const_1_context x amount sz en hXTrans hAmountTrans
      hSzTrans hEnTrans hResultTy with
    ⟨W, A, E, rfl, rfl, rfl, hW0, _hA0, _hEW, _hD0,
      hXSmtTy, hRhsSmtTy⟩
  have hLhsSmtTy := smt_typeof_bvshl_same1 x (Term.Numeral A) W
    hXSmtTy rfl hW0
  unfold bvShlByConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsSmtTy.trans hRhsSmtTy.symm)
    (by rw [hLhsSmtTy]; intro h; cases h)

private theorem eval_bv_term_local1
    (M : SmtModel) (hM : model_wf M)
    (t : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt t) =
      SmtType.BitVec (native_int_to_nat W) ->
    exists p : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary W p /\
      native_zeq p (native_mod_total p (native_int_pow2 W)) = true := by
  intro hW0 hTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt t)
      (native_int_to_nat W) hTy with
    ⟨p, hEval, hCanonical⟩
  have hRound := native_int_to_nat_roundtrip W hW0
  have hEval' :
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary W p := by
    simpa [hRound] using hEval
  have hCanonical' :
      native_zeq p (native_mod_total p (native_int_pow2 W)) = true := by
    simpa [hRound] using hCanonical
  exact ⟨p, hEval', hCanonical'⟩

private theorem eval_bvsize_local1
    (M : SmtModel) (x : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M (__eo_to_smt (bvShiftByConst2Bvsize x)) =
      SmtValue.Numeral W := by
  intro hW0 hXTy
  have hRound := native_int_to_nat_roundtrip W hW0
  have hSize :
      __eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)) = W := by
    rw [hXTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral W
  rw [hSize]
  simp [native_ite, hW0, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem model_eval_eq_true_of_eo_eq_true1
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
        SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem eval_lt_width_local1
    (M : SmtModel) (x : Term) (A W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral A))
            (bvShiftByConst2Bvsize x))) =
      SmtValue.Boolean (native_zlt A W) := by
  intro hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.lt (SmtTerm.Numeral A)
        (__eo_to_smt (bvShiftByConst2Bvsize x))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_local1 M x W hW0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval_lt]

private theorem eval_bvsize_minus_one1
    (M : SmtModel) (x : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (bvShiftByConst2Bvsize x)) (Term.Numeral 1))) =
      SmtValue.Numeral (native_zplus W (native_zneg 1)) := by
  intro hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.neg (__eo_to_smt (bvShiftByConst2Bvsize x))
        (SmtTerm.Numeral 1)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_local1 M x W hW0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem eval_shl_end_local1
    (M : SmtModel) (x : Term) (A W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg) (bvShiftByConst2Bvsize x))
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
                (Term.Numeral A)) (Term.Numeral 0))))) =
      SmtValue.Numeral
        (native_zplus W
          (native_zneg (native_zplus 1 (native_zplus A 0)))) := by
  intro hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.neg (__eo_to_smt (bvShiftByConst2Bvsize x))
        (SmtTerm.plus (SmtTerm.Numeral 1)
          (SmtTerm.plus (SmtTerm.Numeral A) (SmtTerm.Numeral 0)))) = _
  have hInner :
      __smtx_model_eval M
          (SmtTerm.plus (SmtTerm.Numeral A) (SmtTerm.Numeral 0)) =
        SmtValue.Numeral (native_zplus A 0) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [__smtx_model_eval, __smtx_model_eval_plus]
  have hOuter :
      __smtx_model_eval M
          (SmtTerm.plus (SmtTerm.Numeral 1)
            (SmtTerm.plus (SmtTerm.Numeral A) (SmtTerm.Numeral 0))) =
        SmtValue.Numeral (native_zplus 1 (native_zplus A 0)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hInner]
    simp [__smtx_model_eval, __smtx_model_eval_plus]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_local1 M x W hW0 hXTy, hOuter]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem bv_lshr_by_const_1_premises_numeric
    (M : SmtModel) (x : Term) (A N W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvShiftByConst1LtPrem x (Term.Numeral A)) true ->
    eo_interprets M
      (bvLshrByConst1NmPrem x (Term.Numeral N)) true ->
    native_zlt A W = true /\
      N = native_zplus W (native_zneg 1) := by
  intro hW0 hXSmtTy hLtPrem hNmPrem
  have hLtEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral A))
      (bvShiftByConst2Bvsize x)) (Term.Boolean true)
    (by simpa [bvShiftByConst1LtPrem] using hLtPrem)
  have hNmEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Numeral N)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvShiftByConst2Bvsize x)) (Term.Numeral 1))
    (by simpa [bvLshrByConst1NmPrem] using hNmPrem)
  rw [eval_lt_width_local1 M x A W hW0 hXSmtTy] at hLtEq
  rw [eval_bvsize_minus_one1 M x W hW0 hXSmtTy] at hNmEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hLtEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral N))
      (SmtValue.Numeral (native_zplus W (native_zneg 1))) =
    SmtValue.Boolean true at hNmEq
  rw [__smtx_model_eval.eq_def] at hNmEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hLtEq hNmEq
  exact ⟨hLtEq, hNmEq⟩

private theorem bv_shl_by_const_1_premises_numeric
    (M : SmtModel) (x : Term) (A E W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvShiftByConst1LtPrem x (Term.Numeral A)) true ->
    eo_interprets M
      (bvShlByConst1EnPrem x (Term.Numeral A) (Term.Numeral E)) true ->
    native_zlt A W = true /\
      E = native_zplus W
        (native_zneg (native_zplus 1 (native_zplus A 0))) := by
  intro hW0 hXSmtTy hLtPrem hEnPrem
  have hLtEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral A))
      (bvShiftByConst2Bvsize x)) (Term.Boolean true)
    (by simpa [bvShiftByConst1LtPrem] using hLtPrem)
  have hEnEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Numeral E)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg) (bvShiftByConst2Bvsize x))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
          (Term.Numeral A)) (Term.Numeral 0))))
    (by simpa [bvShlByConst1EnPrem] using hEnPrem)
  rw [eval_lt_width_local1 M x A W hW0 hXSmtTy] at hLtEq
  rw [eval_shl_end_local1 M x A W hW0 hXSmtTy] at hEnEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hLtEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral E))
      (SmtValue.Numeral
        (native_zplus W
          (native_zneg (native_zplus 1 (native_zplus A 0))))) =
    SmtValue.Boolean true at hEnEq
  rw [__smtx_model_eval.eq_def] at hEnEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hLtEq hEnEq
  exact ⟨hLtEq, hEnEq⟩

private theorem native_int_pow2_add_of_nonneg_local1
    {a b : native_Int} (ha : 0 <= a) (hb : 0 <= b) :
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

private theorem int_lt_native_int_pow2_of_nonneg_lt
    {A W : native_Int} (hA0 : 0 <= A) (hAW : A < W) :
    A < native_int_pow2 W := by
  have hW0 : 0 <= W := Int.le_trans hA0 (Int.le_of_lt hAW)
  have hWNotNeg : ¬ W < 0 := Int.not_lt_of_ge hW0
  have hWCast : (Int.toNat W : Int) = W := Int.toNat_of_nonneg hW0
  have hNat : Int.toNat W < 2 ^ Int.toNat W := Nat.lt_two_pow_self
  have hInt :
      (Int.toNat W : Int) < ((2 ^ Int.toNat W : Nat) : Int) := by
    exact_mod_cast hNat
  have hWPow : W < native_int_pow2 W := by
    rw [native_int_pow2, native_zexp_total, if_neg hWNotNeg]
    rw [← hWCast]
    exact_mod_cast hNat
  exact Int.lt_trans hAW hWPow

private theorem eval_shift_amount_numeral1
    (M : SmtModel) (A W : native_Int) :
    native_zleq 0 A = true ->
    native_zlt A W = true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W))) =
      SmtValue.Binary W A := by
  intro hA0 hAW
  have ha0 : (0 : Int) <= A := by
    simpa [SmtEval.native_zleq] using hA0
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have hAPow : A < native_int_pow2 W :=
    int_lt_native_int_pow2_of_nonneg_lt ha0 haw
  have hMod : native_mod_total A (native_int_pow2 W) = A := by
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt ha0 hAPow
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (SmtTerm.Numeral A)) = _
  rw [smtx_eval_int_to_bv_term_eq]
  change __smtx_model_eval_int_to_bv
      (SmtValue.Numeral W) (SmtValue.Numeral A) = _
  simp [__smtx_model_eval_int_to_bv, hMod]

private theorem eval_shift_zero_numeral1
    (M : SmtModel) (A : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvShiftByConst1Zero (Term.Numeral A))) =
      SmtValue.Binary A 0 := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral A) (SmtTerm.Numeral 0)) = _
  simp [native_mod_total]

private theorem native_int_pow2_pos_of_nonneg_local1
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem lshr_const1_value_local
    (W A N p : native_Int)
    (hW0 : 0 <= W) (hA0 : 0 <= A) (hAW : A < W)
    (hN : N = W - 1)
    (hp0 : 0 <= p) (hpW : p < native_int_pow2 W) :
    __smtx_model_eval_bvlshr
        (SmtValue.Binary W p) (SmtValue.Binary W A) =
      __smtx_model_eval_concat
        (SmtValue.Binary A 0)
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) := by
  let D : native_Int := W - A
  let q : native_Int := native_div_total p (native_int_pow2 A)
  have hD0 : 0 <= D := by
    dsimp [D]
    exact Int.sub_nonneg.mpr (Int.le_of_lt hAW)
  have hDW : D <= W := by
    dsimp [D]
    exact Int.sub_le_self W hA0
  have hWidthExtract : N + 1 + -A = D := by
    dsimp [D]
    rw [hN]
    have hCancel : W - 1 + 1 = W := Int.sub_add_cancel W 1
    rw [hCancel]
    rfl
  have hWidthTotal : A + D = W := by
    dsimp [D]
    calc
      A + (W - A) = A + W - A := by rw [Int.add_sub_assoc]
      _ = W + A - A := by rw [Int.add_comm A W]
      _ = W := Int.add_sub_cancel W A
  have hPow : native_int_pow2 W =
      native_int_pow2 A * native_int_pow2 D := by
    rw [← hWidthTotal]
    exact native_int_pow2_add_of_nonneg_local1 hA0 hD0
  have hPowA0 : 0 < native_int_pow2 A :=
    native_int_pow2_pos_of_nonneg_local1 hA0
  have hq0 : 0 <= q := by
    dsimp [q, native_div_total]
    exact Int.ediv_nonneg hp0 (Int.le_of_lt hPowA0)
  have hqD : q < native_int_pow2 D := by
    dsimp [q, native_div_total]
    apply Int.ediv_lt_of_lt_mul hPowA0
    rw [Int.mul_comm, ← hPow]
    exact hpW
  have hqW : q < native_int_pow2 W := by
    exact Int.lt_of_lt_of_le hqD
      (native_int_pow2_le_of_le_nonneg hD0 hDW)
  have hqModD : native_mod_total q (native_int_pow2 D) = q := by
    simpa [native_mod_total] using Int.emod_eq_of_lt hq0 hqD
  have hqModW : native_mod_total q (native_int_pow2 W) = q := by
    simpa [native_mod_total] using Int.emod_eq_of_lt hq0 hqW
  have hPowZero : native_int_pow2 0 = 1 := by native_decide
  simp only [__smtx_model_eval_bvlshr, __smtx_model_eval_concat,
    __smtx_model_eval_extract, native_binary_extract, native_binary_concat]
  simp [native_zplus, native_zneg, native_zmult, hWidthExtract,
    hWidthTotal, hPowZero, hqModD, hqModW]
  change native_mod_total q (native_int_pow2 W) =
    native_mod_total
      (native_mod_total (native_mod_total q (native_int_pow2 D))
        (native_int_pow2 D)) (native_int_pow2 W)
  simp [hqModD]

private theorem eval_bv_lshr_by_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst1NmPrem x nm) true ->
    __smtx_model_eval M (__eo_to_smt (bvLshrByConst2Lhs x amount sz)) =
      __smtx_model_eval M (__eo_to_smt (bvLshrByConst1Rhs x amount nm)) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem
  rcases bv_lshr_by_const_1_context x amount sz nm hXTrans hAmountTrans
      hSzTrans hNmTrans hResultTy with
    ⟨W, A, N, rfl, rfl, rfl, hW0, hA0, _hNW, _hD0,
      hXSmtTy, _hRhsSmtTy⟩
  rcases bv_lshr_by_const_1_premises_numeric M x A N W hW0 hXSmtTy
      hLtPrem hNmPrem with ⟨hAW, hN⟩
  have hw0 : (0 : Int) <= W := by
    simpa [SmtEval.native_zleq] using hW0
  have ha0 : (0 : Int) <= A := by
    simpa [SmtEval.native_zleq] using hA0
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have hn : N = W - 1 := by
    have hsimpa := hN
    try simp [SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact hsimpa
  rcases eval_bv_term_local1 M hM x W hW0 hXSmtTy with
    ⟨p, hXEval, hCanonical⟩
  have hRange := bitvec_payload_range_of_canonical hW0 hCanonical
  have hAmountEval := eval_shift_amount_numeral1 M A W hA0 hAW
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvLshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W))) =
        __smtx_model_eval_bvlshr
          (SmtValue.Binary W p) (SmtValue.Binary W A) := by
    change __smtx_model_eval M
        (SmtTerm.bvlshr (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hAmountEval]
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral A)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by rfl
  have hInnerEval := eval_concat_term M
    (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))
    (Term.Binary 0 0)
    (__smtx_model_eval_extract
      (SmtValue.Numeral N) (SmtValue.Numeral A)
      (SmtValue.Binary W p))
    (SmtValue.Binary 0 0) hExtractEval hEmptyEval
  have hZeroEval := eval_shift_zero_numeral1 M A
  have hRhsEval := eval_concat_term M
    (bvShiftByConst1Zero (Term.Numeral A))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x (Term.Numeral N) (Term.Numeral A)))
      (Term.Binary 0 0))
    (SmtValue.Binary A 0)
    (__smtx_model_eval_concat
      (__smtx_model_eval_extract
        (SmtValue.Numeral N) (SmtValue.Numeral A)
        (SmtValue.Binary W p))
      (SmtValue.Binary 0 0)) hZeroEval hInnerEval
  rw [hLhsEval]
  change __smtx_model_eval_bvlshr
      (SmtValue.Binary W p) (SmtValue.Binary W A) =
    __smtx_model_eval M
      (__eo_to_smt
        (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)))
  rw [show __smtx_model_eval M
        (__eo_to_smt
          (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N))) =
      __smtx_model_eval_concat
        (SmtValue.Binary A 0)
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) by
      simpa [bvLshrByConst1Rhs] using hRhsEval]
  exact lshr_const1_value_local W A N p hw0 ha0 haw hn
    hRange.1 hRange.2

private theorem facts_bv_lshr_by_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst1NmPrem x nm) true ->
    eo_interprets M (bvLshrByConst1Term x amount sz nm) true := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem
  have hBool := typed_bv_lshr_by_const_1_term x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  unfold bvLshrByConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvLshrByConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvLshrByConst2Lhs x amount sz)))
      (__smtx_model_eval M (__eo_to_smt (bvLshrByConst1Rhs x amount nm)))
    rw [eval_bv_lshr_by_const_1_term M hM x amount sz nm hXTrans
      hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem]
    exact RuleProofs.smt_value_rel_refl _

private theorem shl_mod_extract_local
    (p D A : native_Int) :
    native_int_pow2 (D + A) =
        native_int_pow2 D * native_int_pow2 A ->
    native_mod_total
        (native_zmult (native_mod_total p (native_int_pow2 D))
          (native_int_pow2 A))
        (native_int_pow2 (D + A)) =
      native_mod_total (native_zmult p (native_int_pow2 A))
        (native_int_pow2 (D + A)) := by
  intro hPow
  let d := native_int_pow2 D
  let a := native_int_pow2 A
  let q := p / d
  let r := p % d
  have hDivMod : d * q + r = p := by
    simpa [d, q, r] using Int.mul_ediv_add_emod p d
  have hDistrib : (d * q + r) * a = (d * a) * q + r * a := by
    rw [Int.add_mul]
    congr 1
    ac_rfl
  have hCong : (p * a) % (d * a) = (r * a) % (d * a) := by
    calc
      (p * a) % (d * a) = ((d * q + r) * a) % (d * a) := by
        rw [hDivMod]
      _ = ((d * a) * q + r * a) % (d * a) := by rw [hDistrib]
      _ = (r * a) % (d * a) := by
        rw [Int.add_emod]
        simp [Int.mul_emod_right]
  change
    (p % native_int_pow2 D * native_int_pow2 A) %
        native_int_pow2 (D + A) =
      (p * native_int_pow2 A) % native_int_pow2 (D + A)
  rw [hPow]
  simpa [d, a, r] using hCong.symm

private theorem shl_const1_value_local
    (W A E p : native_Int)
    (hW0 : 0 <= W) (hA0 : 0 <= A) (hAW : A < W)
    (hE : E = W - (1 + A)) :
    __smtx_model_eval_bvshl
        (SmtValue.Binary W p) (SmtValue.Binary W A) =
      __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral E) (SmtValue.Numeral 0)
          (SmtValue.Binary W p))
        (__smtx_model_eval_concat
          (SmtValue.Binary A 0) (SmtValue.Binary 0 0)) := by
  let D : native_Int := W - A
  have hD0 : 0 <= D := by
    dsimp [D]
    exact Int.sub_nonneg.mpr (Int.le_of_lt hAW)
  have hWidthExtract : E + 1 = D := by
    dsimp [D]
    rw [hE]
    calc
      W - (1 + A) + 1 = W + (-(1 + A)) + 1 := by
        rw [Int.sub_eq_add_neg]
      _ = W + (-A) + (-1 + 1) := by
        rw [Int.neg_add]
        ac_rfl
      _ = W - A := by simp [Int.sub_eq_add_neg]
  have hWidthTotal : D + A = W := by
    dsimp [D]
    exact Int.sub_add_cancel W A
  have hPow : native_int_pow2 (D + A) =
      native_int_pow2 D * native_int_pow2 A :=
    native_int_pow2_add_of_nonneg_local1 hD0 hA0
  have hPowZero : native_int_pow2 0 = 1 := by native_decide
  have hDivZero : native_div_total p (native_int_pow2 0) = p := by
    simp [native_div_total, hPowZero]
  have hDivOne : native_div_total p 1 = p := by
    simp [native_div_total]
  have hZeroModA : native_mod_total 0 (native_int_pow2 A) = 0 := by
    simp [native_mod_total]
  have hResidueCanonical :
      native_mod_total
          (native_mod_total p (native_int_pow2 D))
          (native_int_pow2 D) =
        native_mod_total p (native_int_pow2 D) := by
    simp [native_mod_total]
  have hLift := shl_mod_extract_local p D A hPow
  simp only [__smtx_model_eval_bvshl, __smtx_model_eval_concat,
    __smtx_model_eval_extract, native_binary_extract, native_binary_concat]
  simp [native_zplus, native_zneg, native_zmult, hWidthExtract,
    hWidthTotal, hPowZero, hDivZero, hResidueCanonical]
  rw [hDivOne, hZeroModA, Int.add_zero]
  change native_mod_total (native_zmult p (native_int_pow2 A))
      (native_int_pow2 W) =
    native_mod_total
      (native_zmult (native_mod_total p (native_int_pow2 D))
        (native_int_pow2 A)) (native_int_pow2 W)
  rw [← hWidthTotal]
  exact hLift.symm

private theorem eval_bv_shl_by_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvShlByConst1EnPrem x amount en) true ->
    __smtx_model_eval M (__eo_to_smt (bvShlByConst2Lhs x amount sz)) =
      __smtx_model_eval M (__eo_to_smt (bvShlByConst1Rhs x amount en)) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy hLtPrem hEnPrem
  rcases bv_shl_by_const_1_context x amount sz en hXTrans hAmountTrans
      hSzTrans hEnTrans hResultTy with
    ⟨W, A, E, rfl, rfl, rfl, hW0, hA0, _hEW, _hD0,
      hXSmtTy, _hRhsSmtTy⟩
  rcases bv_shl_by_const_1_premises_numeric M x A E W hW0 hXSmtTy
      hLtPrem hEnPrem with ⟨hAW, hE⟩
  have hw0 : (0 : Int) <= W := by
    simpa [SmtEval.native_zleq] using hW0
  have ha0 : (0 : Int) <= A := by
    simpa [SmtEval.native_zleq] using hA0
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have he : E = W - (1 + A) := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      Int.sub_eq_add_neg] using hE
  rcases eval_bv_term_local1 M hM x W hW0 hXSmtTy with
    ⟨p, hXEval, _hCanonical⟩
  have hAmountEval := eval_shift_amount_numeral1 M A W hA0 hAW
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvShlByConst2Lhs x (Term.Numeral A) (Term.Numeral W))) =
        __smtx_model_eval_bvshl
          (SmtValue.Binary W p) (SmtValue.Binary W A) := by
    change __smtx_model_eval M
        (SmtTerm.bvshl (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hAmountEval]
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral E) (Term.Numeral 0))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral E) (SmtValue.Numeral 0)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by rfl
  have hZeroEval := eval_shift_zero_numeral1 M A
  have hInnerEval := eval_concat_term M
    (bvShiftByConst1Zero (Term.Numeral A)) (Term.Binary 0 0)
    (SmtValue.Binary A 0) (SmtValue.Binary 0 0)
    hZeroEval hEmptyEval
  have hRhsEval := eval_concat_term M
    (bvExtractTerm x (Term.Numeral E) (Term.Numeral 0))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvShiftByConst1Zero (Term.Numeral A))) (Term.Binary 0 0))
    (__smtx_model_eval_extract
      (SmtValue.Numeral E) (SmtValue.Numeral 0)
      (SmtValue.Binary W p))
    (__smtx_model_eval_concat
      (SmtValue.Binary A 0) (SmtValue.Binary 0 0))
    hExtractEval hInnerEval
  rw [hLhsEval]
  change __smtx_model_eval_bvshl
      (SmtValue.Binary W p) (SmtValue.Binary W A) =
    __smtx_model_eval M
      (__eo_to_smt
        (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E)))
  rw [show __smtx_model_eval M
        (__eo_to_smt
          (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E))) =
      __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral E) (SmtValue.Numeral 0)
          (SmtValue.Binary W p))
        (__smtx_model_eval_concat
          (SmtValue.Binary A 0) (SmtValue.Binary 0 0)) by
      simpa [bvShlByConst1Rhs] using hRhsEval]
  exact shl_const1_value_local W A E p hw0 ha0 haw he

private theorem facts_bv_shl_by_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvShlByConst1EnPrem x amount en) true ->
    eo_interprets M (bvShlByConst1Term x amount sz en) true := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy hLtPrem hEnPrem
  have hBool := typed_bv_shl_by_const_1_term x amount sz en
    hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  unfold bvShlByConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvShlByConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvShlByConst2Lhs x amount sz)))
      (__smtx_model_eval M (__eo_to_smt (bvShlByConst1Rhs x amount en)))
    rw [eval_bv_shl_by_const_1_term M hM x amount sz en hXTrans
      hAmountTrans hSzTrans hEnTrans hResultTy hLtPrem hEnPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvShlByConst1Program
    (x amount sz en P1 P2 : Term) : Term :=
  __eo_prog_bv_shl_by_const_1 x amount sz en (Proof.pf P1) (Proof.pf P2)

def bvLshrByConst1Program
    (x amount sz nm P1 P2 : Term) : Term :=
  __eo_prog_bv_lshr_by_const_1 x amount sz nm (Proof.pf P1) (Proof.pf P2)

private theorem shift_and_true1 {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true /\ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h |-
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h |-

private def bvShlByConst1Guard
    (x amount en amountRef1 xRef1 enRef xRef2 amountRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and (__eo_eq amount amountRef1) (__eo_eq x xRef1))
        (__eo_eq en enRef))
      (__eo_eq x xRef2))
    (__eo_eq amount amountRef2)

private def bvLshrByConst1Guard
    (x amount nm amountRef xRef1 nmRef xRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and (__eo_eq amount amountRef) (__eo_eq x xRef1))
      (__eo_eq nm nmRef))
    (__eo_eq x xRef2)

private theorem bv_shl_by_const_1_guard_refs
    {x amount en amountRef1 xRef1 enRef xRef2 amountRef2 body : Term} :
    __eo_requires
        (bvShlByConst1Guard x amount en amountRef1 xRef1 enRef xRef2
          amountRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    amountRef1 = amount /\ xRef1 = x /\ enRef = en /\
      xRef2 = x /\ amountRef2 = amount := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvShlByConst1Guard at hGuard
  rcases shift_and_true1 hGuard with ⟨hG4, hAmount2⟩
  rcases shift_and_true1 hG4 with ⟨hG3, hX2⟩
  rcases shift_and_true1 hG3 with ⟨hG2, hEn⟩
  rcases shift_and_true1 hG2 with ⟨hAmount1, hX1⟩
  exact ⟨support_eq_of_eo_eq_true amount amountRef1 hAmount1,
    support_eq_of_eo_eq_true x xRef1 hX1,
    support_eq_of_eo_eq_true en enRef hEn,
    support_eq_of_eo_eq_true x xRef2 hX2,
    support_eq_of_eo_eq_true amount amountRef2 hAmount2⟩

private theorem bv_lshr_by_const_1_guard_refs
    {x amount nm amountRef xRef1 nmRef xRef2 body : Term} :
    __eo_requires
        (bvLshrByConst1Guard x amount nm amountRef xRef1 nmRef xRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    amountRef = amount /\ xRef1 = x /\ nmRef = nm /\ xRef2 = x := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvLshrByConst1Guard at hGuard
  rcases shift_and_true1 hGuard with ⟨hG3, hX2⟩
  rcases shift_and_true1 hG3 with ⟨hG2, hNm⟩
  rcases shift_and_true1 hG2 with ⟨hAmount, hX1⟩
  exact ⟨support_eq_of_eo_eq_true amount amountRef hAmount,
    support_eq_of_eo_eq_true x xRef1 hX1,
    support_eq_of_eo_eq_true nm nmRef hNm,
    support_eq_of_eo_eq_true x xRef2 hX2⟩

private theorem bv_shl_by_const_1_premise_shape
    (x amount sz en P1 P2 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    en ≠ Term.Stuck ->
    bvShlByConst1Program x amount sz en P1 P2 ≠ Term.Stuck ->
    exists amountRef1 xRef1 enRef xRef2 amountRef2,
      P1 = bvShiftByConst1LtPrem xRef1 amountRef1 /\
      P2 = bvShlByConst1EnPrem xRef2 amountRef2 enRef := by
  intro hX hAmount hSz hEn hProg
  by_cases hShape :
      exists amountRef1 xRef1 enRef xRef2 amountRef2,
        P1 = bvShiftByConst1LtPrem xRef1 amountRef1 /\
        P2 = bvShlByConst1EnPrem xRef2 amountRef2 enRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_shl_by_const_1.eq_6 x amount sz en
      (Proof.pf P1) (Proof.pf P2) hX hAmount hSz hEn (by
        intro amountRef1 xRef1 enRef xRef2 amountRef2 hP1 hP2
        cases hP1
        cases hP2
        exact hShape
          ⟨amountRef1, xRef1, enRef, xRef2, amountRef2, rfl, rfl⟩)

private theorem bv_lshr_by_const_1_premise_shape
    (x amount sz nm P1 P2 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvLshrByConst1Program x amount sz nm P1 P2 ≠ Term.Stuck ->
    exists amountRef xRef1 nmRef xRef2,
      P1 = bvShiftByConst1LtPrem xRef1 amountRef /\
      P2 = bvLshrByConst1NmPrem xRef2 nmRef := by
  intro hX hAmount hSz hNm hProg
  by_cases hShape :
      exists amountRef xRef1 nmRef xRef2,
        P1 = bvShiftByConst1LtPrem xRef1 amountRef /\
        P2 = bvLshrByConst1NmPrem xRef2 nmRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_lshr_by_const_1.eq_6 x amount sz nm
      (Proof.pf P1) (Proof.pf P2) hX hAmount hSz hNm (by
        intro amountRef xRef1 nmRef xRef2 hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨amountRef, xRef1, nmRef, xRef2, rfl, rfl⟩)

private theorem bv_shl_by_const_1_program_canonical
    (x amount sz en : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    en ≠ Term.Stuck ->
    bvShlByConst1Program x amount sz en
        (bvShiftByConst1LtPrem x amount)
        (bvShlByConst1EnPrem x amount en) =
      bvShlByConst1Term x amount sz en := by
  intro hX hAmount hSz hEn
  unfold bvShlByConst1Program bvShiftByConst1LtPrem
    bvShlByConst1EnPrem bvShiftByConst2Bvsize
  rw [__eo_prog_bv_shl_by_const_1.eq_5 x amount sz en
    amount x en x amount hX hAmount hSz hEn]
  simp [bvShlByConst1Term, bvShlByConst2Lhs, bvShlByConst1Rhs,
    bvShiftByConst1Zero, bvShiftByConst2Const, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hEn]

private theorem bv_lshr_by_const_1_program_canonical
    (x amount sz nm : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvLshrByConst1Program x amount sz nm
        (bvShiftByConst1LtPrem x amount)
        (bvLshrByConst1NmPrem x nm) =
      bvLshrByConst1Term x amount sz nm := by
  intro hX hAmount hSz hNm
  unfold bvLshrByConst1Program bvShiftByConst1LtPrem
    bvLshrByConst1NmPrem bvShiftByConst2Bvsize
  rw [__eo_prog_bv_lshr_by_const_1.eq_5 x amount sz nm
    amount x nm x hX hAmount hSz hNm]
  simp [bvLshrByConst1Term, bvLshrByConst2Lhs, bvLshrByConst1Rhs,
    bvShiftByConst1Zero, bvShiftByConst2Const, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hNm]

private theorem bvShlByConst1Program_normalize
    (x amount sz en P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    bvShlByConst1Program x amount sz en P1 P2 ≠ Term.Stuck ->
    P1 = bvShiftByConst1LtPrem x amount /\
      P2 = bvShlByConst1EnPrem x amount en /\
      bvShlByConst1Program x amount sz en P1 P2 =
        bvShlByConst1Term x amount sz en := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  have hEn := RuleProofs.term_ne_stuck_of_has_smt_translation en hEnTrans
  rcases bv_shl_by_const_1_premise_shape x amount sz en P1 P2
      hX hAmount hSz hEn hProg with
    ⟨amountRef1, xRef1, enRef, xRef2, amountRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvShlByConst1Program bvShiftByConst1LtPrem
    bvShlByConst1EnPrem bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_shl_by_const_1.eq_5 x amount sz en
    amountRef1 xRef1 enRef xRef2 amountRef2
    hX hAmount hSz hEn] at hReq
  have hRefs := bv_shl_by_const_1_guard_refs
    (x := x) (amount := amount) (en := en)
    (amountRef1 := amountRef1) (xRef1 := xRef1) (enRef := enRef)
    (xRef2 := xRef2) (amountRef2 := amountRef2)
    (by simpa [bvShlByConst1Guard] using hReq)
  rcases hRefs with
    ⟨hAmountRef1, hXRef1, hEnRef, hXRef2, hAmountRef2⟩
  subst amountRef1
  subst xRef1
  subst enRef
  subst xRef2
  subst amountRef2
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact bv_shl_by_const_1_program_canonical x amount sz en
    hX hAmount hSz hEn

private theorem bvLshrByConst1Program_normalize
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    bvLshrByConst1Program x amount sz nm P1 P2 ≠ Term.Stuck ->
    P1 = bvShiftByConst1LtPrem x amount /\
      P2 = bvLshrByConst1NmPrem x nm /\
      bvLshrByConst1Program x amount sz nm P1 P2 =
        bvLshrByConst1Term x amount sz nm := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_lshr_by_const_1_premise_shape x amount sz nm P1 P2
      hX hAmount hSz hNm hProg with
    ⟨amountRef, xRef1, nmRef, xRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvLshrByConst1Program bvShiftByConst1LtPrem
    bvLshrByConst1NmPrem bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_lshr_by_const_1.eq_5 x amount sz nm
    amountRef xRef1 nmRef xRef2 hX hAmount hSz hNm] at hReq
  have hRefs := bv_lshr_by_const_1_guard_refs
    (x := x) (amount := amount) (nm := nm)
    (amountRef := amountRef) (xRef1 := xRef1) (nmRef := nmRef)
    (xRef2 := xRef2)
    (by simpa [bvLshrByConst1Guard] using hReq)
  rcases hRefs with ⟨hAmountRef, hXRef1, hNmRef, hXRef2⟩
  subst amountRef
  subst xRef1
  subst nmRef
  subst xRef2
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact bv_lshr_by_const_1_program_canonical x amount sz nm
    hX hAmount hSz hNm

theorem typed_bv_shl_by_const_1_program
    (x amount sz en P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Program x amount sz en P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvShlByConst1Program x amount sz en P1 P2) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvShlByConst1Program_normalize x amount sz en P1 P2
      hXTrans hAmountTrans hSzTrans hEnTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_shl_by_const_1_term x amount sz en
    hXTrans hAmountTrans hSzTrans hEnTrans hTermTy

theorem typed_bv_lshr_by_const_1_program
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Program x amount sz nm P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvLshrByConst1Program x amount sz nm P1 P2) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvLshrByConst1Program_normalize x amount sz nm P1 P2
      hXTrans hAmountTrans hSzTrans hNmTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_lshr_by_const_1_term x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hTermTy

theorem facts_bv_shl_by_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x amount sz en P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Program x amount sz en P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (bvShlByConst1Program x amount sz en P1 P2) true := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvShlByConst1Program_normalize x amount sz en P1 P2
      hXTrans hAmountTrans hSzTrans hEnTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLtPrem : eo_interprets M (bvShiftByConst1LtPrem x amount) true := by
    simpa [hP1] using hP1True
  have hEnPrem : eo_interprets M (bvShlByConst1EnPrem x amount en) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_shl_by_const_1_term M hM x amount sz en
    hXTrans hAmountTrans hSzTrans hEnTrans hTermTy hLtPrem hEnPrem

theorem facts_bv_lshr_by_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Program x amount sz nm P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (bvLshrByConst1Program x amount sz nm P1 P2) true := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvLshrByConst1Program_normalize x amount sz nm P1 P2
      hXTrans hAmountTrans hSzTrans hNmTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLtPrem : eo_interprets M (bvShiftByConst1LtPrem x amount) true := by
    simpa [hP1] using hP1True
  have hNmPrem : eo_interprets M (bvLshrByConst1NmPrem x nm) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_lshr_by_const_1_term M hM x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hTermTy hLtPrem hNmPrem

/-! Support for the in-range arithmetic-right-shift rewrite. -/

def bvAshrByConst1Sign (x nm : Term) : Term :=
  bvExtractTerm x nm nm

def bvAshrByConst1Fill (x amount nm : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.repeat amount)
    (bvAshrByConst1Sign x nm)

def bvAshrByConst1Rhs (x amount nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (bvAshrByConst1Fill x amount nm))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat)
        (bvExtractTerm x nm amount))
      (Term.Binary 0 0))

def bvAshrByConst1Term (x amount sz nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvAshrByConst2Lhs x amount sz))
    (bvAshrByConst1Rhs x amount nm)

private theorem eo_typeof_repeat_arg_bitvec_of_ne_stuck_local1
    {A idx C : Term}
    (h : __eo_typeof_repeat A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_repeat at h
  split at h <;> simp at h ⊢

private theorem repeat_amount_context_local1
    (inner rn widthTerm : Term) :
    __eo_typeof inner =
        Term.Apply (Term.UOp UserOp.BitVec) widthTerm ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.repeat rn) inner) ≠
      Term.Stuck ->
    ∃ r : native_Int,
      rn = Term.Numeral r ∧ native_zlt 0 r = true := by
  intro hInnerTy hRepeatNe
  change __eo_typeof_repeat (__eo_typeof rn) rn (__eo_typeof inner) ≠
      Term.Stuck at hRepeatNe
  rw [hInnerTy] at hRepeatNe
  have hParts :
      __eo_typeof rn = Term.UOp UserOp.Int ∧
      __eo_requires (__eo_gt rn (Term.Numeral 0))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec)
            (__eo_mul rn widthTerm)) ≠ Term.Stuck := by
    unfold __eo_typeof_repeat at hRepeatNe
    split at hRepeatNe <;> simp_all
  have hGuard :
      __eo_gt rn (Term.Numeral 0) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hParts.2
  cases rn <;> simp [__eo_gt] at hGuard
  case Numeral r =>
    exact ⟨r, rfl, by simpa [__eo_gt] using hGuard⟩

private theorem smt_typeof_bvashr_same1
    (x amount : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt amount) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt (bvAshrByConst2Lhs x amount
      (Term.Numeral W))) = SmtType.BitVec (native_int_to_nat W) := by
  intro hXTy hAmountTy hW0
  have hConstTy := smt_typeof_bv_const_of_int_type amount W hAmountTy hW0
  have hConstTy' :
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount)) =
        SmtType.BitVec (native_int_to_nat W) := by
    have hsimpa := hConstTy
    try simp [bvShiftByConst2Const] at hsimpa ⊢
    exact hsimpa
  change __smtx_typeof
      (SmtTerm.bvashr (__eo_to_smt x)
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem bv_ashr_by_const_1_context
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvAshrByConst1Term x amount sz nm) = Term.Bool ->
    ∃ W A N : native_Int,
      sz = Term.Numeral W ∧ amount = Term.Numeral A ∧
      nm = Term.Numeral N ∧
      native_zleq 0 W = true ∧ native_zlt 0 A = true ∧
      native_zleq 0 N = true ∧ native_zlt N W = true ∧
      native_zlt 0
        (native_zplus (native_zplus N 1) (native_zneg A)) = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvAshrByConst1Rhs x amount nm)) = Term.Bool
    at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases shift_operand_context1 x amount sz hXTrans hAmountTrans
      hSzTrans hLhsNe with
    ⟨W, rfl, hW0, hXTy, _hAmountTy, _hConstTy, hXSmtTy,
      _hAmountSmtTy⟩
  change __eo_typeof_concat
      (__eo_typeof (bvAshrByConst1Fill x amount nm))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x nm amount)) (Term.Binary 0 0))) ≠
      Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsNe with
    ⟨_wFill, wInner, _hFillTy, hInnerTy⟩
  have hInnerNe :
      __eo_typeof_concat (__eo_typeof (bvExtractTerm x nm amount))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    have hsimpa := (show
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x nm amount)) (Term.Binary 0 0)) ≠
        Term.Stuck by
      rw [hInnerTy]
      intro h
      cases h)
    try simp at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerNe with
    ⟨_wExtract, _wEmpty, hExtractTy, _hEmptyTy⟩
  have hExtractNe : __eo_typeof (bvExtractTerm x nm amount) ≠
      Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x nm amount hXTrans hExtractNe with
    ⟨W', N, A, hXTy', hNm, hAmount, _hW'0, hA0, hNW', hD0,
      _hXSmtTy'⟩
  have hWW' : W' = W := by
    rw [hXTy] at hXTy'
    injection hXTy' with _ hNum
    injection hNum with hEq
    exact hEq.symm
  subst W'
  subst amount
  subst nm
  have hFillNe :
      __eo_typeof (bvAshrByConst1Fill x (Term.Numeral A)
        (Term.Numeral N)) ≠ Term.Stuck := by
    rw [_hFillTy]
    intro h
    cases h
  have hFillNe' :
      __eo_typeof_repeat (Term.UOp UserOp.Int) (Term.Numeral A)
          (__eo_typeof (bvAshrByConst1Sign x (Term.Numeral N))) ≠
        Term.Stuck := by
    have hsimpa := hFillNe
    try simp [bvAshrByConst1Fill] at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_repeat_arg_bitvec_of_ne_stuck_local1 hFillNe' with
    ⟨wSign, hSignTy⟩
  have hSignNe :
      __eo_typeof (bvAshrByConst1Sign x (Term.Numeral N)) ≠
        Term.Stuck := by
    rw [hSignTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x (Term.Numeral N)
      (Term.Numeral N) hXTrans hSignNe with
    ⟨W'', NHigh, NLow, hXTy'', hNHigh, hNLow, _hW''0, hN0,
      hNW'', _hSignD0, _hXSmtTy''⟩
  have hWW'' : W'' = W := by
    rw [hXTy] at hXTy''
    injection hXTy'' with _ hNum
    injection hNum with hEq
    exact hEq.symm
  subst W''
  have hNHighEq : NHigh = N := by
    injection hNHigh with hEq
    exact hEq.symm
  have hNLowEq : NLow = N := by
    injection hNLow with hEq
    exact hEq.symm
  subst NHigh
  subst NLow
  rcases repeat_amount_context_local1
      (bvAshrByConst1Sign x (Term.Numeral N)) (Term.Numeral A) wSign
      hSignTy hFillNe with ⟨A', hAEq, hAPos⟩
  have hAA' : A' = A := by
    injection hAEq with hEq
    exact hEq.symm
  subst A'
  exact ⟨W, A, N, rfl, rfl, rfl, hW0, hAPos, hN0, hNW', hD0,
    hXSmtTy⟩

private theorem typed_bv_ashr_by_const_1_term
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvAshrByConst1Term x amount sz nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvAshrByConst1Term x amount sz nm) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  rcases bv_ashr_by_const_1_context x amount sz nm hXTrans hAmountTrans
      hSzTrans hNmTrans hResultTy with
    ⟨W, A, N, rfl, rfl, rfl, hW0, hAPos, hN0, hNW, hD0,
      hXSmtTy⟩
  have hLhsTy := smt_typeof_bvashr_same1 x (Term.Numeral A) W
    hXSmtTy rfl hW0
  have hSignTy :
      __smtx_typeof
          (__eo_to_smt (bvAshrByConst1Sign x (Term.Numeral N))) =
        SmtType.BitVec 1 := by
    have hOne :
        native_zplus (native_zplus N 1) (native_zneg N) = 1 := by
      simp [SmtEval.native_zplus, SmtEval.native_zneg]
      grind
    have hSignD0 :
        native_zlt 0
            (native_zplus (native_zplus N 1) (native_zneg N)) = true := by
      rw [hOne]
      native_decide
    have hRaw := smt_typeof_extract_of_context x W N N hXSmtTy
      hW0 hN0 hNW hSignD0
    simpa [bvAshrByConst1Sign, hOne, native_int_to_nat,
      SmtEval.native_int_to_nat] using hRaw
  have hAOne : native_zleq 1 A = true := by
    have hAInt : (0 : Int) < A := by
      simpa [SmtEval.native_zlt] using hAPos
    have hsimpa := hAInt
    try simp [SmtEval.native_zleq] at hsimpa ⊢
    exact hsimpa
  have hFillTy :
      __smtx_typeof
          (__eo_to_smt
            (bvAshrByConst1Fill x (Term.Numeral A)
              (Term.Numeral N))) =
        SmtType.BitVec (native_int_to_nat A) := by
    unfold bvAshrByConst1Fill
    change __smtx_typeof
      (SmtTerm.repeat (SmtTerm.Numeral A)
        (__eo_to_smt (bvAshrByConst1Sign x (Term.Numeral N)))) = _
    rw [typeof_repeat_eq, hSignTy]
    simp [__smtx_typeof_repeat, native_ite, hAOne,
      SmtEval.native_zmult, native_nat_to_int, Smtm.native_nat_to_int]
  have hA0 := native_zleq_of_zlt_true 0 A hAPos
  have hLowTy := smt_typeof_extract_of_context x W N A hXSmtTy
    hW0 hA0 hNW hD0
  have hInnerTy := smt_typeof_concat_bitvec
    (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))
    (Term.Binary 0 0) _ _ hLowTy smt_typeof_empty_bitvec
  have hRhsRawTy := smt_typeof_concat_bitvec
    (bvAshrByConst1Fill x (Term.Numeral A) (Term.Numeral N))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x (Term.Numeral N) (Term.Numeral A)))
      (Term.Binary 0 0)) _ _ hFillTy hInnerTy
  have hLhsTrans : RuleProofs.eo_has_smt_translation
      (bvAshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsTy]
    intro h
    cases h
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvAshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)) := by
    unfold RuleProofs.eo_has_smt_translation bvAshrByConst1Rhs
    rw [hRhsRawTy]
    intro h
    cases h
  have hEOTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hLhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvAshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W))
      (__eo_typeof
        (bvAshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W)))
      (__eo_to_smt
        (bvAshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W)))
      rfl hLhsTrans rfl
  have hRhsBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvAshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N))
      (__eo_typeof
        (bvAshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)))
      (__eo_to_smt
        (bvAshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)))
      rfl hRhsTrans rfl
  unfold bvAshrByConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
    (by rw [hLhsTy]; intro h; cases h)

private theorem bvlshr_bitvec_value_local1 (x : BitVec W) (A : Nat) :
    __smtx_model_eval_bvlshr
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int) (↑A : Int)) =
      SmtValue.Binary (↑W : Int) (↑(x >>> A).toNat : Int) := by
  simp only [__smtx_model_eval_bvlshr, SmtEval.native_mod_total,
    SmtEval.native_div_total, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [natpow2_eq A, natpow2_eq W]
  norm_cast
  rw [Nat.mod_eq_of_lt]
  simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using
    (x >>> A).isLt

private theorem bvnot_bitvec_value_local1 (x : BitVec W) :
    __smtx_model_eval_bvnot
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int)) =
      SmtValue.Binary (↑W : Int) (↑(~~~x).toNat : Int) := by
  simp only [__smtx_model_eval_bvnot, native_binary_not,
    SmtEval.native_zplus, SmtEval.native_zneg,
    SmtEval.native_mod_total]
  rw [natpow2_eq W]
  have hx : x.toNat + 1 ≤ 2 ^ W := by omega
  have hRaw :
      (2 ^ W : Int) + -((x.toNat : Int) + 1) =
        (↑(~~~x).toNat : Int) := by
    rw [BitVec.toNat_not]
    have hSub : 2 ^ W - 1 - x.toNat = 2 ^ W - (x.toNat + 1) := by
      omega
    rw [hSub, Int.ofNat_sub hx]
    push_cast
    omega
  rw [hRaw]
  norm_cast
  rw [Nat.mod_eq_of_lt]
  exact (~~~x).isLt

private theorem extractLsb_sign_bit_local1
    {x : BitVec W} (hWPos : 0 < W) :
    x.extractLsb' (W - 1) 1 = BitVec.fill 1 x.msb := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  rw [BitVec.getElem_extractLsb', BitVec.getElem_fill]
  simp only [Nat.add_zero]
  exact (BitVec.msb_eq_getLsbD_last x).symm

private theorem eval_extract_msb_bitvec_local1
    (x : BitVec W) (hW : 0 < W) :
    __smtx_model_eval_extract
        (SmtValue.Numeral (↑(W - 1) : Int))
        (SmtValue.Numeral (↑(W - 1) : Int))
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int)) =
      SmtValue.Binary 1 (↑x.msb.toNat : Int) := by
  rw [extract_val_bitvec_start_len W (W - 1) 1 (↑x.toNat : Int)
    (↑(W - 1) : Int) (↑(W - 1) : Int)
    (by exact Int.natCast_nonneg _)
    (by norm_cast; exact x.isLt) rfl (by push_cast; omega)]
  rw [bitvec_ofInt_natCast_toNat, extractLsb_sign_bit_local1 hW]
  cases x.msb <;> native_decide

private theorem bvashr_bitvec_value_local1
    (x : BitVec W) (A : Nat) (hW : 0 < W) :
    __smtx_model_eval_bvashr
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int) (↑A : Int)) =
      SmtValue.Binary (↑W : Int) (↑(x.sshiftRight A).toNat : Int) := by
  unfold __smtx_model_eval_bvashr
  simp only [__smtx_bv_sizeof_value, __smtx_model_eval__,
    SmtEval.native_zplus, SmtEval.native_zneg]
  have hSub : (↑W : Int) + -1 = (↑(W - 1) : Int) := by omega
  rw [hSub, eval_extract_msb_bitvec_local1 x hW]
  cases hmsb : x.msb with
  | false =>
      simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval_ite]
      rw [bvlshr_bitvec_value_local1]
      rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
  | true =>
      simp [__smtx_model_eval_eq, native_veq, __smtx_model_eval_ite]
      rw [bvnot_bitvec_value_local1 x, bvlshr_bitvec_value_local1,
        bvnot_bitvec_value_local1]
      rw [BitVec.sshiftRight_eq_of_msb_true hmsb]

private theorem bvashr_decomp_local1
    (x : BitVec W) (A : Nat) (hAW : A < W) :
    x.sshiftRight A =
      ((BitVec.fill A x.msb) ++ (x.extractLsb' A (W - A))).cast
        (by omega) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_sshiftRight hi]
  simp only [BitVec.getElem_cast, BitVec.getElem_append,
    BitVec.getElem_fill, BitVec.getElem_extractLsb']
  by_cases hLow : i < W - A
  · have hAI : A + i < W := by omega
    simp only [hLow]
    rw [dif_pos hAI, BitVec.getLsbD_eq_getElem hAI]
    simp
  · have hHigh : W - A ≤ i := Nat.le_of_not_gt hLow
    simp [hLow]
    omega

private theorem concat_bitvec_values_local1
    (x : BitVec A) (y : BitVec B) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑B : Int) (↑y.toNat : Int)) =
      SmtValue.Binary (↑(A + B) : Int) (↑(x ++ y).toNat : Int) := by
  simp only [__smtx_model_eval_concat, SmtEval.native_zplus,
    native_mod_total, native_binary_concat, native_zmult]
  have hWidth : (↑A + ↑B : Int) = ↑(A + B) := by norm_cast
  rw [hWidth, natpow2_eq B, natpow2_eq (A + B),
    show ((2 : Int) ^ B) = ((2 ^ B : Nat) : Int) by norm_cast,
    show ((2 : Int) ^ (A + B)) = ((2 ^ (A + B) : Nat) : Int) by
      norm_cast]
  norm_cast
  have hyLt : y.toNat < 2 ^ B := y.isLt
  have hShiftOr := Nat.shiftLeft_add_eq_or_of_lt hyLt x.toNat
  have hFormula : x.toNat * 2 ^ B + y.toNat = (x ++ y).toNat := by
    rw [BitVec.toNat_append, ← hShiftOr, Nat.shiftLeft_eq]
  rw [hFormula, Nat.mod_eq_of_lt (x ++ y).isLt]

private theorem concat_empty_right_value_local1 (x : BitVec A) :
    __smtx_model_eval_concat
        (SmtValue.Binary (↑A : Int) (↑x.toNat : Int))
        (SmtValue.Binary 0 0) =
      SmtValue.Binary (↑A : Int) (↑x.toNat : Int) := by
  have h := concat_bitvec_values_local1 x (0#0)
  simpa using h

private theorem native_int_pow2_nat_succ_local1 (n : Nat) :
    native_int_pow2 (Int.ofNat (Nat.succ n)) =
      2 * native_int_pow2 (Int.ofNat n) := by
  have h1 : (0 : Int) ≤ 1 := by decide
  have hn : (0 : Int) ≤ Int.ofNat n := Int.natCast_nonneg n
  have hAdd := native_int_pow2_add_of_nonneg_local1
    (a := Int.ofNat n) (b := 1) hn h1
  have hSucc : (Int.ofNat (Nat.succ n) : Int) = Int.ofNat n + 1 := by
    simp
  have hPow1 : native_int_pow2 (1 : Int) = 2 := by native_decide
  rw [hSucc, hAdd, hPow1, Int.mul_comm]

private theorem native_pow2_minus_one_mod_self_local1
    (w : native_Int) :
    native_zleq 0 w = true ->
    native_mod_total (native_int_pow2 w - 1) (native_int_pow2 w) =
      native_int_pow2 w - 1 := by
  intro hW0
  have hw : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hW0
  have hPowPos : 0 < native_int_pow2 w :=
    native_int_pow2_pos_of_nonneg_local1 hw
  have hLo : 0 ≤ native_int_pow2 w - 1 :=
    Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr hPowPos)
  have hHi : native_int_pow2 w - 1 < native_int_pow2 w :=
    Int.sub_lt_self _ (by decide : (0 : Int) < 1)
  simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hLo hHi

private theorem eval_repeat_rec_zero_bit_local1 :
    ∀ n : native_Nat,
      __smtx_repeat_rec n (SmtValue.Binary 1 0) =
        SmtValue.Binary (native_nat_to_int n) 0
  | Nat.zero => by
      simp [__smtx_repeat_rec, native_nat_to_int,
        Smtm.native_nat_to_int]
  | Nat.succ n => by
      rw [__smtx_repeat_rec, eval_repeat_rec_zero_bit_local1 n]
      have hWidth :
          native_zplus (1 : native_Int) (native_nat_to_int n) =
            native_nat_to_int (Nat.succ n) := by
        simp [SmtEval.native_zplus, native_nat_to_int,
          Smtm.native_nat_to_int]
        rw [Int.add_comm]
      have hWidthInt : (1 : Int) + ↑n = ↑n + 1 := by
        rw [Int.add_comm]
      simp [__smtx_model_eval_concat, native_binary_concat,
        SmtEval.native_zplus, SmtEval.native_zmult,
        native_nat_to_int, Smtm.native_nat_to_int,
        native_mod_total, hWidth, hWidthInt]

private theorem eval_repeat_rec_one_bit_local1 :
    ∀ n : native_Nat,
      __smtx_repeat_rec n (SmtValue.Binary 1 1) =
        SmtValue.Binary (native_nat_to_int n)
          (native_int_pow2 (native_nat_to_int n) - 1)
  | Nat.zero => by
      simp [__smtx_repeat_rec, native_nat_to_int,
        Smtm.native_nat_to_int, native_int_pow2, native_zexp_total]
  | Nat.succ n => by
      rw [__smtx_repeat_rec, eval_repeat_rec_one_bit_local1 n]
      have hPowSucc :
          native_int_pow2 (native_nat_to_int (Nat.succ n)) =
            2 * native_int_pow2 (native_nat_to_int n) := by
        simpa [native_nat_to_int, Smtm.native_nat_to_int] using
          native_int_pow2_nat_succ_local1 n
      have hRaw :
          native_int_pow2 (native_nat_to_int n) +
              (native_int_pow2 (native_nat_to_int n) - 1) =
            native_int_pow2 (native_nat_to_int (Nat.succ n)) - 1 := by
        let P := native_int_pow2 (native_nat_to_int n)
        change P + (P - 1) =
          native_int_pow2 (native_nat_to_int (Nat.succ n)) - 1
        rw [hPowSucc]
        change P + (P - 1) = 2 * P - 1
        grind
      have hSucc0 :
          native_zleq 0 (native_nat_to_int (Nat.succ n)) = true := by
        have hNonneg : (0 : Int) ≤ Int.ofNat (Nat.succ n) :=
          Int.natCast_nonneg (Nat.succ n)
        have hsimpa := hNonneg
        try simp [SmtEval.native_zleq] at hsimpa ⊢
        exact hsimpa
      have hMod := native_pow2_minus_one_mod_self_local1
        (native_nat_to_int (Nat.succ n)) hSucc0
      have hWidthInt : (1 : Int) + ↑n = ↑n + 1 := by
        rw [Int.add_comm]
      have hPayload :
          native_mod_total
              (native_int_pow2 (native_nat_to_int n) +
                (native_int_pow2 (native_nat_to_int n) - 1))
              (native_int_pow2 (↑n + 1)) =
            native_int_pow2 (↑n + 1) - 1 := by
        rw [hRaw]
        simpa [native_nat_to_int, Smtm.native_nat_to_int] using hMod
      simpa [__smtx_model_eval_concat, native_binary_concat,
        SmtEval.native_zplus, SmtEval.native_zmult,
        native_nat_to_int, Smtm.native_nat_to_int, hWidthInt]
        using hPayload

private theorem eval_repeat_bit_local1 (A : Nat) (b : Bool) :
    __smtx_model_eval_repeat (SmtValue.Numeral (↑A : Int))
        (SmtValue.Binary 1 (↑b.toNat : Int)) =
      SmtValue.Binary (↑A : Int) (↑(BitVec.fill A b).toNat : Int) := by
  have hAToNat : native_int_to_nat (↑A : Int) = A := by
    simp [native_int_to_nat, SmtEval.native_int_to_nat]
  have hPowOne : 1 ≤ (2 : Nat) ^ A :=
    Nat.one_le_pow A 2 (by decide)
  have hOnesCast : Int.ofNat ((2 : Nat) ^ A - 1) =
      (2 : Int) ^ A - 1 := by
    simpa using (Int.ofNat_sub hPowOne)
  cases b with
  | false =>
      simp [__smtx_model_eval_repeat, hAToNat,
        eval_repeat_rec_zero_bit_local1, BitVec.fill_toNat,
        native_nat_to_int, Smtm.native_nat_to_int]
  | true =>
      simp [__smtx_model_eval_repeat, hAToNat,
        eval_repeat_rec_one_bit_local1, BitVec.fill_toNat,
        native_nat_to_int, Smtm.native_nat_to_int, natpow2_eq]
      exact hOnesCast.symm

private theorem ashr_const1_value_local1
    (W A N p : native_Int)
    (hW0 : 0 ≤ W) (hA0 : 0 ≤ A) (hAPos : 0 < A) (hAW : A < W)
    (hN : N = W - 1) (hp0 : 0 ≤ p)
    (hpW : p < native_int_pow2 W) :
    __smtx_model_eval_bvashr
        (SmtValue.Binary W p) (SmtValue.Binary W A) =
      __smtx_model_eval_concat
        (__smtx_model_eval_repeat (SmtValue.Numeral A)
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral N)
            (SmtValue.Binary W p)))
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) := by
  let WN := Int.toNat W
  let AN := Int.toNat A
  let xBV := BitVec.ofInt WN p
  let lowBV := xBV.extractLsb' AN (WN - AN)
  have hWRound : (↑WN : Int) = W := by
    simpa [WN] using Int.toNat_of_nonneg hW0
  have hARound : (↑AN : Int) = A := by
    simpa [AN] using Int.toNat_of_nonneg hA0
  have hANPos : 0 < AN := by
    have hANPosInt : (0 : Int) < (↑AN : Int) := by
      rw [hARound]
      exact hAPos
    exact_mod_cast hANPosInt
  have hANW : AN < WN := by
    have hANWInt : (↑AN : Int) < (↑WN : Int) := by
      rw [hARound, hWRound]
      exact hAW
    exact_mod_cast hANWInt
  have hWNPos : 0 < WN := Nat.lt_trans hANPos hANW
  have hNCast : N = (↑(WN - 1) : Int) := by
    calc
      N = W - 1 := hN
      _ = (↑WN : Int) - 1 := by simpa only [hWRound]
      _ = (↑(WN - 1) : Int) := by omega
  have hDCast : N + 1 + -A = (↑(WN - AN) : Int) := by
    have hCastSub :
        (↑(WN - AN) : Int) = (↑WN : Int) - (↑AN : Int) :=
      Int.ofNat_sub (Nat.le_of_lt hANW)
    calc
      N + 1 + -A = W - A := by rw [hN]; grind
      _ = (↑WN : Int) - (↑AN : Int) := by
        simp only [hWRound, hARound]
      _ = (↑(WN - AN) : Int) := hCastSub.symm
  have hpW' : p < (2 : Int) ^ WN := by
    simpa [← hWRound, natpow2_eq] using hpW
  have hXToNat : (↑xBV.toNat : Int) = p := by
    have hToNat := ofInt_toNat_canonical WN p hp0 hpW'
    rw [show xBV.toNat = Int.toNat p by simpa [xBV] using hToNat]
    exact Int.toNat_of_nonneg hp0
  have hSignEval :
      __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral N)
          (SmtValue.Binary W p) =
        SmtValue.Binary 1 (↑xBV.msb.toNat : Int) := by
    rw [show W = (↑WN : Int) by exact hWRound.symm,
      show p = (↑xBV.toNat : Int) by exact hXToNat.symm,
      hNCast]
    exact eval_extract_msb_bitvec_local1 xBV hWNPos
  have hRepeatEval :
      __smtx_model_eval_repeat (SmtValue.Numeral A)
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral N)
            (SmtValue.Binary W p)) =
        SmtValue.Binary (↑AN : Int)
          (↑(BitVec.fill AN xBV.msb).toNat : Int) := by
    rw [hSignEval, ← hARound]
    exact eval_repeat_bit_local1 AN xBV.msb
  have hLowEval :
      __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral A)
          (SmtValue.Binary W p) =
        SmtValue.Binary (↑(WN - AN) : Int) (↑lowBV.toNat : Int) := by
    rw [show W = (↑WN : Int) by exact hWRound.symm,
      hNCast, ← hARound]
    simpa [lowBV, xBV] using
      extract_val_bitvec_start_len WN AN (WN - AN) p
        (↑(WN - 1) : Int) (↑AN : Int) hp0 hpW' rfl (by
          push_cast
          omega)
  have hInnerEval :
      __smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0) =
        SmtValue.Binary (↑(WN - AN) : Int) (↑lowBV.toNat : Int) := by
    rw [hLowEval]
    exact concat_empty_right_value_local1 lowBV
  rw [hRepeatEval, hInnerEval, concat_bitvec_values_local1]
  have hWidth : AN + (WN - AN) = WN := by omega
  have hAshr := bvashr_bitvec_value_local1 xBV AN hWNPos
  have hDecomp := bvashr_decomp_local1 xBV AN hANW
  rw [show W = (↑WN : Int) by exact hWRound.symm,
    show A = (↑AN : Int) by exact hARound.symm,
    show p = (↑xBV.toNat : Int) by exact hXToNat.symm]
  rw [hAshr, hDecomp]
  simp only [BitVec.toNat_cast]
  simpa [hWidth, lowBV, BitVec.extractLsb'_toNat]

private theorem eval_bv_ashr_by_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvAshrByConst1Term x amount sz nm) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst1NmPrem x nm) true ->
    __smtx_model_eval M (__eo_to_smt (bvAshrByConst2Lhs x amount sz)) =
      __smtx_model_eval M (__eo_to_smt (bvAshrByConst1Rhs x amount nm)) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem
  rcases bv_ashr_by_const_1_context x amount sz nm hXTrans hAmountTrans
      hSzTrans hNmTrans hResultTy with
    ⟨W, A, N, rfl, rfl, rfl, hW0, hAPos, _hN0, _hNW, _hD0,
      hXSmtTy⟩
  have hA0 := native_zleq_of_zlt_true 0 A hAPos
  rcases bv_lshr_by_const_1_premises_numeric M x A N W hW0 hXSmtTy
      hLtPrem hNmPrem with ⟨hAW, hN⟩
  have hw0 : (0 : Int) ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have ha0 : (0 : Int) ≤ A := by
    simpa [SmtEval.native_zleq] using hA0
  have haPos : (0 : Int) < A := by
    simpa [SmtEval.native_zlt] using hAPos
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have hn : N = W - 1 := by
    have hsimpa := hN
    try simp [SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact hsimpa
  rcases eval_bv_term_local1 M hM x W hW0 hXSmtTy with
    ⟨p, hXEval, hCanonical⟩
  have hRange := bitvec_payload_range_of_canonical hW0 hCanonical
  have hAmountEval := eval_shift_amount_numeral1 M A W hA0 hAW
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvAshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W))) =
        __smtx_model_eval_bvashr
          (SmtValue.Binary W p) (SmtValue.Binary W A) := by
    change __smtx_model_eval M
        (SmtTerm.bvashr (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hAmountEval]
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt (bvAshrByConst1Sign x (Term.Numeral N))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral N)
          (SmtValue.Binary W p) := by
    unfold bvAshrByConst1Sign
    rw [eval_extract_term, hXEval]
  have hFillEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvAshrByConst1Fill x (Term.Numeral A)
              (Term.Numeral N))) =
        __smtx_model_eval_repeat (SmtValue.Numeral A)
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral N)
            (SmtValue.Binary W p)) := by
    change __smtx_model_eval M
        (SmtTerm.repeat (SmtTerm.Numeral A)
          (__eo_to_smt (bvAshrByConst1Sign x (Term.Numeral N)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hSignEval]
    simp [__smtx_model_eval]
  have hLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral A)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by rfl
  have hInnerEval := eval_concat_term M
    (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))
    (Term.Binary 0 0)
    (__smtx_model_eval_extract
      (SmtValue.Numeral N) (SmtValue.Numeral A)
      (SmtValue.Binary W p))
    (SmtValue.Binary 0 0) hLowEval hEmptyEval
  have hRhsEval := eval_concat_term M
    (bvAshrByConst1Fill x (Term.Numeral A) (Term.Numeral N))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x (Term.Numeral N) (Term.Numeral A)))
      (Term.Binary 0 0))
    (__smtx_model_eval_repeat (SmtValue.Numeral A)
      (__smtx_model_eval_extract
        (SmtValue.Numeral N) (SmtValue.Numeral N)
        (SmtValue.Binary W p)))
    (__smtx_model_eval_concat
      (__smtx_model_eval_extract
        (SmtValue.Numeral N) (SmtValue.Numeral A)
        (SmtValue.Binary W p))
      (SmtValue.Binary 0 0)) hFillEval hInnerEval
  rw [hLhsEval]
  rw [show __smtx_model_eval M
        (__eo_to_smt
          (bvAshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N))) =
      __smtx_model_eval_concat
        (__smtx_model_eval_repeat (SmtValue.Numeral A)
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral N)
            (SmtValue.Binary W p)))
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) by
      simpa [bvAshrByConst1Rhs] using hRhsEval]
  exact ashr_const1_value_local1 W A N p hw0 ha0 haPos haw hn
    hRange.1 hRange.2

private theorem facts_bv_ashr_by_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvAshrByConst1Term x amount sz nm) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst1NmPrem x nm) true ->
    eo_interprets M (bvAshrByConst1Term x amount sz nm) true := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem
  have hBool := typed_bv_ashr_by_const_1_term x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  unfold bvAshrByConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvAshrByConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvAshrByConst2Lhs x amount sz)))
      (__smtx_model_eval M (__eo_to_smt (bvAshrByConst1Rhs x amount nm)))
    rw [eval_bv_ashr_by_const_1_term M hM x amount sz nm hXTrans
      hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvAshrByConst1Program
    (x amount sz nm P1 P2 : Term) : Term :=
  __eo_prog_bv_ashr_by_const_1 x amount sz nm (Proof.pf P1) (Proof.pf P2)

private theorem bv_ashr_by_const_1_premise_shape
    (x amount sz nm P1 P2 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvAshrByConst1Program x amount sz nm P1 P2 ≠ Term.Stuck ->
    ∃ amountRef xRef1 nmRef xRef2,
      P1 = bvShiftByConst1LtPrem xRef1 amountRef ∧
      P2 = bvLshrByConst1NmPrem xRef2 nmRef := by
  intro hX hAmount hSz hNm hProg
  by_cases hShape :
      ∃ amountRef xRef1 nmRef xRef2,
        P1 = bvShiftByConst1LtPrem xRef1 amountRef ∧
        P2 = bvLshrByConst1NmPrem xRef2 nmRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_ashr_by_const_1.eq_6 x amount sz nm
      (Proof.pf P1) (Proof.pf P2) hX hAmount hSz hNm (by
        intro amountRef xRef1 nmRef xRef2 hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨amountRef, xRef1, nmRef, xRef2, rfl, rfl⟩)

private theorem bv_ashr_by_const_1_program_canonical
    (x amount sz nm : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvAshrByConst1Program x amount sz nm
        (bvShiftByConst1LtPrem x amount)
        (bvLshrByConst1NmPrem x nm) =
      bvAshrByConst1Term x amount sz nm := by
  intro hX hAmount hSz hNm
  unfold bvAshrByConst1Program bvShiftByConst1LtPrem
    bvLshrByConst1NmPrem bvShiftByConst2Bvsize
  rw [__eo_prog_bv_ashr_by_const_1.eq_5 x amount sz nm
    amount x nm x hX hAmount hSz hNm]
  simp [bvAshrByConst1Term, bvAshrByConst2Lhs, bvAshrByConst1Rhs,
    bvAshrByConst1Fill, bvAshrByConst1Sign, bvShiftByConst2Const,
    bvExtractTerm, __eo_requires, __eo_and, __eo_eq, native_ite,
    native_teq, native_not, native_and, hX, hAmount, hNm]

private theorem bvAshrByConst1Program_normalize
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    bvAshrByConst1Program x amount sz nm P1 P2 ≠ Term.Stuck ->
    P1 = bvShiftByConst1LtPrem x amount ∧
      P2 = bvLshrByConst1NmPrem x nm ∧
      bvAshrByConst1Program x amount sz nm P1 P2 =
        bvAshrByConst1Term x amount sz nm := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_ashr_by_const_1_premise_shape x amount sz nm P1 P2
      hX hAmount hSz hNm hProg with
    ⟨amountRef, xRef1, nmRef, xRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvAshrByConst1Program bvShiftByConst1LtPrem
    bvLshrByConst1NmPrem bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_ashr_by_const_1.eq_5 x amount sz nm
    amountRef xRef1 nmRef xRef2 hX hAmount hSz hNm] at hReq
  have hRefs := bv_lshr_by_const_1_guard_refs
    (x := x) (amount := amount) (nm := nm)
    (amountRef := amountRef) (xRef1 := xRef1) (nmRef := nmRef)
    (xRef2 := xRef2)
    (by simpa [bvLshrByConst1Guard] using hReq)
  rcases hRefs with ⟨hAmountRef, hXRef1, hNmRef, hXRef2⟩
  subst amountRef
  subst xRef1
  subst nmRef
  subst xRef2
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact bv_ashr_by_const_1_program_canonical x amount sz nm
    hX hAmount hSz hNm

theorem typed_bv_ashr_by_const_1_program
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvAshrByConst1Program x amount sz nm P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvAshrByConst1Program x amount sz nm P1 P2) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvAshrByConst1Program_normalize x amount sz nm P1 P2
      hXTrans hAmountTrans hSzTrans hNmTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvAshrByConst1Term x amount sz nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_ashr_by_const_1_term x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hTermTy

theorem facts_bv_ashr_by_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvAshrByConst1Program x amount sz nm P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (bvAshrByConst1Program x amount sz nm P1 P2) true := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvAshrByConst1Program_normalize x amount sz nm P1 P2
      hXTrans hAmountTrans hSzTrans hNmTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvAshrByConst1Term x amount sz nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLtPrem : eo_interprets M (bvShiftByConst1LtPrem x amount) true := by
    simpa [hP1] using hP1True
  have hNmPrem : eo_interprets M (bvLshrByConst1NmPrem x nm) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_ashr_by_const_1_term M hM x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hTermTy hLtPrem hNmPrem
