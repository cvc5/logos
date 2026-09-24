module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport

public section

/-! Shared support for the `bv_zero_extend_{ult,eq}_const` rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvZeroExtendUltConstBvsize (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_bvsize) x

def bvZeroExtendUltConstConst (c nm : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv nm) c

def bvZeroExtendUltConstZero (x m : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.zero_extend m) x

def bvZeroExtendUltConstLow (c nm nm2 : Term) : Term :=
  bvExtractTerm (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)

def bvZeroExtendUltConstWidthPrem (x nm2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm2)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvZeroExtendUltConstBvsize x)) (Term.Numeral 1))

def bvZeroExtendUltConstValuePremRefs
    (m cLeft nmLeft nm2 cRight nmRight : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvZeroExtendUltConstConst cLeft nmLeft))
    (bvZeroExtendUltConstZero
      (bvZeroExtendUltConstLow cRight nmRight nm2) m)

def bvZeroExtendUltConstValuePrem
    (_x m c nm nm2 : Term) : Term :=
  bvZeroExtendUltConstValuePremRefs m c nm nm2 c nm

def bvZeroExtendUltConst1Lhs
    (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstZero x m))
    (bvZeroExtendUltConstConst c nm)

def bvZeroExtendUltConst1Rhs
    (x c nm nm2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
    (bvZeroExtendUltConstLow c nm nm2)

def bvZeroExtendUltConst1Term
    (x m c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvZeroExtendUltConst1Lhs x m c nm))
    (bvZeroExtendUltConst1Rhs x c nm nm2)

def bvZeroExtendUltConst2Lhs
    (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstConst c nm))
    (bvZeroExtendUltConstZero x m)

def bvZeroExtendUltConst2Rhs
    (x c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstLow c nm nm2)) x

def bvZeroExtendUltConst2Term
    (x m c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvZeroExtendUltConst2Lhs x m c nm))
    (bvZeroExtendUltConst2Rhs x c nm nm2)

def bvZeroExtendEqConstNmm1Prem (nm nmm1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nmm1)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) nm) (Term.Numeral 1))

def bvZeroExtendEqConstHigh
    (c nm nm2 nmm1 : Term) : Term :=
  bvExtractTerm (bvZeroExtendUltConstConst c nm) nmm1 nm2

def bvZeroExtendEqConstZero (m : Term) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral 0) m

def bvZeroExtendEqConstEq (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b

def bvZeroExtendEqConstAnd (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

def bvZeroExtendEqConstUpper
    (m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendEqConstHigh c nm nm2 nmm1)
    (bvZeroExtendEqConstZero m)

def bvZeroExtendEqConstLower
    (x c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstEq x (bvZeroExtendUltConstLow c nm nm2)

def bvZeroExtendEqConstRhs
    (x m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstAnd
    (bvZeroExtendEqConstUpper m c nm nm2 nmm1)
    (bvZeroExtendEqConstAnd
      (bvZeroExtendEqConstLower x c nm nm2) (Term.Boolean true))

def bvZeroExtendEqConst1Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendUltConstZero x m)
    (bvZeroExtendUltConstConst c nm)

def bvZeroExtendEqConst2Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendUltConstConst c nm)
    (bvZeroExtendUltConstZero x m)

def bvZeroExtendEqConst1Term
    (x m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq (bvZeroExtendEqConst1Lhs x m c nm)
    (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)

def bvZeroExtendEqConst2Term
    (x m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq (bvZeroExtendEqConst2Lhs x m c nm)
    (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)

private theorem eo_typeof_eq_bool_of_ne_stuck_zero_extend_local
    (A B : Term) (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not] at h ⊢
  all_goals
    assumption

private theorem typeof_or_bool_args_zero_extend_local (A B : Term) :
    __eo_typeof_or A B = Term.Bool -> A = Term.Bool ∧ B = Term.Bool := by
  intro h
  cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢

private theorem typeof_or_args_bool_of_ne_stuck_zero_extend_local
    (A B : Term) (h : __eo_typeof_or A B ≠ Term.Stuck) :
    A = Term.Bool ∧ B = Term.Bool := by
  have hBool : __eo_typeof_or A B = Term.Bool := by
    cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢
  exact typeof_or_bool_args_zero_extend_local A B hBool

private theorem mk_apply_bitvec_shape_of_ne_stuck_local
    (width : Term)
    (h : __eo_mk_apply (Term.UOp UserOp.BitVec) width ≠ Term.Stuck) :
    ∃ width',
      __eo_mk_apply (Term.UOp UserOp.BitVec) width =
        Term.Apply (Term.UOp UserOp.BitVec) width' := by
  cases width <;> simp [__eo_mk_apply] at h ⊢

private theorem typeof_zero_extend_result_bitvec_of_ne_stuck_local
    (x m : Term)
    (h : __eo_typeof (bvZeroExtendUltConstZero x m) ≠ Term.Stuck) :
    ∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
  change __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) ≠
    Term.Stuck at h
  change ∃ width,
    __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) =
      Term.Apply (Term.UOp UserOp.BitVec) width
  unfold __eo_typeof_zero_extend at h ⊢
  split at h <;> simp_all [__eo_requires, __eo_mk_apply, native_ite,
    native_teq, native_not]
  exact mk_apply_bitvec_shape_of_ne_stuck_local _ h.2

private theorem typeof_extract_result_bitvec_of_ne_stuck_local
    (x hi lo : Term)
    (h : __eo_typeof (bvExtractTerm x hi lo) ≠ Term.Stuck) :
    ∃ width,
      __eo_typeof (bvExtractTerm x hi lo) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
  change __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
    (__eo_typeof x) ≠ Term.Stuck at h
  change ∃ width,
    __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
      (__eo_typeof x) = Term.Apply (Term.UOp UserOp.BitVec) width
  unfold __eo_typeof_extract at h ⊢
  split at h <;> simp_all [__eo_requires, __eo_mk_apply, native_ite,
    native_teq, native_not]
  exact mk_apply_bitvec_shape_of_ne_stuck_local _ h

private theorem typeof_bvult_arg_types_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_bvult A B ≠ Term.Stuck) :
    ∃ width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A <;> cases B <;> simp [__eo_typeof_bvult] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvult] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvult] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true) Term.Bool ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvult] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem smt_typeof_zero_extend_of_context_local
    (x : Term) (w a : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ->
    native_zleq 0 w = true ->
    native_zleq 0 a = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral a)) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus w a)) := by
  intro hXTy hw0 ha0
  have hRound := native_int_to_nat_roundtrip w hw0
  have hComm : native_zplus a w = native_zplus w a := by
    simp [SmtEval.native_zplus, Int.add_comm]
  change __smtx_typeof
      (SmtTerm.zero_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [typeof_zero_extend_eq, hXTy]
  simp [__smtx_typeof_zero_extend, native_ite, ha0, hRound, hComm]

private theorem bv_zero_extend_ult_const_context_of_types
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    ∃ W A : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes
  rcases hLowTypes with ⟨widthW, hXTy, hLowTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width
      x widthW hXTrans hXTy with
    ⟨W, hWidthW, hW0, hXSmtTy⟩
  subst widthW
  rcases hWideTypes with ⟨widthWide, hZeroTy, hConstTy⟩
  have hSignTy :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.sign_extend m) x) =
        Term.Apply (Term.UOp UserOp.BitVec) widthWide := by
    have hsimpa := hZeroTy
    try simp [bvZeroExtendUltConstZero] at hsimpa ⊢
    exact hsimpa
  rcases sign_extend_index_context x m widthWide W hXTy hSignTy with
    ⟨A, hM, hA0, hWidthWide⟩
  subst m
  subst widthWide
  have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_all_ones_const_context c nm
      (Term.Numeral (native_zplus W A)) hCNe hNmNe
      (by simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using hConstTy) with
    ⟨N, hNm, hWidthN, hN0, hCTy⟩
  have hN : N = native_zplus W A := by
    injection hWidthN with h
    exact h.symm
  subst N
  subst nm
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c (Term.UOp UserOp.Int) (__eo_to_smt c) rfl hCTrans hCTy
  have hConstSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type c (native_zplus W A)
        hCSmtTy hN0
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rw [hLowTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wide, high, low, _hConstEoTy, hNm2, hLow,
      hWide0, hLow0, hHighWide, hExtractWidth0, hConstSmtTy'⟩
  have hLowEq : low = 0 := by
    injection hLow with h
    exact h.symm
  subst low
  have hLowSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) nm2)) =
        SmtType.BitVec
          (native_int_to_nat
            (native_zplus (native_zplus high 1) (native_zneg 0))) := by
    rw [hNm2]
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wide high 0 hConstSmtTy' hWide0 hLow0 hHighWide hExtractWidth0
  have hLowTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) nm2) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLowSmtTyRaw]
    intro h
    cases h
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) nm2)) =
        SmtType.BitVec (native_int_to_nat W) := by
    have h :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) nm2)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2))
        rfl hLowTrans hLowTy
    simpa [__eo_to_smt_type, hW0, native_ite] using h
  have hZeroSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstZero x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvZeroExtendUltConstZero] using
      smt_typeof_zero_extend_of_context_local x W A hXSmtTy hW0 hA0
  exact ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy,
    hConstSmtTy, hLowSmtTy, hZeroSmtTy⟩

private theorem bv_zero_extend_ult_const_1_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    ∃ W A : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstZero x m))
        (__eo_typeof (bvZeroExtendUltConstConst c nm)))
      (__eo_typeof_bvult (__eo_typeof x)
        (__eo_typeof (bvZeroExtendUltConstLow c nm nm2))) =
      Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hWideNe, hLowNe⟩
  exact bv_zero_extend_ult_const_context_of_types x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans
    (typeof_bvult_arg_types_of_ne_stuck_local hWideNe)
    (typeof_bvult_arg_types_of_ne_stuck_local hLowNe)

private theorem bv_zero_extend_ult_const_2_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    ∃ W A : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstConst c nm))
        (__eo_typeof (bvZeroExtendUltConstZero x m)))
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstLow c nm nm2))
        (__eo_typeof x)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hWideNe, hLowNe⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hWideNe with
    ⟨wide, hConstTy, hZeroTy⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hLowNe with
    ⟨low, hLowTy, hXTy⟩
  exact bv_zero_extend_ult_const_context_of_types x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans
    ⟨wide, hZeroTy, hConstTy⟩ ⟨low, hXTy, hLowTy⟩

private theorem smt_typeof_bvult_of_same_bitvec_local
    (a b : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b)) =
      SmtType.Bool := by
  intro hA hB
  change __smtx_typeof (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hA, hB, native_nateq, native_ite]

private theorem typed_bv_zero_extend_ult_const_1_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst1Term x m c nm nm2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_1_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, _hW0, _hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, hZeroSmtTy⟩
  have hLhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstZero x (Term.Numeral A))
    (bvZeroExtendUltConstConst c
      (Term.Numeral (native_zplus W A)))
    (native_int_to_nat (native_zplus W A)) hZeroSmtTy hConstSmtTy
  have hRhsTy := smt_typeof_bvult_of_same_bitvec_local
    x
    (bvZeroExtendUltConstLow c
      (Term.Numeral (native_zplus W A)) nm2)
    (native_int_to_nat W) hXSmtTy hLowSmtTy
  unfold bvZeroExtendUltConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvZeroExtendUltConst1Lhs, bvZeroExtendUltConst1Rhs] using
      hLhsTy.trans hRhsTy.symm)
    (by
      have h :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvult)
                    (bvZeroExtendUltConstZero x (Term.Numeral A)))
                  (bvZeroExtendUltConstConst c
                    (Term.Numeral (native_zplus W A))))) ≠
            SmtType.None := by
        rw [hLhsTy]
        intro h
        cases h
      simpa [bvZeroExtendUltConst1Lhs] using h)

private theorem typed_bv_zero_extend_ult_const_2_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst2Term x m c nm nm2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_2_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, _hW0, _hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, hZeroSmtTy⟩
  have hLhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstConst c
      (Term.Numeral (native_zplus W A)))
    (bvZeroExtendUltConstZero x (Term.Numeral A))
    (native_int_to_nat (native_zplus W A)) hConstSmtTy hZeroSmtTy
  have hRhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstLow c
      (Term.Numeral (native_zplus W A)) nm2) x
    (native_int_to_nat W) hLowSmtTy hXSmtTy
  unfold bvZeroExtendUltConst2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvZeroExtendUltConst2Lhs, bvZeroExtendUltConst2Rhs] using
      hLhsTy.trans hRhsTy.symm)
    (by
      have h :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvult)
                    (bvZeroExtendUltConstConst c
                      (Term.Numeral (native_zplus W A))))
                  (bvZeroExtendUltConstZero x (Term.Numeral A)))) ≠
            SmtType.None := by
        rw [hLhsTy]
        intro h
        cases h
      simpa [bvZeroExtendUltConst2Lhs] using h)

private theorem eval_zero_extend_term_local
    (M : SmtModel) (x : Term) (a : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConstZero x (Term.Numeral a))) =
      __smtx_model_eval_zero_extend (SmtValue.Numeral a)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.zero_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval]

private theorem eval_bvult_term_local
    (M : SmtModel) (x y : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x) y)) =
      __smtx_model_eval_bvult
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  change __smtx_model_eval M
      (SmtTerm.bvult (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_zero_extend_ult_const_both
    (M : SmtModel) (hM : model_wf M)
    (x c nm2 : Term) (W A : native_Int) :
    native_zleq 0 W = true ->
    native_zleq 0 A = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2)) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvZeroExtendUltConstValuePrem x (Term.Numeral A) c
        (Term.Numeral (native_zplus W A)) nm2) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)) ∧
    __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)) := by
  intro hW0 hA0 hXSmtTy hConstSmtTy hLowSmtTy hValuePrem
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    have hW : (0 : Int) ≤ W := by
      simpa [SmtEval.native_zleq] using hW0
    have hA : (0 : Int) ≤ A := by
      simpa [SmtEval.native_zleq] using hA0
    have hsimpa :=
      Int.add_nonneg hW hA
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hWRound := native_int_to_nat_roundtrip W hW0
  have hWideRound :=
    native_int_to_nat_roundtrip (native_zplus W A) hWide0
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x)
      (native_int_to_nat W) hXSmtTy with
    ⟨xPayload, hXEval, _hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary W xPayload := by
    simpa [hWRound] using hXEval
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) nm2))
      (native_int_to_nat W) hLowSmtTy with
    ⟨lowPayload, hLowEval, _hLowCan⟩
  have hLowEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) nm2)) =
        SmtValue.Binary W lowPayload := by
    simpa [hWRound] using hLowEval
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))))
      (native_int_to_nat (native_zplus W A)) hConstSmtTy with
    ⟨constPayload, hConstEval, _hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (native_zplus W A) constPayload := by
    simpa [hWideRound] using hConstEval
  have hZeroXEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstZero x (Term.Numeral A))) =
        SmtValue.Binary (native_zplus W A) xPayload := by
    rw [eval_zero_extend_term_local, hXEval']
    simp [__smtx_model_eval_zero_extend, SmtEval.native_zplus,
      Int.add_comm]
  have hZeroLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstZero
              (bvZeroExtendUltConstLow c
                (Term.Numeral (native_zplus W A)) nm2)
              (Term.Numeral A))) =
        SmtValue.Binary (native_zplus W A) lowPayload := by
    rw [eval_zero_extend_term_local, hLowEval']
    simp [__smtx_model_eval_zero_extend, SmtEval.native_zplus,
      Int.add_comm]
  have hValueRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))))
        (__smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstZero
              (bvZeroExtendUltConstLow c
                (Term.Numeral (native_zplus W A)) nm2)
              (Term.Numeral A)))) := by
    exact RuleProofs.eo_interprets_eq_rel M _ _
      (by have hsimpa := hValuePrem; (try simp [bvZeroExtendUltConstValuePrem] at hsimpa ⊢); exact hsimpa)
  rw [hConstEval', hZeroLowEval] at hValueRel
  have hValueEq :
      SmtValue.Binary (native_zplus W A) constPayload =
        SmtValue.Binary (native_zplus W A) lowPayload :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp hValueRel
  have hPayloadEq : constPayload = lowPayload := by
    injection hValueEq
  constructor
  · unfold bvZeroExtendUltConst1Lhs bvZeroExtendUltConst1Rhs
    rw [eval_bvult_term_local, hZeroXEval, hConstEval',
      eval_bvult_term_local, hXEval', hLowEval', hPayloadEq]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt]
  · unfold bvZeroExtendUltConst2Lhs bvZeroExtendUltConst2Rhs
    rw [eval_bvult_term_local, hConstEval', hZeroXEval,
      eval_bvult_term_local, hLowEval', hXEval', hPayloadEq]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt]

private theorem facts_bv_zero_extend_ult_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstValuePrem x m c nm nm2) true ->
    eo_interprets M (bvZeroExtendUltConst1Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy hValuePrem
  have hBool := typed_bv_zero_extend_ult_const_1_term
    x m c nm nm2 hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_1_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, _hZeroSmtTy⟩
  unfold bvZeroExtendUltConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvZeroExtendUltConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)))
    rw [(eval_bv_zero_extend_ult_const_both M hM x c nm2 W A
      hW0 hA0 hXSmtTy hConstSmtTy hLowSmtTy
      (by simpa using hValuePrem)).1]
    exact RuleProofs.smt_value_rel_refl _

private theorem facts_bv_zero_extend_ult_const_2_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstValuePrem x m c nm nm2) true ->
    eo_interprets M (bvZeroExtendUltConst2Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy hValuePrem
  have hBool := typed_bv_zero_extend_ult_const_2_term
    x m c nm nm2 hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_2_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, _hZeroSmtTy⟩
  unfold bvZeroExtendUltConst2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvZeroExtendUltConst2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)))
    rw [(eval_bv_zero_extend_ult_const_both M hM x c nm2 W A
      hW0 hA0 hXSmtTy hConstSmtTy hLowSmtTy
      (by simpa using hValuePrem)).2]
    exact RuleProofs.smt_value_rel_refl _

def bvZeroExtendUltConst1Program
    (x m c nm nm2 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_ult_const_1 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2)

def bvZeroExtendUltConst2Program
    (x m c nm nm2 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_ult_const_2 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2)

private def bvZeroExtendUltConstGuard
    (x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef
      nm2Ref2 nmRef2 cRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq nm2 nm2Ref1) (__eo_eq x xRef))
              (__eo_eq nm nmRef1))
            (__eo_eq c cRef1))
          (__eo_eq m mRef))
        (__eo_eq nm2 nm2Ref2))
      (__eo_eq nm nmRef2))
    (__eo_eq c cRef2)

private theorem bv_zero_extend_ult_const_guard_refs
    {x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef
      nm2Ref2 nmRef2 cRef2 body : Term} :
    __eo_requires
        (bvZeroExtendUltConstGuard x m c nm nm2 nm2Ref1 xRef
          nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nm2Ref1 = nm2 ∧ xRef = x ∧ nmRef1 = nm ∧ cRef1 = c ∧
      mRef = m ∧ nm2Ref2 = nm2 ∧ nmRef2 = nm ∧ cRef2 = c := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvZeroExtendUltConstGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG7, hC2⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hNm2⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hNm22⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hM⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hC1⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNm1⟩
  rcases bv_extract_support_and_true hG2 with ⟨hNm21, hX⟩
  exact ⟨(bv_extract_support_eq_true hNm21).symm,
    (bv_extract_support_eq_true hX).symm,
    (bv_extract_support_eq_true hNm1).symm,
    (bv_extract_support_eq_true hC1).symm,
    (bv_extract_support_eq_true hM).symm,
    (bv_extract_support_eq_true hNm22).symm,
    (bv_extract_support_eq_true hNm2).symm,
    (bv_extract_support_eq_true hC2).symm⟩

private theorem bv_zero_extend_ult_const_1_premise_shape
    (x m c nm nm2 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst1Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
      P2 = bvZeroExtendUltConstValuePremRefs
        mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2 := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
        P2 = bvZeroExtendUltConstValuePremRefs
          mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_ult_const_1.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 (by
        intro nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2
          hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef,
          nm2Ref2, nmRef2, cRef2, rfl, rfl⟩)

private theorem bv_zero_extend_ult_const_2_premise_shape
    (x m c nm nm2 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst2Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
      P2 = bvZeroExtendUltConstValuePremRefs
        mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2 := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
        P2 = bvZeroExtendUltConstValuePremRefs
          mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_ult_const_2.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 (by
        intro nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2
          hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef,
          nm2Ref2, nmRef2, cRef2, rfl, rfl⟩)

private theorem bv_zero_extend_ult_const_1_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst1Program x m c nm nm2
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendUltConstValuePrem x m c nm nm2) =
      bvZeroExtendUltConst1Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvZeroExtendUltConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePrem bvZeroExtendUltConstValuePremRefs
    bvZeroExtendUltConstBvsize bvZeroExtendUltConstZero
    bvZeroExtendUltConstLow bvZeroExtendUltConstConst bvExtractTerm
  rw [__eo_prog_bv_zero_extend_ult_const_1.eq_6
    x m c nm nm2 nm2 x nm c m nm2 nm c hX hM hC hNm hNm2]
  simp [bvZeroExtendUltConstGuard, bvZeroExtendUltConst1Term,
    bvZeroExtendUltConst1Lhs, bvZeroExtendUltConst1Rhs,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bv_zero_extend_ult_const_2_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst2Program x m c nm nm2
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendUltConstValuePrem x m c nm nm2) =
      bvZeroExtendUltConst2Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvZeroExtendUltConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePrem bvZeroExtendUltConstValuePremRefs
    bvZeroExtendUltConstBvsize bvZeroExtendUltConstZero
    bvZeroExtendUltConstLow bvZeroExtendUltConstConst bvExtractTerm
  rw [__eo_prog_bv_zero_extend_ult_const_2.eq_6
    x m c nm nm2 nm2 x nm c m nm2 nm c hX hM hC hNm hNm2]
  simp [bvZeroExtendUltConstGuard, bvZeroExtendUltConst2Term,
    bvZeroExtendUltConst2Lhs, bvZeroExtendUltConst2Rhs,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bvZeroExtendUltConst1Program_normalize
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvZeroExtendUltConst1Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 ∧
      bvZeroExtendUltConst1Program x m c nm nm2 P1 P2 =
        bvZeroExtendUltConst1Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_zero_extend_ult_const_1_premise_shape
      x m c nm nm2 P1 P2 hX hM hC hNm hNm2 hProg with
    ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef, nm2Ref2, nmRef2,
      cRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendUltConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePremRefs bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstZero bvZeroExtendUltConstLow
    bvZeroExtendUltConstConst bvExtractTerm at hReq
  rw [__eo_prog_bv_zero_extend_ult_const_1.eq_6
    x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2
    nmRef2 cRef2 hX hM hC hNm hNm2] at hReq
  rcases bv_zero_extend_ult_const_guard_refs
      (by simpa [bvZeroExtendUltConstGuard] using hReq) with
    ⟨hNm2Ref1, hXRef, hNmRef1, hCRef1, hMRef, hNm2Ref2,
      hNmRef2, hCRef2⟩
  subst nm2Ref1
  subst xRef
  subst nmRef1
  subst cRef1
  subst mRef
  subst nm2Ref2
  subst nmRef2
  subst cRef2
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := by
    simpa using hP1
  have hP2Canonical :
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 := by
    simpa [bvZeroExtendUltConstValuePrem] using hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_ult_const_1_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

private theorem bvZeroExtendUltConst2Program_normalize
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvZeroExtendUltConst2Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 ∧
      bvZeroExtendUltConst2Program x m c nm nm2 P1 P2 =
        bvZeroExtendUltConst2Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_zero_extend_ult_const_2_premise_shape
      x m c nm nm2 P1 P2 hX hM hC hNm hNm2 hProg with
    ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef, nm2Ref2, nmRef2,
      cRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendUltConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePremRefs bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstZero bvZeroExtendUltConstLow
    bvZeroExtendUltConstConst bvExtractTerm at hReq
  rw [__eo_prog_bv_zero_extend_ult_const_2.eq_6
    x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2
    nmRef2 cRef2 hX hM hC hNm hNm2] at hReq
  rcases bv_zero_extend_ult_const_guard_refs
      (by simpa [bvZeroExtendUltConstGuard] using hReq) with
    ⟨hNm2Ref1, hXRef, hNmRef1, hCRef1, hMRef, hNm2Ref2,
      hNmRef2, hCRef2⟩
  subst nm2Ref1
  subst xRef
  subst nmRef1
  subst cRef1
  subst mRef
  subst nm2Ref2
  subst nmRef2
  subst cRef2
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := by
    simpa using hP1
  have hP2Canonical :
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 := by
    simpa [bvZeroExtendUltConstValuePrem] using hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_ult_const_2_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

theorem typed_bv_zero_extend_ult_const_1_program
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst1Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_ult_const_1_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem typed_bv_zero_extend_ult_const_2_program
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst2Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_ult_const_2_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_zero_extend_ult_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    _hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst1Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hValuePrem :
      eo_interprets M
        (bvZeroExtendUltConstValuePrem x m c nm nm2) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_ult_const_1_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy hValuePrem

theorem facts_bv_zero_extend_ult_const_2_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    _hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst2Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hValuePrem :
      eo_interprets M
        (bvZeroExtendUltConstValuePrem x m c nm nm2) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_ult_const_2_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy hValuePrem

private theorem bv_zero_extend_eq_const_rhs_types
    (x m c nm nm2 nmm1 : Term) :
    __eo_typeof (bvZeroExtendEqConstRhs x m c nm nm2 nmm1) ≠
      Term.Stuck ->
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvZeroExtendEqConstLower x c nm nm2) = Term.Bool := by
  intro hRhsNe
  change __eo_typeof_or
      (__eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1))
      (__eo_typeof
        (bvZeroExtendEqConstAnd
          (bvZeroExtendEqConstLower x c nm nm2) (Term.Boolean true))) ≠
    Term.Stuck at hRhsNe
  rcases typeof_or_args_bool_of_ne_stuck_zero_extend_local _ _ hRhsNe with
    ⟨hUpperTy, hTailTy⟩
  have hTailTy' :
      __eo_typeof_or
          (__eo_typeof (bvZeroExtendEqConstLower x c nm nm2))
          Term.Bool = Term.Bool := by
    have hsimpa := hTailTy
    try simp [bvZeroExtendEqConstAnd] at hsimpa ⊢
    exact hsimpa
  exact ⟨hUpperTy,
    (typeof_or_bool_args_zero_extend_local _ _ hTailTy').1⟩

private theorem bv_zero_extend_eq_const_1_type_parts
    (x m c nm nm2 nmm1 : Term) :
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvZeroExtendEqConst1Lhs x m c nm))
      (__eo_typeof (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvZeroExtendUltConstZero x m))
          (__eo_typeof (bvZeroExtendUltConstConst c nm)) ≠ Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvZeroExtendEqConst1Lhs, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_zero_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.1 with ⟨wide, hZeroTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.symm.trans hZeroTy
  rcases bv_zero_extend_eq_const_rhs_types x m c nm nm2 nmm1 hRhsNe with
    ⟨hUpperTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    have hsimpa := hLowerTy
    try simp [bvZeroExtendEqConstLower, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hZeroTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperTy⟩

private theorem bv_zero_extend_eq_const_2_type_parts
    (x m c nm nm2 nmm1 : Term) :
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvZeroExtendEqConst2Lhs x m c nm))
      (__eo_typeof (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvZeroExtendUltConstConst c nm))
          (__eo_typeof (bvZeroExtendUltConstZero x m)) ≠ Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvZeroExtendEqConst2Lhs, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_zero_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.2 with ⟨wide, hZeroTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.trans hZeroTy
  rcases bv_zero_extend_eq_const_rhs_types x m c nm nm2 nmm1 hRhsNe with
    ⟨hUpperTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    have hsimpa := hLowerTy
    try simp [bvZeroExtendEqConstLower, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hZeroTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperTy⟩

private theorem bv_zero_extend_eq_const_context_of_types
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = A ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvZeroExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat A) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendEqConstZero m)) =
        SmtType.BitVec (native_int_to_nat A) := by
  intro hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes hUpperTy
  have hBase := bv_zero_extend_ult_const_context_of_types x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes
  rcases hBase with
    ⟨W, A, hM, hNm, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, hZeroSmtTy⟩
  subst m
  subst nm
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  rcases hLowTypes with ⟨_lowWidth, _hXEoTy, hLowEoTy⟩
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rw [hLowEoTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wideLow, L, lowIndex, _hConstEoTyLow, hNm2, hLowIndex,
      hWideLow0, hLowIndex0, hLWide, hDLow0, hConstSmtTyLow⟩
  have hLowIndexEq : lowIndex = 0 := by
    injection hLowIndex with h
    exact h.symm
  subst lowIndex
  subst nm2
  let dLow := native_zplus (native_zplus L 1) (native_zneg 0)
  have hLowSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtType.BitVec (native_int_to_nat dLow) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideLow L 0 hConstSmtTyLow hWideLow0 hLowIndex0 hLWide hDLow0
  have hDLowNat : native_int_to_nat dLow = native_int_to_nat W := by
    rw [hLowSmtTyRaw] at hLowSmtTy
    injection hLowSmtTy
  have hDLowEq : dLow = W :=
    nonneg_int_eq_of_toNat_eq dLow W
      (native_zleq_of_zlt_true _ _ hDLow0) hW0 hDLowNat
  have hLWidth : native_zplus L 1 = W := by
    simpa [dLow, SmtEval.native_zplus, SmtEval.native_zneg] using hDLowEq
  have hUpperTy' :
      __eo_typeof_eq
          (__eo_typeof
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L) nmm1))
          (__eo_typeof
            (bvZeroExtendEqConstZero (Term.Numeral A))) = Term.Bool := by
    have hsimpa := hUpperTy
    try simp [bvZeroExtendEqConstUpper, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hUpperSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hUpperTy'
  have hUpperTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hUpperTy'
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nmm1 (Term.Numeral L) hConstTrans hUpperSides.1 with
    ⟨wideHigh, H, lowHigh, _hConstEoTyHigh, hNmm1, hLowHigh,
      hWideHigh0, hLowHigh0, hHWide, hDHigh0, hConstSmtTyHigh⟩
  have hLowHighEq : lowHigh = L := by
    injection hLowHigh with h
    exact h.symm
  subst lowHigh
  subst nmm1
  let dHigh := native_zplus (native_zplus H 1) (native_zneg L)
  have hHighSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat dHigh) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideHigh H L hConstSmtTyHigh hWideHigh0 hLowHigh0 hHWide hDHigh0
  have hHighTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hHighSmtTyRaw]
    intro h
    cases h
  have hZeroASmtTy :
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendEqConstZero (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat A) := by
    simpa [bvZeroExtendEqConstZero, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type (Term.Numeral 0) A rfl hA0
  have hZeroATrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendEqConstZero (Term.Numeral A)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hZeroASmtTy]
    intro h
    cases h
  have hHighBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvZeroExtendEqConstHigh c
        (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H))
      (__eo_typeof
        (bvZeroExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)))
      (__eo_to_smt
        (bvZeroExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))) rfl hHighTrans rfl
  have hZeroABridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvZeroExtendEqConstZero (Term.Numeral A))
      (__eo_typeof (bvZeroExtendEqConstZero (Term.Numeral A)))
      (__eo_to_smt (bvZeroExtendEqConstZero (Term.Numeral A)))
      rfl hZeroATrans rfl
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat A) := by
    calc
      _ = __eo_to_smt_type
          (__eo_typeof
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) := hHighBridge
      _ = __eo_to_smt_type
          (__eo_typeof (bvZeroExtendEqConstZero (Term.Numeral A))) := by
            rw [hUpperTypes]
      _ = __smtx_typeof
          (__eo_to_smt (bvZeroExtendEqConstZero (Term.Numeral A))) :=
            hZeroABridge.symm
      _ = SmtType.BitVec (native_int_to_nat A) := hZeroASmtTy
  have hDHighNat : native_int_to_nat dHigh = native_int_to_nat A := by
    rw [hHighSmtTyRaw] at hHighSmtTy
    injection hHighSmtTy
  have hDHighEq : dHigh = A :=
    nonneg_int_eq_of_toNat_eq dHigh A
      (native_zleq_of_zlt_true _ _ hDHigh0) hA0 hDHighNat
  have hHWidth :
      native_zplus (native_zplus H 1) (native_zneg L) = A := by
    simpa [dHigh] using hDHighEq
  exact ⟨W, A, L, H, rfl, rfl, rfl, rfl, hW0, hA0, hLWidth,
    hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy, hZeroSmtTy,
    hHighSmtTy, hZeroASmtTy⟩

private theorem bv_zero_extend_eq_const_1_context
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = A ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvZeroExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat A) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendEqConstZero m)) =
        SmtType.BitVec (native_int_to_nat A) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_1_type_parts x m c nm nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpper⟩
  exact bv_zero_extend_eq_const_context_of_types x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hWide hLow hUpper

private theorem bv_zero_extend_eq_const_2_context
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = A ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvZeroExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat A) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendEqConstZero m)) =
        SmtType.BitVec (native_int_to_nat A) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_2_type_parts x m c nm nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpper⟩
  exact bv_zero_extend_eq_const_context_of_types x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hWide hLow hUpper

private theorem typed_bv_zero_extend_eq_const_1_term
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_1_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, _hLWidth,
      _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy, hZeroSmtTy,
      hHighSmtTy, hZeroASmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConst1Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvZeroExtendEqConst1Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hZeroSmtTy.trans hConstSmtTy.symm)
      (by rw [hZeroSmtTy]; intro h; cases h)
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstUpper (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstUpper bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroASmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvZeroExtendEqConstLower bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvZeroExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLowerBool
      RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hUpperBool hTailBool
  unfold bvZeroExtendEqConst1Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem typed_bv_zero_extend_eq_const_2_term
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_2_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, _hLWidth,
      _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy, hZeroSmtTy,
      hHighSmtTy, hZeroASmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConst2Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvZeroExtendEqConst2Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hConstSmtTy.trans hZeroSmtTy.symm)
      (by rw [hConstSmtTy]; intro h; cases h)
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstUpper (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstUpper bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroASmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvZeroExtendEqConstLower bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvZeroExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLowerBool
      RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hUpperBool hTailBool
  unfold bvZeroExtendEqConst2Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem bv_zero_extend_eq_const_nmm1_numeric
    (M : SmtModel) (N H : native_Int) :
    eo_interprets M
      (bvZeroExtendEqConstNmm1Prem (Term.Numeral N) (Term.Numeral H))
      true ->
    H = native_zplus N (native_zneg 1) := by
  intro hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral H)
            (SmtTerm.neg (SmtTerm.Numeral N) (SmtTerm.Numeral 1))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq] at hEval
      simpa [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval__, native_veq] using hEval

/--
The generated rule's low extraction forces `L + 1 = W`, while its upper
extraction has width `H + 1 - L = A`.  The second premise fixes
`H = W + A - 1`, making the upper extraction one bit too wide.  Thus a
well-typed result cannot coexist with true premises.
-/
private theorem bv_zero_extend_eq_const_widths_false
    (W A L H : Int)
    (hLWidth : L + 1 = W)
    (hHWidth : H + 1 + -L = A)
    (hNmm1 : H = W + A + -1) : False := by
  omega

private theorem facts_bv_zero_extend_eq_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy _hP1True hP2True
  rcases bv_zero_extend_eq_const_1_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, hLWidth,
      hHWidth, _hXSmtTy, _hConstSmtTy, _hLowSmtTy, _hZeroSmtTy,
      _hHighSmtTy, _hZeroASmtTy⟩
  have hNmm1 := bv_zero_extend_eq_const_nmm1_numeric M
    (native_zplus W A) H hP2True
  simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hLWidth hHWidth hNmm1
  exact False.elim
    (bv_zero_extend_eq_const_widths_false W A L H hLWidth hHWidth hNmm1)

private theorem facts_bv_zero_extend_eq_const_2_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy _hP1True hP2True
  rcases bv_zero_extend_eq_const_2_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, hLWidth,
      hHWidth, _hXSmtTy, _hConstSmtTy, _hLowSmtTy, _hZeroSmtTy,
      _hHighSmtTy, _hZeroASmtTy⟩
  have hNmm1 := bv_zero_extend_eq_const_nmm1_numeric M
    (native_zplus W A) H hP2True
  simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hLWidth hHWidth hNmm1
  exact False.elim
    (bv_zero_extend_eq_const_widths_false W A L H hLWidth hHWidth hNmm1)

def bvZeroExtendEqConst1Program
    (x m c nm nm2 nmm1 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_eq_const_1 x m c nm nm2 nmm1
    (Proof.pf P1) (Proof.pf P2)

def bvZeroExtendEqConst2Program
    (x m c nm nm2 nmm1 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_eq_const_2 x m c nm nm2 nmm1
    (Proof.pf P1) (Proof.pf P2)

private def bvZeroExtendEqConstGuard
    (x nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and (__eo_eq nm2 nm2Ref) (__eo_eq x xRef))
      (__eo_eq nmm1 nmm1Ref))
    (__eo_eq nm nmRef)

private theorem bv_zero_extend_eq_const_guard_refs
    {x nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef body : Term} :
    __eo_requires
        (bvZeroExtendEqConstGuard x nm nm2 nmm1 nm2Ref xRef
          nmm1Ref nmRef)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nm2Ref = nm2 ∧ xRef = x ∧ nmm1Ref = nmm1 ∧ nmRef = nm := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvZeroExtendEqConstGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG3, hNm⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNmm1⟩
  rcases bv_extract_support_and_true hG2 with ⟨hNm2, hX⟩
  exact ⟨(bv_extract_support_eq_true hNm2).symm,
    (bv_extract_support_eq_true hX).symm,
    (bv_extract_support_eq_true hNmm1).symm,
    (bv_extract_support_eq_true hNm).symm⟩

private theorem bv_zero_extend_eq_const_1_premise_shape
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    ∃ nm2Ref xRef nmm1Ref nmRef,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ nm2Ref xRef nmm1Ref nmRef,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_eq_const_1.eq_8
      x m c nm nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 hNmm1 (by
        intro nm2Ref xRef nmm1Ref nmRef hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl⟩)

private theorem bv_zero_extend_eq_const_2_premise_shape
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    ∃ nm2Ref xRef nmm1Ref nmRef,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ nm2Ref xRef nmm1Ref nmRef,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_eq_const_2.eq_8
      x m c nm nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 hNmm1 (by
        intro nm2Ref xRef nmm1Ref nmRef hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl⟩)

private theorem bv_zero_extend_eq_const_1_program_canonical
    (x m c nm nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst1Program x m c nm nm2 nmm1
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvZeroExtendEqConst1Term x m c nm nm2 nmm1 := by
  intro hX hM hC hNm hNm2 hNmm1
  unfold bvZeroExtendEqConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_zero_extend_eq_const_1.eq_7
    x m c nm nm2 nmm1 nm2 x nmm1 nm hX hM hC hNm hNm2 hNmm1]
  simp [bvZeroExtendEqConstGuard, bvZeroExtendEqConst1Term,
    bvZeroExtendEqConst1Lhs, bvZeroExtendEqConstRhs,
    bvZeroExtendEqConstUpper, bvZeroExtendEqConstLower,
    bvZeroExtendEqConstEq, bvZeroExtendEqConstAnd,
    bvZeroExtendEqConstHigh, bvZeroExtendEqConstZero,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2, hNmm1]

private theorem bv_zero_extend_eq_const_2_program_canonical
    (x m c nm nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst2Program x m c nm nm2 nmm1
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvZeroExtendEqConst2Term x m c nm nm2 nmm1 := by
  intro hX hM hC hNm hNm2 hNmm1
  unfold bvZeroExtendEqConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_zero_extend_eq_const_2.eq_7
    x m c nm nm2 nmm1 nm2 x nmm1 nm hX hM hC hNm hNm2 hNmm1]
  simp [bvZeroExtendEqConstGuard, bvZeroExtendEqConst2Term,
    bvZeroExtendEqConst2Lhs, bvZeroExtendEqConstRhs,
    bvZeroExtendEqConstUpper, bvZeroExtendEqConstLower,
    bvZeroExtendEqConstEq, bvZeroExtendEqConstAnd,
    bvZeroExtendEqConstHigh, bvZeroExtendEqConstZero,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2, hNmm1]

private theorem bvZeroExtendEqConst1Program_normalize
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2 =
        bvZeroExtendEqConst1Term x m c nm nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_zero_extend_eq_const_1_premise_shape
      x m c nm nm2 nmm1 P1 P2 hX hM hC hNm hNm2 hNmm1 hProg with
    ⟨nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendEqConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_zero_extend_eq_const_1.eq_7
    x m c nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hNm2 hNmm1] at hReq
  rcases bv_zero_extend_eq_const_guard_refs
      (by simpa [bvZeroExtendEqConstGuard] using hReq) with
    ⟨hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := hP1
  have hP2Canonical : P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_eq_const_1_program_canonical
    x m c nm nm2 nmm1 hX hM hC hNm hNm2 hNmm1

private theorem bvZeroExtendEqConst2Program_normalize
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2 =
        bvZeroExtendEqConst2Term x m c nm nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_zero_extend_eq_const_2_premise_shape
      x m c nm nm2 nmm1 P1 P2 hX hM hC hNm hNm2 hNmm1 hProg with
    ⟨nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendEqConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_zero_extend_eq_const_2.eq_7
    x m c nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hNm2 hNmm1] at hReq
  rcases bv_zero_extend_eq_const_guard_refs
      (by simpa [bvZeroExtendEqConstGuard] using hReq) with
    ⟨hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := hP1
  have hP2Canonical : P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_eq_const_2_program_canonical
    x m c nm nm2 nmm1 hX hM hC hNm hNm2 hNmm1

theorem typed_bv_zero_extend_eq_const_1_program
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst1Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_eq_const_1_term x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem typed_bv_zero_extend_eq_const_2_program
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst2Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_eq_const_2_term x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_zero_extend_eq_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst1Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP1] using hP1True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_eq_const_1_term M hM x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy hWidthPrem hNmm1Prem

theorem facts_bv_zero_extend_eq_const_2_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst2Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP1] using hP1True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_eq_const_2_term M hM x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy hWidthPrem hNmm1Prem

/-! Support for the `bv_sign_extend_eq_const` rewrites. -/

def bvSignExtendEqConstMpPrem (m mp : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) mp)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) m)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0)))

def bvSignExtendEqConstSign (x m : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend m) x

def bvSignExtendEqConstZero (mp : Term) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral 0) mp

def bvSignExtendEqConstNotZero (mp : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) (bvSignExtendEqConstZero mp)

def bvSignExtendEqConstOr (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b

def bvSignExtendEqConstHigh
    (c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstHigh c nm nm2 nmm1

def bvSignExtendEqConstUpperZero
    (mp c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConstHigh c nm nm2 nmm1)
    (bvSignExtendEqConstZero mp)

def bvSignExtendEqConstUpperOnes
    (mp c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConstHigh c nm nm2 nmm1)
    (bvSignExtendEqConstNotZero mp)

def bvSignExtendEqConstUpper
    (mp c nm nm2 nmm1 : Term) : Term :=
  bvSignExtendEqConstOr
    (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1)
    (bvSignExtendEqConstOr
      (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1)
      (Term.Boolean false))

def bvSignExtendEqConstLower
    (x c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstLower x c nm nm2

def bvSignExtendEqConstRhs
    (x m c nm mp nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstAnd
    (bvSignExtendEqConstUpper mp c nm nm2 nmm1)
    (bvZeroExtendEqConstAnd
      (bvSignExtendEqConstLower x c nm nm2) (Term.Boolean true))

def bvSignExtendEqConst1Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConstSign x m)
    (bvZeroExtendUltConstConst c nm)

def bvSignExtendEqConst2Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendUltConstConst c nm)
    (bvSignExtendEqConstSign x m)

def bvSignExtendEqConst1Term
    (x m c nm mp nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConst1Lhs x m c nm)
    (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)

def bvSignExtendEqConst2Term
    (x m c nm mp nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConst2Lhs x m c nm)
    (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)

private theorem signExtend_eq_iff_low_upper
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W) :
    x.signExtend (W + A) = c ↔
      x = c.extractLsb' 0 W ∧
        (c.extractLsb' (W - 1) (A + 1) = 0#(A + 1) ∨
          c.extractLsb' (W - 1) (A + 1) = BitVec.allOnes (A + 1)) := by
  constructor
  · intro h
    subst c
    constructor
    · apply BitVec.eq_of_getElem_eq
      intro i hi
      rw [BitVec.getElem_extractLsb' hi,
        BitVec.getLsbD_eq_getElem (by omega),
        BitVec.getElem_signExtend (by omega)]
      simp [hi]
    · cases hx : x.msb
      · left
        apply BitVec.eq_of_getElem_eq
        intro i hi
        rw [BitVec.getElem_extractLsb' hi,
          BitVec.getLsbD_eq_getElem (by omega),
          BitVec.getElem_signExtend (by omega)]
        simp [BitVec.getElem_zero, hx]
        intro h
        have hi0 : i = 0 := by omega
        subst i
        have hsimpa := hx
        try simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega)] at hsimpa ⊢
        exact hsimpa
      · right
        apply BitVec.eq_of_getElem_eq
        intro i hi
        rw [BitVec.getElem_extractLsb' hi,
          BitVec.getLsbD_eq_getElem (by omega),
          BitVec.getElem_signExtend (by omega)]
        simp [BitVec.getElem_allOnes, hx]
        intro h
        have hi0 : i = 0 := by omega
        subst i
        have hsimpa := hx
        try simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_eq_getElem (by omega)] at hsimpa ⊢
        exact hsimpa
  · rintro ⟨hLow, hUpper⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [BitVec.getElem_signExtend hi]
    split
    · rename_i hiW
      have hBit := congrArg (fun z : BitVec W => z[i]) hLow
      have hsimpa := hBit
      try simp [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem hiW] at hsimpa ⊢
      exact hsimpa
    · rename_i hiW
      have hIdx : i - (W - 1) < A + 1 := by omega
      have hFull : W - 1 + (i - (W - 1)) = i := by omega
      rcases hUpper with hZero | hOnes
      · have hUpperBit := congrArg
            (fun z : BitVec (A + 1) => z[i - (W - 1)]'hIdx) hZero
        have hMsbIdx : W - 1 < W := by omega
        have hCMsbIdx : W - 1 < W + A := by omega
        have hLowMsb := congrArg
          (fun z : BitVec W => z[W - 1]'hMsbIdx) hLow
        have hCMsb : c[W - 1] = x.msb := by
          calc
            c[W - 1] = c.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hCMsbIdx).symm
            _ = x[W - 1] := by
              simpa [BitVec.getElem_extractLsb'] using hLowMsb.symm
            _ = x.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hMsbIdx).symm
            _ = x.msb := (BitVec.msb_eq_getLsbD_last x).symm
        have hCi : c[i] = false := by
          simpa [BitVec.getElem_extractLsb', hFull,
            BitVec.getLsbD_eq_getElem hi, BitVec.getElem_zero] using hUpperBit
        have hCBase : c[W - 1] = false := by
          have hBaseIdx : (0 : Nat) < A + 1 := by omega
          have hBase := congrArg
            (fun z : BitVec (A + 1) => z[0]'hBaseIdx) hZero
          have hsimpa := hBase
          try simp [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem hMsbIdx, BitVec.getElem_zero] at hsimpa ⊢
          exact hsimpa
        rw [hCMsb] at hCBase
        rw [hCBase, hCi]
      · have hUpperBit := congrArg
            (fun z : BitVec (A + 1) => z[i - (W - 1)]'hIdx) hOnes
        have hMsbIdx : W - 1 < W := by omega
        have hCMsbIdx : W - 1 < W + A := by omega
        have hLowMsb := congrArg
          (fun z : BitVec W => z[W - 1]'hMsbIdx) hLow
        have hCMsb : c[W - 1] = x.msb := by
          calc
            c[W - 1] = c.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hCMsbIdx).symm
            _ = x[W - 1] := by
              simpa [BitVec.getElem_extractLsb'] using hLowMsb.symm
            _ = x.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hMsbIdx).symm
            _ = x.msb := (BitVec.msb_eq_getLsbD_last x).symm
        have hCi : c[i] = true := by
          simpa [BitVec.getElem_extractLsb', hFull,
            BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes] using hUpperBit
        have hCBase : c[W - 1] = true := by
          have hBaseIdx : (0 : Nat) < A + 1 := by omega
          have hBase := congrArg
            (fun z : BitVec (A + 1) => z[0]'hBaseIdx) hOnes
          have hsimpa := hBase
          try simp [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem hMsbIdx, BitVec.getElem_allOnes] at hsimpa ⊢
          exact hsimpa
        rw [hCMsb] at hCBase
        rw [hCBase, hCi]

private theorem smt_eval_eq_bitvec_values (x y : BitVec W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int) (↑y.toNat : Int)) =
      SmtValue.Boolean (decide (x = y)) := by
  simp only [__smtx_model_eval_eq, native_veq]
  congr 1
  simp only [decide_eq_decide]
  constructor
  · intro h
    injection h with _ hp
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast hp
  · intro h
    subst y
    rfl

private theorem smt_eval_bvnot_zero_value (W : Nat) :
    __smtx_model_eval_bvnot (SmtValue.Binary (↑W : Int) 0) =
      SmtValue.Binary (↑W : Int) (↑(BitVec.allOnes W).toNat : Int) := by
  have hPowPos : (0 : Int) < (2 : Int) ^ W := by
    exact_mod_cast Nat.two_pow_pos W
  have hLower : 0 ≤ (2 : Int) ^ W - 1 := by omega
  have hUpper : (2 : Int) ^ W - 1 < (2 : Int) ^ W := by omega
  have hMod : ((2 : Int) ^ W - 1) % (2 : Int) ^ W =
      (2 : Int) ^ W - 1 :=
    Int.emod_eq_of_lt hLower hUpper
  simp only [__smtx_model_eval_bvnot, native_mod_total, native_binary_not,
    native_zplus, native_zneg, BitVec.toNat_allOnes]
  rw [natpow2_eq W]
  rw [show (2 : Int) ^ W + -(0 + 1) = (2 : Int) ^ W - 1 by omega]
  rw [hMod]
  congr 2
  exact (Int.ofNat_sub Nat.one_le_two_pow).symm

private theorem eval_sign_extend_eq_characterization
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑(W + A) : Int)
          (↑(x.signExtend (W + A)).toNat : Int))
        (SmtValue.Binary (↑(W + A) : Int) (↑c.toNat : Int)) =
      __smtx_model_eval_and
        (__smtx_model_eval_or
          (__smtx_model_eval_eq
            (SmtValue.Binary (↑(A + 1) : Int)
              (↑(c.extractLsb' (W - 1) (A + 1)).toNat : Int))
            (SmtValue.Binary (↑(A + 1) : Int)
              (↑(0#(A + 1)).toNat : Int)))
          (__smtx_model_eval_or
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑(A + 1) : Int)
                (↑(c.extractLsb' (W - 1) (A + 1)).toNat : Int))
              (__smtx_model_eval_bvnot
                (SmtValue.Binary (↑(A + 1) : Int) 0)))
            (SmtValue.Boolean false)))
        (__smtx_model_eval_and
          (__smtx_model_eval_eq
            (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
            (SmtValue.Binary (↑W : Int)
              (↑(c.extractLsb' 0 W).toNat : Int)))
          (SmtValue.Boolean true)) := by
  rw [smt_eval_eq_bitvec_values,
    smt_eval_eq_bitvec_values,
    smt_eval_bvnot_zero_value,
    smt_eval_eq_bitvec_values,
    smt_eval_eq_bitvec_values]
  simp only [__smtx_model_eval_or, __smtx_model_eval_and,
    native_or, native_and]
  have hIff :
    (x.signExtend (W + A) = c) ↔
      x = c.extractLsb' 0 W ∧
        (c.extractLsb' (W - 1) (A + 1) = 0#(A + 1) ∨
          c.extractLsb' (W - 1) (A + 1) = BitVec.allOnes (A + 1))
      := signExtend_eq_iff_low_upper x c hW
  by_cases hLow : x = c.extractLsb' 0 W
  · by_cases hZero :
        c.extractLsb' (W - 1) (A + 1) = 0#(A + 1)
    · have hSign : x.signExtend (W + A) = c :=
        hIff.mpr ⟨hLow, Or.inl hZero⟩
      have hSign' : (c.extractLsb' 0 W).signExtend (W + A) = c := by
        simpa [hLow] using hSign
      simp [hLow, hZero, hSign']
    · by_cases hOnes :
          c.extractLsb' (W - 1) (A + 1) = BitVec.allOnes (A + 1)
      · have hSign : x.signExtend (W + A) = c :=
          hIff.mpr ⟨hLow, Or.inr hOnes⟩
        have hSign' : (c.extractLsb' 0 W).signExtend (W + A) = c := by
          simpa [hLow] using hSign
        simp [hLow, hOnes, hSign']
      · have hSign : x.signExtend (W + A) ≠ c := by
          intro h
          rcases (hIff.mp h).2 with hUpper | hUpper
          · exact hZero hUpper
          · exact hOnes hUpper
        have hSign' :
            (c.extractLsb' 0 W).signExtend (W + A) ≠ c := by
          simpa [hLow] using hSign
        simp [hLow, hZero, hOnes, hSign']
  · have hSign : x.signExtend (W + A) ≠ c := by
      intro h
      exact hLow (hIff.mp h).1
    simp [hLow, hSign]

private theorem typeof_sign_extend_result_bitvec_of_ne_stuck_local
    (x m : Term)
    (h : __eo_typeof (bvSignExtendEqConstSign x m) ≠ Term.Stuck) :
    ∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
  change __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) ≠
    Term.Stuck at h
  change ∃ width,
    __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) =
      Term.Apply (Term.UOp UserOp.BitVec) width
  unfold __eo_typeof_zero_extend at h ⊢
  split at h <;> simp_all [__eo_requires, __eo_mk_apply, native_ite,
    native_teq, native_not]
  exact mk_apply_bitvec_shape_of_ne_stuck_local _ h.2

private theorem smt_typeof_bvnot_same_local
    (a : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvnot a) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro ha
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, ha]

private theorem eo_has_bool_type_or_of_bool_args_local (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [hA, hB, native_ite, native_Teq]

private theorem eo_has_bool_type_false_local :
    RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  unfold RuleProofs.eo_has_bool_type
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem bv_sign_extend_eq_const_rhs_types
    (x m c nm mp nm2 nmm1 : Term) :
    __eo_typeof (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1) ≠
      Term.Stuck ->
    __eo_typeof (bvSignExtendEqConstUpper mp c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvSignExtendEqConstLower x c nm nm2) = Term.Bool := by
  intro hRhsNe
  change __eo_typeof_or
      (__eo_typeof (bvSignExtendEqConstUpper mp c nm nm2 nmm1))
      (__eo_typeof
        (bvZeroExtendEqConstAnd
          (bvSignExtendEqConstLower x c nm nm2) (Term.Boolean true))) ≠
    Term.Stuck at hRhsNe
  rcases typeof_or_args_bool_of_ne_stuck_zero_extend_local _ _ hRhsNe with
    ⟨hUpperTy, hTailTy⟩
  have hTailTy' :
      __eo_typeof_or
          (__eo_typeof (bvSignExtendEqConstLower x c nm nm2))
          Term.Bool = Term.Bool := by
    have hsimpa := hTailTy
    try simp [bvZeroExtendEqConstAnd] at hsimpa ⊢
    exact hsimpa
  have hLowerTy := (typeof_or_bool_args_zero_extend_local _ _ hTailTy').1
  have hUpperTy' :
      __eo_typeof_or
          (__eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1))
          (__eo_typeof
            (bvSignExtendEqConstOr
              (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1)
              (Term.Boolean false))) = Term.Bool := by
    have hsimpa := hUpperTy
    try simp [bvSignExtendEqConstUpper, bvSignExtendEqConstOr] at hsimpa ⊢
    exact hsimpa
  rcases typeof_or_bool_args_zero_extend_local _ _ hUpperTy' with
    ⟨hUpperZeroTy, hUpperTailTy⟩
  have hUpperTailTy' :
      __eo_typeof_or
          (__eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1))
          Term.Bool = Term.Bool := by
    have hsimpa := hUpperTailTy
    try simp [bvSignExtendEqConstOr] at hsimpa ⊢
    exact hsimpa
  have hUpperOnesTy :=
    (typeof_or_bool_args_zero_extend_local _ _ hUpperTailTy').1
  exact ⟨hUpperTy, hUpperZeroTy, hUpperOnesTy, hLowerTy⟩

private theorem bv_sign_extend_eq_const_1_type_parts
    (x m c nm mp nm2 nmm1 : Term) :
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
      Term.Bool ∧
    __eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvSignExtendEqConst1Lhs x m c nm))
      (__eo_typeof (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvSignExtendEqConstSign x m))
          (__eo_typeof (bvZeroExtendUltConstConst c nm)) ≠ Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvSignExtendEqConst1Lhs, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_sign_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.1 with ⟨wide, hSignTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.symm.trans hSignTy
  rcases bv_sign_extend_eq_const_rhs_types x m c nm mp nm2 nmm1 hRhsNe with
    ⟨_hUpperTy, hUpperZeroTy, hUpperOnesTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    have hsimpa := hLowerTy
    try simp [bvSignExtendEqConstLower, bvZeroExtendEqConstLower, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hSignTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperZeroTy, hUpperOnesTy⟩

private theorem bv_sign_extend_eq_const_2_type_parts
    (x m c nm mp nm2 nmm1 : Term) :
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
      Term.Bool ∧
    __eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvSignExtendEqConst2Lhs x m c nm))
      (__eo_typeof (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvZeroExtendUltConstConst c nm))
          (__eo_typeof (bvSignExtendEqConstSign x m)) ≠ Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvSignExtendEqConst2Lhs, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_sign_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.2 with ⟨wide, hSignTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.trans hSignTy
  rcases bv_sign_extend_eq_const_rhs_types x m c nm mp nm2 nmm1 hRhsNe with
    ⟨_hUpperTy, hUpperZeroTy, hUpperOnesTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    have hsimpa := hLowerTy
    try simp [bvSignExtendEqConstLower, bvZeroExtendEqConstLower, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hSignTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperZeroTy, hUpperOnesTy⟩

private theorem bv_sign_extend_eq_const_context_of_types
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A P L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      mp = Term.Numeral P ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 P = true ∧
      native_zleq 0 L = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = P ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvSignExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstZero mp)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstNotZero mp)) =
        SmtType.BitVec (native_int_to_nat P) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hWideTypes hLowTypes
    hUpperZeroTy
  rcases hLowTypes with ⟨widthW, hXTy, hLowTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width
      x widthW hXTrans hXTy with
    ⟨W, hWidthW, hW0, hXSmtTy⟩
  subst widthW
  rcases hWideTypes with ⟨widthWide, hSignTy, hConstTy⟩
  rcases sign_extend_index_context x m widthWide W hXTy hSignTy with
    ⟨A, hM, hA0, hWidthWide⟩
  subst m
  subst widthWide
  have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_all_ones_const_context c nm
      (Term.Numeral (native_zplus W A)) hCNe hNmNe
      (by have hsimpa := hConstTy; (try simp [bvZeroExtendUltConstConst] at hsimpa ⊢); exact hsimpa) with
    ⟨N, hNm, hWidthN, hN0, hCTy⟩
  have hN : N = native_zplus W A := by
    injection hWidthN with h
    exact h.symm
  subst N
  subst nm
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c (Term.UOp UserOp.Int) (__eo_to_smt c) rfl hCTrans hCTy
  have hConstSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type c (native_zplus W A)
        hCSmtTy hN0
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rw [hLowTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wideLow, L, lowIndex, _hConstEoTyLow, hNm2, hLowIndex,
      hWideLow0, hLowIndex0, hLWide, hDLow0, hConstSmtTyLow⟩
  have hLowIndexEq : lowIndex = 0 := by
    injection hLowIndex with h
    exact h.symm
  subst lowIndex
  subst nm2
  let dLow := native_zplus (native_zplus L 1) (native_zneg 0)
  have hLowSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtType.BitVec (native_int_to_nat dLow) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideLow L 0 hConstSmtTyLow hWideLow0 hLowIndex0 hLWide hDLow0
  have hLowTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLowSmtTyRaw]
    intro h
    cases h
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtType.BitVec (native_int_to_nat W) := by
    have h :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L))
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L)))
        rfl hLowTrans hLowTy
    simpa [__eo_to_smt_type, hW0, native_ite] using h
  have hDLowNat : native_int_to_nat dLow = native_int_to_nat W := by
    rw [hLowSmtTyRaw] at hLowSmtTy
    injection hLowSmtTy
  have hDLowEq : dLow = W :=
    nonneg_int_eq_of_toNat_eq dLow W
      (native_zleq_of_zlt_true _ _ hDLow0) hW0 hDLowNat
  have hLWidth : native_zplus L 1 = W := by
    simpa [dLow, SmtEval.native_zplus, SmtEval.native_zneg] using hDLowEq
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    have hRaw := smt_typeof_sign_extend_of_context x W A
      hXSmtTy hW0 hA0
    have hComm : native_zplus A W = native_zplus W A := by
      simp [SmtEval.native_zplus, Int.add_comm]
    simpa [bvSignExtendEqConstSign, hComm] using hRaw
  have hUpperZeroTy' :
      __eo_typeof_eq
          (__eo_typeof
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L) nmm1))
          (__eo_typeof (bvSignExtendEqConstZero mp)) = Term.Bool := by
    have hsimpa := hUpperZeroTy
    try simp [bvSignExtendEqConstUpperZero, bvSignExtendEqConstHigh, bvZeroExtendEqConstEq] at hsimpa ⊢
    exact hsimpa
  have hUpperZeroSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hUpperZeroTy'
  have hUpperZeroTypes :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hUpperZeroTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A))) nmm1 (Term.Numeral L)
      hUpperZeroSides.1 with ⟨upperWidth, hHighEoTy⟩
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nmm1 (Term.Numeral L) hConstTrans hUpperZeroSides.1 with
    ⟨wideHigh, H, lowHigh, _hConstEoTyHigh, hNmm1, hLowHigh,
      hWideHigh0, hLowHigh0, hHWide, hDHigh0, hConstSmtTyHigh⟩
  have hLowHighEq : lowHigh = L := by
    injection hLowHigh with h
    exact h.symm
  subst lowHigh
  subst nmm1
  let dHigh := native_zplus (native_zplus H 1) (native_zneg L)
  have hHighSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat dHigh) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideHigh H L hConstSmtTyHigh hWideHigh0 hLowHigh0 hHWide hDHigh0
  have hMpNe := RuleProofs.term_ne_stuck_of_has_smt_translation mp hMpTrans
  have hZeroEoTy :
      __eo_typeof (bvSignExtendEqConstZero mp) =
        Term.Apply (Term.UOp UserOp.BitVec) upperWidth :=
    hUpperZeroTypes.symm.trans hHighEoTy
  rcases bv_all_ones_const_context (Term.Numeral 0) mp upperWidth
      (by intro h; cases h) hMpNe
      (by simpa [bvSignExtendEqConstZero, bvZeroExtendUltConstConst,
        bvAllOnesConst] using hZeroEoTy) with
    ⟨P, hMp, hUpperWidth, hP0, _hZeroValTy⟩
  subst mp
  subst upperWidth
  have hHighTrans :
      RuleProofs.eo_has_smt_translation
        (bvSignExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hHighSmtTyRaw]
    intro h
    cases h
  have hZeroSmtTy :
      __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) =
        SmtType.BitVec (native_int_to_nat P) := by
    simpa [bvSignExtendEqConstZero, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type (Term.Numeral 0) P rfl hP0
  have hZeroTrans :
      RuleProofs.eo_has_smt_translation
        (bvSignExtendEqConstZero (Term.Numeral P)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hZeroSmtTy]
    intro h
    cases h
  have hHighBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvSignExtendEqConstHigh c
        (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H))
      (__eo_typeof
        (bvSignExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)))
      (__eo_to_smt
        (bvSignExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))) rfl hHighTrans rfl
  have hZeroBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvSignExtendEqConstZero (Term.Numeral P))
      (__eo_typeof (bvSignExtendEqConstZero (Term.Numeral P)))
      (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P)))
      rfl hZeroTrans rfl
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat P) := by
    calc
      _ = __eo_to_smt_type
          (__eo_typeof
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) := hHighBridge
      _ = __eo_to_smt_type
          (__eo_typeof (bvSignExtendEqConstZero (Term.Numeral P))) := by
            rw [hUpperZeroTypes]
      _ = __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) :=
            hZeroBridge.symm
      _ = SmtType.BitVec (native_int_to_nat P) := hZeroSmtTy
  have hDHighNat : native_int_to_nat dHigh = native_int_to_nat P := by
    rw [hHighSmtTyRaw] at hHighSmtTy
    injection hHighSmtTy
  have hDHighEq : dHigh = P :=
    nonneg_int_eq_of_toNat_eq dHigh P
      (native_zleq_of_zlt_true _ _ hDHigh0) hP0 hDHighNat
  have hHWidth :
      native_zplus (native_zplus H 1) (native_zneg L) = P := by
    simpa [dHigh] using hDHighEq
  have hNotZeroSmtTy :
      __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstNotZero (Term.Numeral P))) =
        SmtType.BitVec (native_int_to_nat P) := by
    change __smtx_typeof
        (SmtTerm.bvnot
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P)))) = _
    exact smt_typeof_bvnot_same_local
      (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) P
      hZeroSmtTy
  exact ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl,
    hW0, hA0, hP0, hLowHigh0, hLWidth, hHWidth, hXSmtTy, hConstSmtTy,
    hLowSmtTy, hSignSmtTy, hHighSmtTy, hZeroSmtTy, hNotZeroSmtTy⟩

private theorem bv_sign_extend_eq_const_1_context
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    ∃ W A P L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      mp = Term.Numeral P ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 P = true ∧
      native_zleq 0 L = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = P ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvSignExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstZero mp)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstNotZero mp)) =
        SmtType.BitVec (native_int_to_nat P) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_1_type_parts x m c nm mp nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpperZero, _hUpperOnes⟩
  exact bv_sign_extend_eq_const_context_of_types x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hWide hLow hUpperZero

private theorem bv_sign_extend_eq_const_2_context
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    ∃ W A P L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      mp = Term.Numeral P ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 P = true ∧
      native_zleq 0 L = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = P ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvSignExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstZero mp)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstNotZero mp)) =
        SmtType.BitVec (native_int_to_nat P) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_2_type_parts x m c nm mp nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpperZero, _hUpperOnes⟩
  exact bv_sign_extend_eq_const_context_of_types x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hWide hLow hUpperZero

private theorem typed_bv_sign_extend_eq_const_1_term
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_1_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, _hW0, _hA0, _hP0,
      _hL0, _hLWidth, _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy,
      hSignSmtTy, hHighSmtTy, hZeroSmtTy, hNotZeroSmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvSignExtendEqConst1Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hSignSmtTy.trans hConstSmtTy.symm)
      (by rw [hSignSmtTy]; intro h; cases h)
  have hUpperZeroBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperZero (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperZero bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperOnesBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperOnes bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hNotZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperTailBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstOr
          (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))
          (Term.Boolean false)) := by
    unfold bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperOnesBool eo_has_bool_type_false_local
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpper (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpper bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperZeroBool hUpperTailBool
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvSignExtendEqConstLower bvZeroExtendEqConstLower
      bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvSignExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hLowerBool RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral P)
          (Term.Numeral L) (Term.Numeral H)) := by
    unfold bvSignExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hUpperBool hTailBool
  unfold bvSignExtendEqConst1Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem typed_bv_sign_extend_eq_const_2_term
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_2_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, _hW0, _hA0, _hP0,
      _hL0, _hLWidth, _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy,
      hSignSmtTy, hHighSmtTy, hZeroSmtTy, hNotZeroSmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvSignExtendEqConst2Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hConstSmtTy.trans hSignSmtTy.symm)
      (by rw [hConstSmtTy]; intro h; cases h)
  have hUpperZeroBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperZero (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperZero bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperOnesBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperOnes bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hNotZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperTailBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstOr
          (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))
          (Term.Boolean false)) := by
    unfold bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperOnesBool eo_has_bool_type_false_local
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpper (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpper bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperZeroBool hUpperTailBool
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvSignExtendEqConstLower bvZeroExtendEqConstLower
      bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvSignExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hLowerBool RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral P)
          (Term.Numeral L) (Term.Numeral H)) := by
    unfold bvSignExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hUpperBool hTailBool
  unfold bvSignExtendEqConst2Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem eval_bvsize_bv_sign_extend_eq_const
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

private theorem eval_width_minus_one_bv_sign_extend_eq_const
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
  rw [eval_bvsize_bv_sign_extend_eq_const M x w hw0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus,
    native_zneg]

private theorem bv_sign_extend_eq_const_mp_numeric
    (M : SmtModel) (A P : native_Int) :
    eo_interprets M
      (bvSignExtendEqConstMpPrem (Term.Numeral A) (Term.Numeral P))
      true ->
    P = native_zplus A 1 := by
  intro hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral P)
            (SmtTerm.plus (SmtTerm.Numeral A)
              (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq] at hEval
      simpa [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval__, __smtx_model_eval_plus, native_veq,
        native_zplus] using hEval

private theorem bv_sign_extend_eq_const_nm2_numeric
    (M : SmtModel) (x : Term) (W L : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral L)) true ->
    L = native_zplus W (native_zneg 1) := by
  intro hW0 hXSmtTy hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral L)
            (SmtTerm.neg
              (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
              (SmtTerm.Numeral 1))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq] at hEval
      change __smtx_model_eval_eq (SmtValue.Numeral L)
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                (Term.Numeral 1)))) =
        SmtValue.Boolean true at hEval
      rw [eval_width_minus_one_bv_sign_extend_eq_const
        M x W hW0 hXSmtTy] at hEval
      simpa [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval__, native_veq] using hEval

private theorem eval_sign_extend_term_local
    (M : SmtModel) (x : Term) (a : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral a))) =
      __smtx_model_eval_sign_extend (SmtValue.Numeral a)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.sign_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp [__smtx_model_eval]

private theorem eval_bvnot_term_local (M : SmtModel) (x : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_sign_extend_eq_const_1_lhs_eq_rhs
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A P L H : native_Int) :
    native_zleq 0 W = true ->
    native_zleq 0 A = true ->
    native_zleq 0 P = true ->
    native_zleq 0 L = true ->
    native_zplus L 1 = W ->
    native_zplus (native_zplus H 1) (native_zneg L) = P ->
    P = native_zplus A 1 ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConstRhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)) (Term.Numeral P)
            (Term.Numeral L) (Term.Numeral H))) := by
  intro hW0 hA0 hP0 hL0 hLWidth hHWidth hMp hXSmtTy hConstSmtTy
  have hWNonneg : (0 : Int) ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have hANonneg : (0 : Int) ≤ A := by
    simpa [SmtEval.native_zleq] using hA0
  have hPNonneg : (0 : Int) ≤ P := by
    simpa [SmtEval.native_zleq] using hP0
  have hLNonneg : (0 : Int) ≤ L := by
    simpa [SmtEval.native_zleq] using hL0
  have hLWidthInt : L + 1 = W := by
    simpa [SmtEval.native_zplus] using hLWidth
  have hHWidthInt : H + 1 + -L = P := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hHWidth
  have hMpInt : P = A + 1 := by
    simpa [SmtEval.native_zplus] using hMp
  have hWPosInt : (0 : Int) < W := by
    rw [← hLWidthInt]
    omega
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWCast : (↑WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hACast : (↑AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hWNatPos : 0 < WN := by
    apply Int.ofNat_lt.mp
    change (0 : Int) < (↑WN : Int)
    rw [hWCast]
    exact hWPosInt
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    have hwa : (0 : Int) ≤ W + A := by omega
    have hsimpa := hwa
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    apply Int.ofNat.inj
    have h := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    simpa [Smtm.native_nat_to_int, native_nat_to_int,
      SmtEval.native_zplus, WN, AN, hWCast, hACast] using h
  have hPCastA1 : P = (↑(AN + 1) : Int) := by
    calc
      P = A + 1 := hMpInt
      _ = (↑(AN + 1) : Int) := by
        rw [← hACast]
        norm_cast
  have hLowStart : (0 : Int) = (↑(0 : Nat) : Int) := rfl
  have hLowLen : L + 1 + -0 = (↑WN : Int) := by
    simpa using hLWidthInt.trans hWCast.symm
  have hHighStart : L = (↑(WN - 1) : Int) := by
    calc
      L = W - 1 := by
        rw [← hLWidthInt]
        simp
      _ = (↑WN : Int) - 1 := by rw [← hWCast]
      _ = (↑(WN - 1) : Int) :=
          (Int.ofNat_sub (by omega : 1 ≤ WN)).symm
  have hHighLen : H + 1 + -L = (↑(AN + 1) : Int) := by
    calc
      H + 1 + -L = P := hHWidthInt
      _ = (↑(AN + 1) : Int) := hPCastA1
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      (by simpa [WN] using hXSmtTy) with
    ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑WN : Int) px := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, Smtm.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int]
      using hXRange.2
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A)))) (WN + AN)
      (by simpa [hWideNat] using hConstSmtTy) with
    ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) pc := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (↑(WN + AN) : Int) :=
        Int.natCast_nonneg _
      have hsimpa := hnn; (try simp [SmtEval.native_zleq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢); exact decide_eq_true hsimpa) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    have hsimpa := hConstRange.2
    try simp [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hXPayload : (↑xBV.toNat : Int) = px := by
    have hToNat := ofInt_toNat_canonical WN px hPx0 hPx1
    simp [xBV, hToNat, Int.toNat_of_nonneg hPx0]
  have hConstPayload : (↑cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hXEvalBV :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑WN : Int) (↑xBV.toNat : Int) := by
    rw [hXEval']
    rw [hXPayload]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) (↑cBV.toNat : Int) := by
    rw [hConstEval']
    rw [hConstPayload]
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (↑(WN + AN) : Int)
          (↑(xBV.signExtend (WN + AN)).toNat : Int) := by
    rw [eval_sign_extend_term_local, hXEval']
    rw [← hACast]
    rw [sign_extend_val_bitvec WN AN px hPx0 hPx1]
    rw [Nat.add_comm AN WN]
  have hLowExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtValue.Binary (↑WN : Int)
          (↑(cBV.extractLsb' 0 WN).toNat : Int) := by
    unfold bvZeroExtendUltConstLow
    change __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))
            (Term.Numeral L) (Term.Numeral 0))) = _
    rw [eval_extract_term, hConstEval']
    rw [extract_val_bitvec_start_len (WN + AN) 0 WN pc L 0
      hPc0 hPc1 hLowStart hLowLen]
  have hHighExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H))) =
        SmtValue.Binary (↑(AN + 1) : Int)
          (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int) := by
    unfold bvSignExtendEqConstHigh bvZeroExtendEqConstHigh
    change __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))
            (Term.Numeral H) (Term.Numeral L))) = _
    rw [eval_extract_term, hConstEval']
    rw [extract_val_bitvec_start_len (WN + AN) (WN - 1) (AN + 1)
      pc H L hPc0 hPc1 hHighStart hHighLen]
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) =
        SmtValue.Binary (↑(AN + 1) : Int)
          (↑(0#(AN + 1)).toNat : Int) := by
    unfold bvSignExtendEqConstZero bvZeroExtendUltConstConst
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral P) (SmtTerm.Numeral 0)) = _
    rw [hPCastA1]
    have hMod0 :
        native_mod_total 0
            (native_int_pow2 ((↑AN : Int) + 1)) = 0 := by
      simp [native_mod_total]
    simp [smtx_eval_int_to_bv_numerals, hMod0]
  have hNotZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSignExtendEqConstNotZero (Term.Numeral P))) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (↑(AN + 1) : Int) 0) := by
    unfold bvSignExtendEqConstNotZero
    rw [eval_bvnot_term_local, hZeroEval]
    simp
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑(xBV.signExtend (WN + AN)).toNat : Int))
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑cBV.toNat : Int)) := by
    unfold bvSignExtendEqConst1Lhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A)))
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))) = _
    rw [smtx_eval_eq_term_eq, hSignEval, hConstEvalBV]
  have hUpperZeroEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstUpperZero (Term.Numeral P) c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(AN + 1) : Int)
            (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
          (SmtValue.Binary (↑(AN + 1) : Int)
            (↑(0#(AN + 1)).toNat : Int)) := by
    unfold bvSignExtendEqConstUpperZero bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H)))
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P)))) = _
    rw [smtx_eval_eq_term_eq, hHighExtractEval, hZeroEval]
  have hUpperOnesEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(AN + 1) : Int)
            (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
          (__smtx_model_eval_bvnot
            (SmtValue.Binary (↑(AN + 1) : Int) 0)) := by
    unfold bvSignExtendEqConstUpperOnes bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H)))
          (__eo_to_smt (bvSignExtendEqConstNotZero (Term.Numeral P)))) = _
    rw [smtx_eval_eq_term_eq, hHighExtractEval, hNotZeroEval]
  have hLowerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstLower x c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑WN : Int) (↑xBV.toNat : Int))
          (SmtValue.Binary (↑WN : Int)
            (↑(cBV.extractLsb' 0 WN).toNat : Int)) := by
    unfold bvSignExtendEqConstLower bvZeroExtendEqConstLower
      bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x)
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)))) = _
    rw [smtx_eval_eq_term_eq, hXEvalBV, hLowExtractEval]
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstRhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)) (Term.Numeral P)
              (Term.Numeral L) (Term.Numeral H))) =
        __smtx_model_eval_and
          (__smtx_model_eval_or
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑(AN + 1) : Int)
                (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
              (SmtValue.Binary (↑(AN + 1) : Int)
                (↑(0#(AN + 1)).toNat : Int)))
            (__smtx_model_eval_or
              (__smtx_model_eval_eq
                (SmtValue.Binary (↑(AN + 1) : Int)
                  (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
                (__smtx_model_eval_bvnot
                  (SmtValue.Binary (↑(AN + 1) : Int) 0)))
              (SmtValue.Boolean false)))
          (__smtx_model_eval_and
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑WN : Int) (↑xBV.toNat : Int))
              (SmtValue.Binary (↑WN : Int)
                (↑(cBV.extractLsb' 0 WN).toNat : Int)))
            (SmtValue.Boolean true)) := by
    unfold bvSignExtendEqConstRhs bvZeroExtendEqConstAnd
      bvSignExtendEqConstUpper bvSignExtendEqConstOr
    change __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.or
            (__eo_to_smt
              (bvSignExtendEqConstUpperZero (Term.Numeral P) c
                (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H)))
            (SmtTerm.or
              (__eo_to_smt
                (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
                  (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                  (Term.Numeral H)))
              (SmtTerm.Boolean false)))
          (SmtTerm.and
            (__eo_to_smt
              (bvSignExtendEqConstLower x c
                (Term.Numeral (native_zplus W A)) (Term.Numeral L)))
            (SmtTerm.Boolean true))) = _
    rw [smtx_eval_and_term_eq, smtx_eval_or_term_eq,
      smtx_eval_or_term_eq, smtx_eval_and_term_eq]
    rw [hUpperZeroEval, hUpperOnesEval, hLowerEval]
    simp [__smtx_model_eval]
  rw [hLhsEval, hRhsEval]
  exact eval_sign_extend_eq_characterization xBV cBV hWNatPos

private theorem facts_bv_sign_extend_eq_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvSignExtendEqConstMpPrem m mp) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
    hMpPrem _hWidthPrem _hNmm1Prem
  have hTermBool :=
    typed_bv_sign_extend_eq_const_1_term x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_1_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, hW0, hA0, hP0,
      hL0, hLWidth, hHWidth, hXSmtTy, hConstSmtTy, _hLowSmtTy,
      _hSignSmtTy, _hHighSmtTy, _hZeroSmtTy, _hNotZeroSmtTy⟩
  have hMpEq := bv_sign_extend_eq_const_mp_numeric M A P hMpPrem
  have hEvalEq :=
    eval_bv_sign_extend_eq_const_1_lhs_eq_rhs M hM x c W A P L H
      hW0 hA0 hP0 hL0 hLWidth hHWidth hMpEq hXSmtTy hConstSmtTy
  refine RuleProofs.eo_interprets_eq_of_rel M
    (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)))
    (bvSignExtendEqConstRhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)) (Term.Numeral P)
      (Term.Numeral L) (Term.Numeral H)) ?_ ?_
  · simpa [bvSignExtendEqConst1Term, bvZeroExtendEqConstEq] using hTermBool
  · rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

private theorem eval_bv_sign_extend_eq_const_2_lhs_eq_1_lhs
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A : native_Int) :
    native_zleq 0 W = true ->
    native_zleq 0 A = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) := by
  intro hW0 hA0 hXSmtTy hConstSmtTy
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWCast : (↑WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hACast : (↑AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    have hWNonneg : (0 : Int) ≤ W := by
      simpa [SmtEval.native_zleq] using hW0
    have hANonneg : (0 : Int) ≤ A := by
      simpa [SmtEval.native_zleq] using hA0
    have hwa : (0 : Int) ≤ W + A := by omega
    have hsimpa := hwa
    try simp [SmtEval.native_zleq, SmtEval.native_zplus] at hsimpa ⊢
    exact decide_eq_true hsimpa
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    apply Int.ofNat.inj
    have h := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    simpa [Smtm.native_nat_to_int, native_nat_to_int,
      SmtEval.native_zplus, WN, AN, hWCast, hACast] using h
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      (by simpa [WN] using hXSmtTy) with
    ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑WN : Int) px := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, Smtm.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int]
      using hXRange.2
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A)))) (WN + AN)
      (by simpa [hWideNat] using hConstSmtTy) with
    ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) pc := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (↑(WN + AN) : Int) :=
        Int.natCast_nonneg _
      have hsimpa := hnn; (try simp [SmtEval.native_zleq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢); exact decide_eq_true hsimpa) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    have hsimpa := hConstRange.2
    try simp [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hXPayload : (↑xBV.toNat : Int) = px := by
    have hToNat := ofInt_toNat_canonical WN px hPx0 hPx1
    simp [xBV, hToNat, Int.toNat_of_nonneg hPx0]
  have hConstPayload : (↑cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) (↑cBV.toNat : Int) := by
    rw [hConstEval']
    rw [hConstPayload]
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (↑(WN + AN) : Int)
          (↑(xBV.signExtend (WN + AN)).toNat : Int) := by
    rw [eval_sign_extend_term_local, hXEval']
    rw [← hACast]
    rw [sign_extend_val_bitvec WN AN px hPx0 hPx1]
    rw [Nat.add_comm AN WN]
  have hLhs1Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑(xBV.signExtend (WN + AN)).toNat : Int))
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑cBV.toNat : Int)) := by
    unfold bvSignExtendEqConst1Lhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A)))
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))) = _
    rw [smtx_eval_eq_term_eq, hSignEval, hConstEvalBV]
  have hLhs2Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑cBV.toNat : Int))
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑(xBV.signExtend (WN + AN)).toNat : Int)) := by
    unfold bvSignExtendEqConst2Lhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A)))) = _
    rw [smtx_eval_eq_term_eq, hSignEval, hConstEvalBV]
  rw [hLhs1Eval, hLhs2Eval]
  rw [smt_eval_eq_bitvec_values, smt_eval_eq_bitvec_values]
  have hDec :
      decide (cBV = xBV.signExtend (WN + AN)) =
        decide (xBV.signExtend (WN + AN) = cBV) := by
    rw [decide_eq_decide]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hDec]

private theorem facts_bv_sign_extend_eq_const_2_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvSignExtendEqConstMpPrem m mp) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
    hMpPrem _hWidthPrem _hNmm1Prem
  have hTermBool :=
    typed_bv_sign_extend_eq_const_2_term x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_2_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, hW0, hA0, hP0,
      hL0, hLWidth, hHWidth, hXSmtTy, hConstSmtTy, _hLowSmtTy,
      _hSignSmtTy, _hHighSmtTy, _hZeroSmtTy, _hNotZeroSmtTy⟩
  have hMpEq := bv_sign_extend_eq_const_mp_numeric M A P hMpPrem
  have hEvalEq1 :=
    eval_bv_sign_extend_eq_const_1_lhs_eq_rhs M hM x c W A P L H
      hW0 hA0 hP0 hL0 hLWidth hHWidth hMpEq hXSmtTy hConstSmtTy
  have hEvalLhs :=
    eval_bv_sign_extend_eq_const_2_lhs_eq_1_lhs M hM x c W A
      hW0 hA0 hXSmtTy hConstSmtTy
  refine RuleProofs.eo_interprets_eq_of_rel M
    (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)))
    (bvSignExtendEqConstRhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)) (Term.Numeral P)
      (Term.Numeral L) (Term.Numeral H)) ?_ ?_
  · simpa [bvSignExtendEqConst2Term, bvZeroExtendEqConstEq] using hTermBool
  · rw [hEvalLhs, hEvalEq1]
    exact RuleProofs.smt_value_rel_refl _

def bvSignExtendEqConst1Program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_sign_extend_eq_const_1 x m c nm mp nm2 nmm1
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private def bvSignExtendEqConstGuard
    (x m nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef :
      Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and (__eo_eq mp mpRef) (__eo_eq m mRef))
          (__eo_eq nm2 nm2Ref))
        (__eo_eq x xRef))
      (__eo_eq nmm1 nmm1Ref))
    (__eo_eq nm nmRef)

private theorem bv_sign_extend_eq_const_guard_refs
    {x m nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef body :
      Term} :
    __eo_requires
        (bvSignExtendEqConstGuard x m nm mp nm2 nmm1 mpRef mRef
          nm2Ref xRef nmm1Ref nmRef)
        (Term.Boolean true) body ≠ Term.Stuck ->
    mpRef = mp ∧ mRef = m ∧ nm2Ref = nm2 ∧ xRef = x ∧
      nmm1Ref = nmm1 ∧ nmRef = nm := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvSignExtendEqConstGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG5, hNm⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hNmm1⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hX⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNm2⟩
  rcases bv_extract_support_and_true hG2 with ⟨hMp, hM⟩
  exact ⟨(bv_extract_support_eq_true hMp).symm,
    (bv_extract_support_eq_true hM).symm,
    (bv_extract_support_eq_true hNm2).symm,
    (bv_extract_support_eq_true hX).symm,
    (bv_extract_support_eq_true hNmm1).symm,
    (bv_extract_support_eq_true hNm).symm⟩

private theorem bv_sign_extend_eq_const_1_premise_shape
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
      P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
      P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hMp hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
        P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
        P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_eq_const_1.eq_9
      x m c nm mp nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      (Proof.pf P3)
      hX hM hC hNm hMp hNm2 hNmm1 (by
        intro mpRef mRef nm2Ref xRef nmm1Ref nmRef hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl, rfl⟩)

private theorem bv_sign_extend_eq_const_1_program_canonical
    (x m c nm mp nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst1Program x m c nm mp nm2 nmm1
        (bvSignExtendEqConstMpPrem m mp)
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvSignExtendEqConst1Term x m c nm mp nm2 nmm1 := by
  intro hX hM hC hNm hMp hNm2 hNmm1
  unfold bvSignExtendEqConst1Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_sign_extend_eq_const_1.eq_8
    x m c nm mp nm2 nmm1 mp m nm2 x nmm1 nm
    hX hM hC hNm hMp hNm2 hNmm1]
  simp [bvSignExtendEqConstGuard, bvSignExtendEqConst1Term,
    bvSignExtendEqConst1Lhs, bvSignExtendEqConstRhs,
    bvSignExtendEqConstSign, bvSignExtendEqConstUpper,
    bvSignExtendEqConstUpperZero, bvSignExtendEqConstUpperOnes,
    bvSignExtendEqConstOr, bvSignExtendEqConstLower,
    bvSignExtendEqConstHigh, bvSignExtendEqConstZero,
    bvSignExtendEqConstNotZero, bvZeroExtendEqConstEq,
    bvZeroExtendEqConstAnd, bvZeroExtendEqConstHigh,
    bvZeroExtendEqConstLower, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hMp, hNm2, hNmm1]

private theorem bvSignExtendEqConst1Program_normalize
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvSignExtendEqConstMpPrem m mp ∧
      P2 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3 =
        bvSignExtendEqConst1Term x m c nm mp nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
    hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hMp := RuleProofs.term_ne_stuck_of_has_smt_translation mp hMpTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_sign_extend_eq_const_1_premise_shape
      x m c nm mp nm2 nmm1 P1 P2 P3 hX hM hC hNm hMp hNm2
      hNmm1 hProg with
    ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvSignExtendEqConst1Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_sign_extend_eq_const_1.eq_8
    x m c nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hMp hNm2 hNmm1] at hReq
  rcases bv_sign_extend_eq_const_guard_refs
      (by simpa [bvSignExtendEqConstGuard] using hReq) with
    ⟨hMpRef, hMRef, hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst mpRef
  subst mRef
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvSignExtendEqConstMpPrem m mp := hP1
  have hP2Canonical : P2 = bvZeroExtendUltConstWidthPrem x nm2 := hP2
  have hP3Canonical : P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP3
  refine ⟨hP1Canonical, hP2Canonical, hP3Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical, hP3Canonical]
  exact bv_sign_extend_eq_const_1_program_canonical
    x m c nm mp nm2 nmm1 hX hM hC hNm hMp hNm2 hNmm1

theorem typed_bv_sign_extend_eq_const_1_program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst1Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_eq_const_1_term x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy

theorem facts_bv_sign_extend_eq_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3)
      true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst1Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hMpPrem :
      eo_interprets M (bvSignExtendEqConstMpPrem m mp) true := by
    simpa [hP1] using hP1True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP2] using hP2True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_sign_extend_eq_const_1_term M hM x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy
    hMpPrem hWidthPrem hNmm1Prem

def bvSignExtendEqConst2Program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_sign_extend_eq_const_2 x m c nm mp nm2 nmm1
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private theorem bv_sign_extend_eq_const_2_premise_shape
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
      P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
      P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hMp hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
        P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
        P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_eq_const_2.eq_9
      x m c nm mp nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      (Proof.pf P3)
      hX hM hC hNm hMp hNm2 hNmm1 (by
        intro mpRef mRef nm2Ref xRef nmm1Ref nmRef hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl, rfl⟩)

private theorem bv_sign_extend_eq_const_2_program_canonical
    (x m c nm mp nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst2Program x m c nm mp nm2 nmm1
        (bvSignExtendEqConstMpPrem m mp)
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvSignExtendEqConst2Term x m c nm mp nm2 nmm1 := by
  intro hX hM hC hNm hMp hNm2 hNmm1
  unfold bvSignExtendEqConst2Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_sign_extend_eq_const_2.eq_8
    x m c nm mp nm2 nmm1 mp m nm2 x nmm1 nm
    hX hM hC hNm hMp hNm2 hNmm1]
  simp [bvSignExtendEqConstGuard, bvSignExtendEqConst2Term,
    bvSignExtendEqConst2Lhs, bvSignExtendEqConstRhs,
    bvSignExtendEqConstSign, bvSignExtendEqConstUpper,
    bvSignExtendEqConstUpperZero, bvSignExtendEqConstUpperOnes,
    bvSignExtendEqConstOr, bvSignExtendEqConstLower,
    bvSignExtendEqConstHigh, bvSignExtendEqConstZero,
    bvSignExtendEqConstNotZero, bvZeroExtendEqConstEq,
    bvZeroExtendEqConstAnd, bvZeroExtendEqConstHigh,
    bvZeroExtendEqConstLower, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hMp, hNm2, hNmm1]

private theorem bvSignExtendEqConst2Program_normalize
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvSignExtendEqConstMpPrem m mp ∧
      P2 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3 =
        bvSignExtendEqConst2Term x m c nm mp nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
    hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hMp := RuleProofs.term_ne_stuck_of_has_smt_translation mp hMpTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_sign_extend_eq_const_2_premise_shape
      x m c nm mp nm2 nmm1 P1 P2 P3 hX hM hC hNm hMp hNm2
      hNmm1 hProg with
    ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvSignExtendEqConst2Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_sign_extend_eq_const_2.eq_8
    x m c nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hMp hNm2 hNmm1] at hReq
  rcases bv_sign_extend_eq_const_guard_refs
      (by simpa [bvSignExtendEqConstGuard] using hReq) with
    ⟨hMpRef, hMRef, hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst mpRef
  subst mRef
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvSignExtendEqConstMpPrem m mp := hP1
  have hP2Canonical : P2 = bvZeroExtendUltConstWidthPrem x nm2 := hP2
  have hP3Canonical : P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP3
  refine ⟨hP1Canonical, hP2Canonical, hP3Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical, hP3Canonical]
  exact bv_sign_extend_eq_const_2_program_canonical
    x m c nm mp nm2 nmm1 hX hM hC hNm hMp hNm2 hNmm1

theorem typed_bv_sign_extend_eq_const_2_program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst2Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_eq_const_2_term x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy

theorem facts_bv_sign_extend_eq_const_2_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3)
      true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst2Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hMpPrem :
      eo_interprets M (bvSignExtendEqConstMpPrem m mp) true := by
    simpa [hP1] using hP1True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP2] using hP2True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_sign_extend_eq_const_2_term M hM x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy
    hMpPrem hWidthPrem hNmm1Prem

/-! Support for the middle-range `bv_sign_extend_ult_const` rewrites. -/

private theorem sign_extend_ult_middle_range
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W)
    (hLower : 2 ^ (W - 1) < c.toNat)
    (hUpper : c.toNat ≤ 2 ^ (W + A) - 2 ^ (W - 1)) :
    decide ((x.signExtend (W + A)).toNat < c.toNat) =
      decide (x.msb = false) := by
  have hWWide : W ≤ W + A := by omega
  have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
    calc
      2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
  have hPowMono : 2 ^ W ≤ 2 ^ (W + A) :=
    Nat.pow_le_pow_right (by decide) hWWide
  cases hx : x.msb
  · have hTwoLt : 2 * x.toNat < 2 ^ W :=
      BitVec.msb_eq_false_iff_two_mul_lt.mp hx
    have hXLt : x.toNat < 2 ^ (W - 1) := by omega
    have hSignNat : (x.signExtend (W + A)).toNat = x.toNat := by
      rw [BitVec.signExtend_eq_setWidth_of_msb_false hx,
        BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le x.isLt hPowMono
    simp [hx, hSignNat]
    omega
  · have hTwoGe : 2 ^ W ≤ 2 * x.toNat :=
      BitVec.msb_eq_true_iff_two_mul_ge.mp hx
    have hXGe : 2 ^ (W - 1) ≤ x.toNat := by omega
    have hXWide : x.toNat < 2 ^ (W + A) :=
      Nat.lt_of_lt_of_le x.isLt hPowMono
    have hSignNat :
        (x.signExtend (W + A)).toNat =
          x.toNat + (2 ^ (W + A) - 2 ^ W) := by
      rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt hXWide, hx]
      rfl
    have hSignLower :
        2 ^ (W + A) - 2 ^ (W - 1) ≤
          (x.signExtend (W + A)).toNat := by
      rw [hSignNat]
      omega
    have hNotLt : ¬(x.signExtend (W + A)).toNat < c.toNat := by
      omega
    simp [hx, hNotLt]

def bvSignExtendUltConstAmount (x nm : Term) : Term :=
  bvZeroExtendUltConstConst
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvZeroExtendUltConstBvsize x)) (Term.Numeral 1)) nm

def bvSignExtendUltConstOne (nm : Term) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral 1) nm

def bvSignExtendUltConstZero (nm : Term) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral 0) nm

def bvSignExtendUltConstLowerBound (x nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvshl) (bvSignExtendUltConstOne nm))
    (bvSignExtendUltConstAmount x nm)

def bvSignExtendUltConstUpperBound (x nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvshl)
      (Term.Apply (Term.UOp UserOp.bvnot)
        (bvSignExtendUltConstZero nm)))
    (bvSignExtendUltConstAmount x nm)

def bvSignExtendUltConst2LowerPrem (x c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.bvult)
          (bvSignExtendUltConstLowerBound x nm))
        (bvZeroExtendUltConstConst c nm)))
    (Term.Boolean true)

def bvSignExtendUltConst2UpperPrem (x c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.bvule)
          (bvZeroExtendUltConstConst c nm))
        (bvSignExtendUltConstUpperBound x nm)))
    (Term.Boolean true)

def bvSignExtendUltConstSignBit (x nm2 : Term) : Term :=
  bvExtractTerm x nm2 nm2

def bvSignExtendUltConstBit (b : native_Int) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral b) (Term.Numeral 1)

def bvSignExtendUltConst2Lhs (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult) (bvSignExtendEqConstSign x m))
    (bvZeroExtendUltConstConst c nm)

def bvSignExtendUltConst2Rhs (x nm2 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendUltConstSignBit x nm2)
    (bvSignExtendUltConstBit 0)

def bvSignExtendUltConst2Term (x m c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendUltConst2Lhs x m c nm)
    (bvSignExtendUltConst2Rhs x nm2)

private theorem bv_sign_extend_ult_const_2_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    ∃ W A H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 H = true ∧ native_zlt H W = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvSignExtendUltConstSignBit x nm2)) =
        SmtType.BitVec 1 ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendUltConstBit 0)) =
        SmtType.BitVec 1 := by
  intro hXTrans _hMTrans hCTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof (bvSignExtendEqConstSign x m))
        (__eo_typeof (bvZeroExtendUltConstConst c nm)))
      (__eo_typeof_eq
        (__eo_typeof (bvSignExtendUltConstSignBit x nm2))
        (__eo_typeof (bvSignExtendUltConstBit 0))) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hLhsNe with
    ⟨wideTerm, hSignEoTy, hConstEoTy⟩
  have hRhsTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hRhsNe
  have hRhsSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRhsTy
  have hBitNe :
      __eo_typeof (bvSignExtendUltConstSignBit x nm2) ≠ Term.Stuck :=
    hRhsSides.1
  rcases bv_extract_context_of_non_stuck x nm2 nm2 hXTrans
      (by simpa [bvSignExtendUltConstSignBit] using hBitNe) with
    ⟨W, H, L, hXEoTy, hNm2High, hNm2Low, hW0, hL0, hHW,
      hD0, hXSmtTy⟩
  have hHL : L = H := by
    rw [hNm2High] at hNm2Low
    injection hNm2Low with h
    exact h.symm
  subst L
  subst nm2
  rcases sign_extend_index_context x m wideTerm W hXEoTy hSignEoTy with
    ⟨A, hM, hA0, hWideTerm⟩
  subst m
  subst wideTerm
  have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_all_ones_const_context c nm
      (Term.Numeral (native_zplus W A)) hCNe hNmNe
      (by simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
        hConstEoTy) with
    ⟨N, hNm, hWidthN, hN0, hCTy⟩
  have hN : N = native_zplus W A := by
    injection hWidthN with h
    exact h.symm
  subst N
  subst nm
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c (Term.UOp UserOp.Int) (__eo_to_smt c) rfl hCTrans hCTy
  have hConstSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type c (native_zplus W A)
        hCSmtTy hN0
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    have hRaw := smt_typeof_sign_extend_of_context x W A
      hXSmtTy hW0 hA0
    have hComm : native_zplus A W = native_zplus W A := by
      simp [SmtEval.native_zplus, Int.add_comm]
    simpa [bvSignExtendEqConstSign, hComm] using hRaw
  have hBitSmtTyRaw :=
    smt_typeof_extract_of_context x W H H hXSmtTy hW0 hL0 hHW hD0
  have hBitSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConstSignBit x (Term.Numeral H))) =
        SmtType.BitVec 1 := by
    have hWidthOne :
        native_int_to_nat
            (native_zplus (native_zplus H 1) (native_zneg H)) = 1 := by
      have hEq : native_zplus (native_zplus H 1) (native_zneg H) = 1 := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg]
        have hCancel : H + -H = 0 := by
          simpa using (Int.add_neg_cancel_right (0 : Int) H)
        calc
          H + 1 + -H = H + -H + 1 := by ac_rfl
          _ = 1 := by rw [hCancel, Int.zero_add]
      rw [hEq]
      rfl
    simpa [bvSignExtendUltConstSignBit, hWidthOne] using hBitSmtTyRaw
  have hZeroBitSmtTy :
      __smtx_typeof (__eo_to_smt (bvSignExtendUltConstBit 0)) =
        SmtType.BitVec 1 := by
    have hsimpa :=
      smt_typeof_bv_const_of_int_type (Term.Numeral 0) 1 rfl (by decide)
    try simp [bvSignExtendUltConstBit, bvZeroExtendUltConstConst] at hsimpa ⊢
    exact hsimpa
  exact ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hL0, hHW,
    hXSmtTy, hConstSmtTy, hSignSmtTy, hBitSmtTy, hZeroBitSmtTy⟩

private theorem typed_bv_sign_extend_ult_const_2_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst2Term x m c nm nm2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_sign_extend_ult_const_2_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, H, rfl, rfl, rfl, _hW0, _hA0, _hH0, _hHW,
      _hXSmtTy, hConstSmtTy, hSignSmtTy, hBitSmtTy, hZeroBitSmtTy⟩
  have hLhsSmtTy := smt_typeof_bvult_of_same_bitvec_local
    (bvSignExtendEqConstSign x (Term.Numeral A))
    (bvZeroExtendUltConstConst c
      (Term.Numeral (native_zplus W A)))
    (native_int_to_nat (native_zplus W A)) hSignSmtTy hConstSmtTy
  have hRhsBool : RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst2Rhs x (Term.Numeral H)) := by
    unfold bvSignExtendUltConst2Rhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hBitSmtTy.trans hZeroBitSmtTy.symm)
      (by rw [hBitSmtTy]; intro h; cases h)
  have hRhsSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConst2Rhs x (Term.Numeral H))) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hRhsBool
  unfold bvSignExtendUltConst2Term bvZeroExtendEqConstEq
  have hLhsNN :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConst2Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) ≠ SmtType.None := by
    rw [show __smtx_typeof
        (__eo_to_smt
          (bvSignExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) = SmtType.Bool by
      simpa [bvSignExtendUltConst2Lhs] using hLhsSmtTy]
    intro h
    cases h
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvSignExtendUltConst2Lhs] using
      hLhsSmtTy.trans hRhsSmtTy.symm)
    hLhsNN

private theorem native_int_pow2_nat_cast_sign_ult (n : Nat) :
    native_int_pow2 (Int.ofNat n) = (2 : Int) ^ n := by
  have hn : ¬ (Int.ofNat n : Int) < 0 :=
    Int.not_lt_of_ge (Int.natCast_nonneg n)
  unfold SmtEval.native_int_pow2 SmtEval.native_zexp_total
  rw [if_neg hn]
  simp

private theorem sign_ult_amount_lt_pow (W A : Nat) (hW : 0 < W) :
    (Int.ofNat (W - 1) : Int) < native_int_pow2 (Int.ofNat (W + A)) := by
  rw [native_int_pow2_nat_cast_sign_ult]
  have hNat : W - 1 < 2 ^ (W + A) :=
    Nat.lt_trans (by omega) Nat.lt_two_pow_self
  have hCast : (Int.ofNat (W - 1) : Int) <
      Int.ofNat (2 ^ (W + A)) := by
    exact Int.ofNat_lt.mpr hNat
  simpa using hCast

private theorem eval_sign_extend_ult_const_amount
    (M : SmtModel) (x : Term) (W A : Nat) :
    0 < W ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConstAmount x
            (Term.Numeral (Int.ofNat (W + A))))) =
      SmtValue.Binary (Int.ofNat (W + A)) (Int.ofNat (W - 1)) := by
  intro hW hXTy
  have hWidthEval := eval_width_minus_one_bv_sign_extend_eq_const
    M x (Int.ofNat W) (by simp [SmtEval.native_zleq]) (by have hsimpa := hXTy; (try simp at hsimpa ⊢); exact hsimpa)
  have hWidthCast : (Int.ofNat W : Int) + -1 = Int.ofNat (W - 1) := by
    calc
      (Int.ofNat W : Int) + -1 = (Int.ofNat W : Int) - 1 := rfl
      _ = Int.ofNat (W - 1) :=
        (Int.ofNat_sub (by omega : 1 ≤ W)).symm
  have hNativeWidthCast :
      native_zplus (Int.ofNat W) (native_zneg 1) =
        Int.ofNat (W - 1) := by
    simpa only [SmtEval.native_zplus, SmtEval.native_zneg] using hWidthCast
  have hMod :
      native_mod_total (Int.ofNat (W - 1))
          (native_int_pow2 (Int.ofNat (W + A))) =
        Int.ofNat (W - 1) := by
    apply Int.emod_eq_of_lt
    · exact Int.natCast_nonneg _
    · exact sign_ult_amount_lt_pow W A hW
  unfold bvSignExtendUltConstAmount bvZeroExtendUltConstConst
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral (Int.ofNat (W + A)))
        (SmtTerm.neg
          (__eo_to_smt (bvZeroExtendUltConstBvsize x))
          (SmtTerm.Numeral 1))) = _
  rw [smtx_eval_int_to_bv_term_eq]
  change __smtx_model_eval_int_to_bv
      (__smtx_model_eval M (SmtTerm.Numeral (Int.ofNat (W + A))))
      (__smtx_model_eval M
        (SmtTerm.neg (__eo_to_smt (bvZeroExtendUltConstBvsize x))
          (SmtTerm.Numeral 1))) = _
  rw [show __smtx_model_eval M
        (SmtTerm.neg (__eo_to_smt (bvZeroExtendUltConstBvsize x))
          (SmtTerm.Numeral 1)) =
      SmtValue.Numeral (Int.ofNat (W - 1)) by
    change __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))) = _
    rw [hNativeWidthCast] at hWidthEval
    exact hWidthEval]
  change SmtValue.Binary (Int.ofNat (W + A))
      (native_mod_total (Int.ofNat (W - 1))
        (native_int_pow2 (Int.ofNat (W + A)))) = _
  rw [hMod]

private theorem eval_sign_extend_ult_const_one
    (M : SmtModel) (N : Nat) (hN : 0 < N) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConstOne (Term.Numeral (Int.ofNat N)))) =
      SmtValue.Binary (Int.ofNat N) 1 := by
  have hPow : (1 : Int) < native_int_pow2 (Int.ofNat N) := by
    rw [native_int_pow2_nat_cast_sign_ult]
    exact_mod_cast Nat.one_lt_two_pow (by omega)
  have hMod : native_mod_total 1 (native_int_pow2 (Int.ofNat N)) = 1 :=
    Int.emod_eq_of_lt (by decide) hPow
  unfold bvSignExtendUltConstOne bvZeroExtendUltConstConst
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral (Int.ofNat N))
        (SmtTerm.Numeral 1)) = _
  rw [smtx_eval_int_to_bv_numerals, hMod]

private theorem eval_sign_extend_ult_const_zero
    (M : SmtModel) (N : Nat) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConstZero (Term.Numeral (Int.ofNat N)))) =
      SmtValue.Binary (Int.ofNat N) 0 := by
  unfold bvSignExtendUltConstZero bvZeroExtendUltConstConst
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral (Int.ofNat N))
        (SmtTerm.Numeral 0)) = _
  rw [smtx_eval_int_to_bv_numerals]
  simp [SmtEval.native_mod_total]

private theorem eval_sign_extend_ult_const_lower_bound
    (M : SmtModel) (x : Term) (W A : Nat) :
    0 < W ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConstLowerBound x
            (Term.Numeral (Int.ofNat (W + A))))) =
      SmtValue.Binary (Int.ofNat (W + A))
        (Int.ofNat (2 ^ (W - 1))) := by
  intro hW hXTy
  have hN : 0 < W + A := by omega
  have hOne := eval_sign_extend_ult_const_one M (W + A) hN
  have hAmount := eval_sign_extend_ult_const_amount M x W A hW hXTy
  have hPowLt : (2 : Int) ^ (W - 1) < (2 : Int) ^ (W + A) := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  have hMod :
      native_mod_total
          (native_zmult 1 (native_int_pow2 (Int.ofNat (W - 1))))
          (native_int_pow2 (Int.ofNat (W + A))) =
        Int.ofNat (2 ^ (W - 1)) := by
    rw [native_int_pow2_nat_cast_sign_ult,
      native_int_pow2_nat_cast_sign_ult]
    change ((1 : Int) * 2 ^ (W - 1)) % 2 ^ (W + A) =
      Int.ofNat (2 ^ (W - 1))
    rw [Int.one_mul, Int.emod_eq_of_lt]
    · norm_cast
    · exact Int.natCast_nonneg _
    · exact hPowLt
  unfold bvSignExtendUltConstLowerBound
  change __smtx_model_eval M
      (SmtTerm.bvshl
        (__eo_to_smt
          (bvSignExtendUltConstOne (Term.Numeral (Int.ofNat (W + A)))))
        (__eo_to_smt
          (bvSignExtendUltConstAmount x
            (Term.Numeral (Int.ofNat (W + A)))))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hOne, hAmount]
  simp only [__smtx_model_eval_bvshl]
  rw [hMod]

private theorem sign_ult_all_ones_shift_mod (N H : Nat) (hHN : H < N) :
    native_mod_total
        (native_zmult (Int.ofNat (2 ^ N - 1))
          (native_int_pow2 (Int.ofNat H)))
        (native_int_pow2 (Int.ofNat N)) =
      Int.ofNat (2 ^ N - 2 ^ H) := by
  rw [native_int_pow2_nat_cast_sign_ult,
    native_int_pow2_nat_cast_sign_ult]
  have hPowPos : 0 < (2 : Int) ^ H := by
    exact_mod_cast Nat.two_pow_pos H
  have hPowLt : (2 : Int) ^ H < (2 : Int) ^ N := by
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < 2) hHN
  have hCalc :
      ((Int.ofNat (2 ^ N - 1)) * (2 : Int) ^ H) % (2 : Int) ^ N =
        (2 : Int) ^ N - (2 : Int) ^ H := by
    have hCastSub : (Int.ofNat (2 ^ N - 1) : Int) =
        (2 : Int) ^ N - 1 :=
      Int.ofNat_sub Nat.one_le_two_pow
    rw [hCastSub]
    have hEq :
        ((2 : Int) ^ N - 1) * (2 : Int) ^ H =
          ((2 : Int) ^ H - 1) * (2 : Int) ^ N +
            ((2 : Int) ^ N - (2 : Int) ^ H) := by
      calc
        ((2 : Int) ^ N - 1) * (2 : Int) ^ H =
            (2 : Int) ^ N * (2 : Int) ^ H - (2 : Int) ^ H := by
          rw [Int.sub_mul, Int.one_mul]
        _ = (2 : Int) ^ H * (2 : Int) ^ N - (2 : Int) ^ H := by
          rw [Int.mul_comm]
        _ = ((2 : Int) ^ H * (2 : Int) ^ N - (2 : Int) ^ N) +
              ((2 : Int) ^ N - (2 : Int) ^ H) := by
          generalize (2 : Int) ^ H * (2 : Int) ^ N = q
          omega
        _ = ((2 : Int) ^ H - 1) * (2 : Int) ^ N +
              ((2 : Int) ^ N - (2 : Int) ^ H) := by
          rw [Int.sub_mul, Int.one_mul]
    rw [hEq, Int.add_emod]
    have hMultiple :
        (((2 : Int) ^ H - 1) * (2 : Int) ^ N) % (2 : Int) ^ N = 0 := by
      simp
    rw [hMultiple, Int.zero_add]
    have hRemainder :
        ((2 : Int) ^ N - (2 : Int) ^ H) % (2 : Int) ^ N =
          (2 : Int) ^ N - (2 : Int) ^ H := by
      apply Int.emod_eq_of_lt
      · exact Int.sub_nonneg.mpr (Int.le_of_lt hPowLt)
      · exact Int.sub_lt_self _ hPowPos
    rw [hRemainder]
    exact hRemainder
  change
    ((Int.ofNat (2 ^ N - 1) : Int) * (2 : Int) ^ H) % (2 : Int) ^ N =
      Int.ofNat (2 ^ N - 2 ^ H)
  rw [hCalc]
  exact (Int.ofNat_sub (by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hHN))).symm

private theorem eval_sign_extend_ult_const_upper_bound
    (M : SmtModel) (x : Term) (W A : Nat) :
    0 < W ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConstUpperBound x
            (Term.Numeral (Int.ofNat (W + A))))) =
      SmtValue.Binary (Int.ofNat (W + A))
        (Int.ofNat (2 ^ (W + A) - 2 ^ (W - 1))) := by
  intro hW hXTy
  have hN : 0 < W + A := by omega
  have hZero := eval_sign_extend_ult_const_zero M (W + A)
  have hAmount := eval_sign_extend_ult_const_amount M x W A hW hXTy
  have hMaxMod :
      native_mod_total (native_int_pow2 (Int.ofNat (W + A)) - 1)
          (native_int_pow2 (Int.ofNat (W + A))) =
        Int.ofNat (2 ^ (W + A) - 1) := by
    rw [native_int_pow2_nat_cast_sign_ult]
    have hPowPos : (0 : Int) < 2 ^ (W + A) := by
      exact_mod_cast Nat.two_pow_pos (W + A)
    change ((2 : Int) ^ (W + A) - 1) % (2 : Int) ^ (W + A) =
      Int.ofNat (2 ^ (W + A) - 1)
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    exact (Int.ofNat_sub Nat.one_le_two_pow).symm
  have hNotZero :
      __smtx_model_eval_bvnot
          (SmtValue.Binary (Int.ofNat (W + A)) 0) =
        SmtValue.Binary (Int.ofNat (W + A))
          (Int.ofNat (2 ^ (W + A) - 1)) := by
    simp only [__smtx_model_eval_bvnot, SmtEval.native_binary_not,
      SmtEval.native_zplus, SmtEval.native_zneg]
    have hsimpa := hMaxMod
    try simp at hsimpa ⊢
    exact hsimpa
  have hShiftMod := sign_ult_all_ones_shift_mod
    (W + A) (W - 1) (by omega)
  unfold bvSignExtendUltConstUpperBound
  change __smtx_model_eval M
      (SmtTerm.bvshl
        (SmtTerm.bvnot
          (__eo_to_smt
            (bvSignExtendUltConstZero
              (Term.Numeral (Int.ofNat (W + A))))))
        (__eo_to_smt
          (bvSignExtendUltConstAmount x
            (Term.Numeral (Int.ofNat (W + A)))))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  change __smtx_model_eval_bvshl
      (__smtx_model_eval_bvnot
        (__smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstZero
              (Term.Numeral (Int.ofNat (W + A)))))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConstAmount x
            (Term.Numeral (Int.ofNat (W + A)))))) = _
  rw [hZero, hNotZero, hAmount]
  simpa [__smtx_model_eval_bvshl, hShiftMod]

private theorem sign_bit_extract_eq_zero
    (x : BitVec W) (hW : 0 < W) :
    decide (x.extractLsb' (W - 1) 1 = 0#1) =
      decide (x.msb = false) := by
  rw [decide_eq_decide]
  constructor
  · intro h
    have hBit := congrArg (fun z : BitVec 1 => z[0]) h
    simpa [BitVec.getElem_extractLsb', BitVec.getElem_zero,
      BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_eq_getElem (by omega)] using hBit
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [BitVec.getElem_extractLsb', BitVec.getElem_zero,
      BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_eq_getElem (by omega)] using h

private theorem eval_bvule_term_local
    (M : SmtModel) (x y : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) x) y)) =
      __smtx_model_eval_bvule
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  change __smtx_model_eval M
      (SmtTerm.bvule (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem sign_extend_ult_const_2_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A H : native_Int) :
    native_zleq 0 W = true -> native_zleq 0 A = true ->
    native_zleq 0 H = true -> native_zlt H W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    eo_interprets M
      (bvSignExtendUltConst2LowerPrem x c
        (Term.Numeral (native_zplus W A))) true ->
    eo_interprets M
      (bvSignExtendUltConst2UpperPrem x c
        (Term.Numeral (native_zplus W A))) true ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral H)) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst2Rhs x (Term.Numeral H))) := by
  intro hW0 hA0 hH0 hHW hXSmtTy hConstSmtTy
    hLowerPrem hUpperPrem hWidthPrem
  have hHEq := bv_sign_extend_eq_const_nm2_numeric
    M x W H hW0 hXSmtTy hWidthPrem
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWRound : (Int.ofNat WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hARound : (Int.ofNat AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hWNatPos : 0 < WN := by
    have hHNonneg : (0 : Int) ≤ H := by
      change decide ((0 : Int) ≤ H) = true at hH0
      exact of_decide_eq_true hH0
    have hHLt : H < W := by
      change decide (H < W) = true at hHW
      exact of_decide_eq_true hHW
    have hWPos : (0 : Int) < W := Int.lt_of_le_of_lt hHNonneg hHLt
    have hWNatPosInt : (0 : Int) < Int.ofNat WN := by
      rw [hWRound]
      exact hWPos
    exact Int.natCast_pos.mp hWNatPosInt
  have hHCast : H = Int.ofNat (WN - 1) := by
    have hSub : H = W - 1 := by
      have hsimpa := hHEq
      try simp [SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
      exact hsimpa
    rw [← hWRound] at hSub
    calc
      H = (Int.ofNat WN : Int) - 1 := hSub
      _ = Int.ofNat (WN - 1) :=
        (Int.ofNat_sub (by omega : 1 ≤ WN)).symm
  have hWideCast :
      (Int.ofNat (WN + AN) : Int) = native_zplus W A := by
    calc
      (Int.ofNat (WN + AN) : Int) =
          (Int.ofNat WN : Int) + Int.ofNat AN := rfl
      _ = W + A := by rw [hWRound, hARound]
      _ = native_zplus W A := rfl
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    apply decide_eq_true
    have hWNonneg : (0 : Int) ≤ W := of_decide_eq_true hW0
    have hANonneg : (0 : Int) ≤ A := of_decide_eq_true hA0
    simpa [SmtEval.native_zplus] using Int.add_nonneg hWNonneg hANonneg
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    have hRound := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    have hRound' :
        (Int.ofNat (native_int_to_nat (native_zplus W A)) : Int) =
          native_zplus W A := by
      simpa [Smtm.native_nat_to_int, native_nat_to_int] using hRound
    exact Int.ofNat.inj (hRound'.trans hWideCast.symm)
  have hXSmtTyNat : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec WN := by
    simpa [WN] using hXSmtTy
  have hConstSmtTyNat :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (Int.ofNat (WN + AN))))) =
        SmtType.BitVec (WN + AN) := by
    rw [hWideCast, ← hWideNat]
    exact hConstSmtTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      hXSmtTyNat with ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (Int.ofNat WN) px := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, Smtm.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] using
      hXRange.2
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (Int.ofNat (WN + AN))))) (WN + AN)
      hConstSmtTyNat with ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (Int.ofNat (WN + AN))))) =
        SmtValue.Binary (Int.ofNat (WN + AN)) pc := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (Int.ofNat (WN + AN) : Int) :=
        Int.natCast_nonneg _
      have hsimpa := hnn; (try simp [SmtEval.native_zleq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢); exact decide_eq_true hsimpa) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    have hsimpa :=
      hConstRange.2
    try simp [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hXPayload : (Int.ofNat xBV.toNat : Int) = px := by
    have hToNat := ofInt_toNat_canonical WN px hPx0 hPx1
    simp [xBV, hToNat, Int.toNat_of_nonneg hPx0]
  have hConstPayload : (Int.ofNat cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hXEvalBV :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (Int.ofNat WN) (Int.ofNat xBV.toNat) := by
    rw [hXEval', hXPayload]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (Int.ofNat (WN + AN))))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat cBV.toNat) := by
    rw [hConstEval', hConstPayload]
  have hLowerBoundEval :=
    eval_sign_extend_ult_const_lower_bound M x WN AN hWNatPos hXSmtTyNat
  have hUpperBoundEval :=
    eval_sign_extend_ult_const_upper_bound M x WN AN hWNatPos hXSmtTyNat
  have hLowerRel := RuleProofs.eo_interprets_eq_rel M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvult)
        (bvSignExtendUltConstLowerBound x
          (Term.Numeral (native_zplus W A))))
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A))))
    (Term.Boolean true)
    (by simpa [bvSignExtendUltConst2LowerPrem] using hLowerPrem)
  have hLowerCmpEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvult)
                (bvSignExtendUltConstLowerBound x
                  (Term.Numeral (native_zplus W A))))
              (bvZeroExtendUltConstConst c
                (Term.Numeral (native_zplus W A))))) =
        SmtValue.Boolean
          (decide (2 ^ (WN - 1) < cBV.toNat)) := by
    rw [eval_bvult_term_local]
    rw [show __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstLowerBound x
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (2 ^ (WN - 1))) by
      simpa only [← hWideCast] using hLowerBoundEval]
    rw [show __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat cBV.toNat) by
      simpa only [← hWideCast] using hConstEvalBV]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
    norm_cast
  rw [hLowerCmpEval] at hLowerRel
  have hLowerValueEq :
      SmtValue.Boolean (decide (2 ^ (WN - 1) < cBV.toNat)) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp (by have hsimpa := hLowerRel; (try simp at hsimpa ⊢); exact hsimpa)
  have hLowerDec : decide (2 ^ (WN - 1) < cBV.toNat) = true := by
    injection hLowerValueEq
  have hLower : 2 ^ (WN - 1) < cBV.toNat := of_decide_eq_true hLowerDec
  have hUpperRel := RuleProofs.eo_interprets_eq_rel M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))))
      (bvSignExtendUltConstUpperBound x
        (Term.Numeral (native_zplus W A))))
    (Term.Boolean true)
    (by simpa [bvSignExtendUltConst2UpperPrem] using hUpperPrem)
  have hUpperCmpEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvule)
                (bvZeroExtendUltConstConst c
                  (Term.Numeral (native_zplus W A))))
              (bvSignExtendUltConstUpperBound x
                (Term.Numeral (native_zplus W A))))) =
        SmtValue.Boolean
          (decide (cBV.toNat ≤ 2 ^ (WN + AN) - 2 ^ (WN - 1))) := by
    rw [eval_bvule_term_local]
    rw [show __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat cBV.toNat) by
      simpa only [← hWideCast] using hConstEvalBV]
    rw [show __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstUpperBound x
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (2 ^ (WN + AN) - 2 ^ (WN - 1))) by
      simpa only [← hWideCast] using hUpperBoundEval]
    simp only [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
      __smtx_model_eval_bvugt, __smtx_model_eval_or,
      __smtx_model_eval_eq, SmtEval.native_zlt, native_veq,
      SmtEval.native_or]
    let U : Nat := 2 ^ (WN + AN) - 2 ^ (WN - 1)
    change SmtValue.Boolean
        (decide ((Int.ofNat cBV.toNat : Int) < Int.ofNat U) ||
          decide
            (SmtValue.Binary (Int.ofNat (WN + AN)) (Int.ofNat U) =
              SmtValue.Binary (Int.ofNat (WN + AN))
                (Int.ofNat cBV.toNat))) =
      SmtValue.Boolean (decide (cBV.toNat ≤ U))
    congr 1
    rw [← Bool.decide_or, decide_eq_decide]
    constructor
    · intro h
      rcases h with hLt | hEq
      · exact Nat.le_of_lt (Int.ofNat_lt.mp hLt)
      · have hPayload : Int.ofNat U = Int.ofNat cBV.toNat := by
          injection hEq
        exact Nat.le_of_eq (Int.ofNat.inj hPayload).symm
    · intro hLe
      by_cases hEq : cBV.toNat = U
      · right
        rw [← hEq]
      · left
        apply Int.ofNat_lt.mpr
        omega
  rw [hUpperCmpEval] at hUpperRel
  have hUpperValueEq :
      SmtValue.Boolean
          (decide (cBV.toNat ≤ 2 ^ (WN + AN) - 2 ^ (WN - 1))) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp (by have hsimpa := hUpperRel; (try simp at hsimpa ⊢); exact hsimpa)
  have hUpperDec :
      decide (cBV.toNat ≤ 2 ^ (WN + AN) - 2 ^ (WN - 1)) = true := by
    injection hUpperValueEq
  have hUpper : cBV.toNat ≤ 2 ^ (WN + AN) - 2 ^ (WN - 1) :=
    of_decide_eq_true hUpperDec
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (xBV.signExtend (WN + AN)).toNat) := by
    rw [eval_sign_extend_term_local, hXEval']
    rw [← hARound]
    have hSign := sign_extend_val_bitvec WN AN px hPx0 hPx1
    rw [Nat.add_comm AN WN] at hSign
    exact hSign
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst2Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Boolean
          (decide ((xBV.signExtend (WN + AN)).toNat < cBV.toNat)) := by
    unfold bvSignExtendUltConst2Lhs
    rw [eval_bvult_term_local, hSignEval]
    rw [show __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat cBV.toNat) by
      simpa only [← hWideCast] using hConstEvalBV]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
  have hSignBitEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstSignBit x (Term.Numeral H))) =
        SmtValue.Binary 1
          (Int.ofNat (xBV.extractLsb' (WN - 1) 1).toNat) := by
    unfold bvSignExtendUltConstSignBit
    rw [eval_extract_term, hXEval']
    rw [show H = Int.ofNat (WN - 1) by exact hHCast]
    simpa [xBV] using
      extract_val_bitvec_start_len WN (WN - 1) 1 px
        (Int.ofNat (WN - 1)) (Int.ofNat (WN - 1))
        hPx0 hPx1 rfl (by push_cast; omega)
  have hZeroBitEval :
      __smtx_model_eval M (__eo_to_smt (bvSignExtendUltConstBit 0)) =
        SmtValue.Binary 1 (Int.ofNat (0#1).toNat) := by
    unfold bvSignExtendUltConstBit bvZeroExtendUltConstConst
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)) = _
    rw [smtx_eval_int_to_bv_numerals]
    rfl
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst2Rhs x (Term.Numeral H))) =
        SmtValue.Boolean
          (decide (xBV.extractLsb' (WN - 1) 1 = 0#1)) := by
    unfold bvSignExtendUltConst2Rhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvSignExtendUltConstSignBit x (Term.Numeral H)))
          (__eo_to_smt (bvSignExtendUltConstBit 0))) = _
    rw [smtx_eval_eq_term_eq, hSignBitEval, hZeroBitEval]
    exact smt_eval_eq_bitvec_values _ _
  rw [hLhsEval, hRhsEval,
    sign_extend_ult_middle_range xBV cBV hWNatPos hLower hUpper,
    sign_bit_extract_eq_zero xBV hWNatPos]

private theorem facts_bv_sign_extend_ult_const_2_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvSignExtendUltConst2LowerPrem x c nm) true ->
    eo_interprets M (bvSignExtendUltConst2UpperPrem x c nm) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvSignExtendUltConst2Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
    hLowerPrem hUpperPrem hWidthPrem
  have hBool := typed_bv_sign_extend_ult_const_2_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_sign_extend_ult_const_2_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hH0, hHW,
      hXSmtTy, hConstSmtTy, _hSignSmtTy, _hBitSmtTy, _hZeroBitSmtTy⟩
  unfold bvSignExtendUltConst2Term bvZeroExtendEqConstEq
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSignExtendUltConst2Term, bvZeroExtendEqConstEq] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst2Rhs x (Term.Numeral H))))
    rw [sign_extend_ult_const_2_eval_eq M hM x c W A H
      hW0 hA0 hH0 hHW hXSmtTy hConstSmtTy
      (by simpa using hLowerPrem) (by simpa using hUpperPrem)
      (by simpa using hWidthPrem)]
    exact RuleProofs.smt_value_rel_refl _

def bvSignExtendUltConst2Program
    (x m c nm nm2 P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_sign_extend_ult_const_2 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private def bvSignExtendUltConst2LowerPremRefs
    (nmOne nmAmount x nmConst c : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvult)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvshl)
            (bvSignExtendUltConstOne nmOne))
          (bvSignExtendUltConstAmount x nmAmount)))
      (bvZeroExtendUltConstConst c nmConst))
    (Term.Boolean true)

private def bvSignExtendUltConst2UpperPremRefs
    (nmConst c nmZero nmAmount x : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvZeroExtendUltConstConst c nmConst))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.bvshl)
          (Term.Apply (Term.UOp UserOp.bvnot)
            (bvSignExtendUltConstZero nmZero)))
        (bvSignExtendUltConstAmount x nmAmount)))
    (Term.Boolean true)

private def bvSignExtendUltConst2Guard
    (x c nm nm2 nmL1 nmL2 xL nmL3 cL
      nmU1 cU nmU2 nmU3 xU nm2W xW : Term) : Term :=
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
                      (__eo_and (__eo_eq nm nmL1) (__eo_eq nm nmL2))
                      (__eo_eq x xL))
                    (__eo_eq nm nmL3))
                  (__eo_eq c cL))
                (__eo_eq nm nmU1))
              (__eo_eq c cU))
            (__eo_eq nm nmU2))
          (__eo_eq nm nmU3))
        (__eo_eq x xU))
      (__eo_eq nm2 nm2W))
    (__eo_eq x xW)

private theorem bv_sign_extend_ult_const_2_guard_refs
    {x c nm nm2 nmL1 nmL2 xL nmL3 cL
      nmU1 cU nmU2 nmU3 xU nm2W xW body : Term} :
    __eo_requires
        (bvSignExtendUltConst2Guard x c nm nm2 nmL1 nmL2 xL nmL3 cL
          nmU1 cU nmU2 nmU3 xU nm2W xW)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nmL1 = nm ∧ nmL2 = nm ∧ xL = x ∧ nmL3 = nm ∧ cL = c ∧
      nmU1 = nm ∧ cU = c ∧ nmU2 = nm ∧ nmU3 = nm ∧ xU = x ∧
      nm2W = nm2 ∧ xW = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvSignExtendUltConst2Guard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG11, hXW⟩
  rcases bv_extract_support_and_true hG11 with ⟨hG10, hNm2W⟩
  rcases bv_extract_support_and_true hG10 with ⟨hG9, hXU⟩
  rcases bv_extract_support_and_true hG9 with ⟨hG8, hNmU3⟩
  rcases bv_extract_support_and_true hG8 with ⟨hG7, hNmU2⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hCU⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hNmU1⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hCL⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hNmL3⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hXL⟩
  rcases bv_extract_support_and_true hG2 with ⟨hNmL1, hNmL2⟩
  exact ⟨(bv_extract_support_eq_true hNmL1).symm,
    (bv_extract_support_eq_true hNmL2).symm,
    (bv_extract_support_eq_true hXL).symm,
    (bv_extract_support_eq_true hNmL3).symm,
    (bv_extract_support_eq_true hCL).symm,
    (bv_extract_support_eq_true hNmU1).symm,
    (bv_extract_support_eq_true hCU).symm,
    (bv_extract_support_eq_true hNmU2).symm,
    (bv_extract_support_eq_true hNmU3).symm,
    (bv_extract_support_eq_true hXU).symm,
    (bv_extract_support_eq_true hNm2W).symm,
    (bv_extract_support_eq_true hXW).symm⟩

private theorem bv_sign_extend_ult_const_2_premise_shape
    (x m c nm nm2 P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3 ≠ Term.Stuck ->
    ∃ nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU nm2W xW,
      P1 = bvSignExtendUltConst2LowerPremRefs nmL1 nmL2 xL nmL3 cL ∧
      P2 = bvSignExtendUltConst2UpperPremRefs nmU1 cU nmU2 nmU3 xU ∧
      P3 = bvZeroExtendUltConstWidthPrem xW nm2W := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU nm2W xW,
        P1 = bvSignExtendUltConst2LowerPremRefs nmL1 nmL2 xL nmL3 cL ∧
        P2 = bvSignExtendUltConst2UpperPremRefs nmU1 cU nmU2 nmU3 xU ∧
        P3 = bvZeroExtendUltConstWidthPrem xW nm2W
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_ult_const_2.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hM hC hNm hNm2 (by
        intro nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU nm2W xW
          hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨nmL1, nmL2, xL, nmL3, cL, nmU1, cU, nmU2, nmU3, xU,
            nm2W, xW, rfl, rfl, rfl⟩)

private theorem bv_sign_extend_ult_const_2_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst2Program x m c nm nm2
        (bvSignExtendUltConst2LowerPrem x c nm)
        (bvSignExtendUltConst2UpperPrem x c nm)
        (bvZeroExtendUltConstWidthPrem x nm2) =
      bvSignExtendUltConst2Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvSignExtendUltConst2Program bvSignExtendUltConst2LowerPrem
    bvSignExtendUltConst2UpperPrem bvZeroExtendUltConstWidthPrem
    bvSignExtendUltConstLowerBound bvSignExtendUltConstUpperBound
    bvSignExtendUltConstOne bvSignExtendUltConstZero
    bvSignExtendUltConstAmount bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstConst
  rw [__eo_prog_bv_sign_extend_ult_const_2.eq_6
    x m c nm nm2 nm nm x nm c nm c nm nm x nm2 x
    hX hM hC hNm hNm2]
  simp [bvSignExtendUltConst2Guard, bvSignExtendUltConst2Term,
    bvSignExtendUltConst2Lhs, bvSignExtendUltConst2Rhs,
    bvSignExtendEqConstSign, bvSignExtendUltConstSignBit,
    bvSignExtendUltConstBit, bvZeroExtendEqConstEq,
    bvZeroExtendUltConstConst, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bvSignExtendUltConst2Program_normalize
    (x m c nm nm2 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvSignExtendUltConst2LowerPrem x c nm ∧
      P2 = bvSignExtendUltConst2UpperPrem x c nm ∧
      P3 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3 =
        bvSignExtendUltConst2Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_sign_extend_ult_const_2_premise_shape
      x m c nm nm2 P1 P2 P3 hX hM hC hNm hNm2 hProg with
    ⟨nmL1, nmL2, xL, nmL3, cL, nmU1, cU, nmU2, nmU3, xU,
      nm2W, xW, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvSignExtendUltConst2Program bvSignExtendUltConst2LowerPremRefs
    bvSignExtendUltConst2UpperPremRefs bvZeroExtendUltConstWidthPrem
    bvSignExtendUltConstOne bvSignExtendUltConstZero
    bvSignExtendUltConstAmount bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstConst bvZeroExtendEqConstEq at hReq
  rw [__eo_prog_bv_sign_extend_ult_const_2.eq_6
    x m c nm nm2 nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU
    nm2W xW hX hM hC hNm hNm2] at hReq
  rcases bv_sign_extend_ult_const_2_guard_refs
      (by simpa [bvSignExtendUltConst2Guard] using hReq) with
    ⟨hNmL1, hNmL2, hXL, hNmL3, hCL, hNmU1, hCU, hNmU2, hNmU3,
      hXU, hNm2W, hXW⟩
  subst nmL1
  subst nmL2
  subst xL
  subst nmL3
  subst cL
  subst nmU1
  subst cU
  subst nmU2
  subst nmU3
  subst xU
  subst nm2W
  subst xW
  have hP1Canonical : P1 = bvSignExtendUltConst2LowerPrem x c nm := by
    have hsimpa := hP1
    try simp [bvSignExtendUltConst2LowerPrem, bvSignExtendUltConst2LowerPremRefs, bvSignExtendUltConstLowerBound] at hsimpa ⊢
    exact hsimpa
  have hP2Canonical : P2 = bvSignExtendUltConst2UpperPrem x c nm := by
    have hsimpa := hP2
    try simp [bvSignExtendUltConst2UpperPrem, bvSignExtendUltConst2UpperPremRefs, bvSignExtendUltConstUpperBound] at hsimpa ⊢
    exact hsimpa
  have hP3Canonical : P3 = bvZeroExtendUltConstWidthPrem x nm2 := hP3
  refine ⟨hP1Canonical, hP2Canonical, hP3Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical, hP3Canonical]
  exact bv_sign_extend_ult_const_2_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

theorem typed_bv_sign_extend_ult_const_2_program
    (x m c nm nm2 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst2Program_normalize x m c nm nm2 P1 P2 P3
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst2Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_ult_const_2_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_sign_extend_ult_const_2_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvSignExtendUltConst2Program x m c nm nm2 P1 P2 P3) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst2Program_normalize x m c nm nm2 P1 P2 P3
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst2Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLowerPrem :
      eo_interprets M (bvSignExtendUltConst2LowerPrem x c nm) true := by
    simpa [hP1] using hP1True
  have hUpperPrem :
      eo_interprets M (bvSignExtendUltConst2UpperPrem x c nm) true := by
    simpa [hP2] using hP2True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_sign_extend_ult_const_2_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy
    hLowerPrem hUpperPrem hWidthPrem

/-! Support for the complementary middle-range `bv_sign_extend_ult_const_4`. -/

def bvSignExtendUltConst4LowerBound (x nm : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot)
    (bvSignExtendUltConstUpperBound x nm)

def bvSignExtendUltConst4UpperBound (x nm : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot)
    (bvSignExtendUltConstLowerBound x nm)

def bvSignExtendUltConst4LowerPrem (x c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvSignExtendUltConst4LowerBound x nm))
      (bvZeroExtendUltConstConst c nm))
    (Term.Boolean true)

def bvSignExtendUltConst4UpperPrem (x c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvZeroExtendUltConstConst c nm))
      (bvSignExtendUltConst4UpperBound x nm))
    (Term.Boolean true)

def bvSignExtendUltConst4Lhs (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstConst c nm))
    (bvSignExtendEqConstSign x m)

def bvSignExtendUltConst4Rhs (x nm2 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendUltConstSignBit x nm2)
    (bvSignExtendUltConstBit 1)

def bvSignExtendUltConst4Term (x m c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendUltConst4Lhs x m c nm)
    (bvSignExtendUltConst4Rhs x nm2)

private theorem sign_extend_ult_middle_range_rev
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W)
    (hLower : 2 ^ (W - 1) - 1 ≤ c.toNat)
    (hUpper : c.toNat ≤ 2 ^ (W + A) - 2 ^ (W - 1) - 1) :
    decide (c.toNat < (x.signExtend (W + A)).toNat) =
      decide (x.msb = true) := by
  have hWWide : W ≤ W + A := by omega
  have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
    calc
      2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
  have hPowMono : 2 ^ W ≤ 2 ^ (W + A) :=
    Nat.pow_le_pow_right (by decide) hWWide
  have hHalfPos : 0 < 2 ^ (W - 1) := Nat.two_pow_pos _
  cases hx : x.msb
  · have hTwoLt : 2 * x.toNat < 2 ^ W :=
      BitVec.msb_eq_false_iff_two_mul_lt.mp hx
    have hXLt : x.toNat < 2 ^ (W - 1) := by omega
    have hSignNat : (x.signExtend (W + A)).toNat = x.toNat := by
      rw [BitVec.signExtend_eq_setWidth_of_msb_false hx,
        BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le x.isLt hPowMono
    have hNotLt : ¬c.toNat < (x.signExtend (W + A)).toNat := by
      rw [hSignNat]
      omega
    simp [hx, hNotLt]
  · have hTwoGe : 2 ^ W ≤ 2 * x.toNat :=
      BitVec.msb_eq_true_iff_two_mul_ge.mp hx
    have hXGe : 2 ^ (W - 1) ≤ x.toNat := by omega
    have hXWide : x.toNat < 2 ^ (W + A) :=
      Nat.lt_of_lt_of_le x.isLt hPowMono
    have hSignNat :
        (x.signExtend (W + A)).toNat =
          x.toNat + (2 ^ (W + A) - 2 ^ W) := by
      rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt hXWide, hx]
      rfl
    have hSignLower :
        2 ^ (W + A) - 2 ^ (W - 1) ≤
          (x.signExtend (W + A)).toNat := by
      rw [hSignNat]
      omega
    have hLt : c.toNat < (x.signExtend (W + A)).toNat := by
      omega
    simp [hx, hLt]

private theorem sign_ult_not_nat_value
    (N v : Nat) (hV : v < 2 ^ N) :
    native_mod_total
        (native_binary_not (Int.ofNat N) (Int.ofNat v))
        (native_int_pow2 (Int.ofNat N)) =
      Int.ofNat (2 ^ N - v - 1) := by
  unfold SmtEval.native_binary_not
  simp only [SmtEval.native_zplus, SmtEval.native_zneg,
    native_int_pow2_nat_cast_sign_ult]
  have hOneLe : 1 ≤ 2 ^ N - v := by omega
  have hFirstCast :
      (Int.ofNat (2 ^ N - v) : Int) =
        (2 : Int) ^ N - Int.ofNat v :=
    Int.ofNat_sub (Nat.le_of_lt hV)
  have hCast :
      (Int.ofNat (2 ^ N - v - 1) : Int) =
        (2 : Int) ^ N - Int.ofNat v - 1 := by
    calc
      (Int.ofNat (2 ^ N - v - 1) : Int) =
          Int.ofNat (2 ^ N - v) - 1 :=
        Int.ofNat_sub hOneLe
      _ = ((2 : Int) ^ N - Int.ofNat v) - 1 :=
        congrArg (fun z : Int => z - 1) hFirstCast
      _ = (2 : Int) ^ N - Int.ofNat v - 1 := rfl
  rw [show (2 : Int) ^ N + -(Int.ofNat v + 1) =
      (2 : Int) ^ N - Int.ofNat v - 1 by omega]
  unfold SmtEval.native_mod_total
  change ((2 : Int) ^ N - Int.ofNat v - 1) % (2 : Int) ^ N = _
  rw [Int.emod_eq_of_lt]
  · exact hCast.symm
  · rw [← hCast]
    exact Int.natCast_nonneg _
  · have hV0 : (0 : Int) ≤ Int.ofNat v := Int.natCast_nonneg _
    omega

private theorem eval_sign_extend_ult_const_not_lower_bound
    (M : SmtModel) (x : Term) (W A : Nat) :
    0 < W ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst4UpperBound x
            (Term.Numeral (Int.ofNat (W + A))))) =
      SmtValue.Binary (Int.ofNat (W + A))
        (Int.ofNat (2 ^ (W + A) - 2 ^ (W - 1) - 1)) := by
  intro hW hXTy
  have hLower := eval_sign_extend_ult_const_lower_bound M x W A hW hXTy
  have hPowLt : 2 ^ (W - 1) < 2 ^ (W + A) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  unfold bvSignExtendUltConst4UpperBound
  rw [eval_bvnot_term_local, hLower]
  simp only [__smtx_model_eval_bvnot]
  rw [sign_ult_not_nat_value (W + A) (2 ^ (W - 1)) hPowLt]

private theorem eval_sign_extend_ult_const_not_upper_bound
    (M : SmtModel) (x : Term) (W A : Nat) :
    0 < W ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst4LowerBound x
            (Term.Numeral (Int.ofNat (W + A))))) =
      SmtValue.Binary (Int.ofNat (W + A))
        (Int.ofNat (2 ^ (W - 1) - 1)) := by
  intro hW hXTy
  have hUpper := eval_sign_extend_ult_const_upper_bound M x W A hW hXTy
  have hHalfPos : 0 < 2 ^ (W - 1) := Nat.two_pow_pos _
  have hHalfLt : 2 ^ (W - 1) < 2 ^ (W + A) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hValueLt :
      2 ^ (W + A) - 2 ^ (W - 1) < 2 ^ (W + A) := by omega
  have hNot := sign_ult_not_nat_value (W + A)
    (2 ^ (W + A) - 2 ^ (W - 1)) hValueLt
  have hResult :
      2 ^ (W + A) - (2 ^ (W + A) - 2 ^ (W - 1)) - 1 =
        2 ^ (W - 1) - 1 := by omega
  unfold bvSignExtendUltConst4LowerBound
  rw [eval_bvnot_term_local, hUpper]
  simp only [__smtx_model_eval_bvnot]
  rw [hNot, hResult]

private theorem bv_sign_extend_ult_const_4_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst4Term x m c nm nm2) = Term.Bool ->
    ∃ W A H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 H = true ∧ native_zlt H W = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvSignExtendUltConstSignBit x nm2)) =
        SmtType.BitVec 1 ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendUltConstBit 1)) =
        SmtType.BitVec 1 := by
  intro hXTrans _hMTrans hCTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstConst c nm))
        (__eo_typeof (bvSignExtendEqConstSign x m)))
      (__eo_typeof_eq
        (__eo_typeof (bvSignExtendUltConstSignBit x nm2))
        (__eo_typeof (bvSignExtendUltConstBit 1))) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hLhsNe with
    ⟨wideTerm, hConstEoTy, hSignEoTy⟩
  have hRhsTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hRhsNe
  have hRhsSides := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hRhsTy
  have hBitNe :
      __eo_typeof (bvSignExtendUltConstSignBit x nm2) ≠ Term.Stuck :=
    hRhsSides.1
  rcases bv_extract_context_of_non_stuck x nm2 nm2 hXTrans
      (by simpa [bvSignExtendUltConstSignBit] using hBitNe) with
    ⟨W, H, L, hXEoTy, hNm2High, hNm2Low, hW0, hL0, hHW,
      hD0, hXSmtTy⟩
  have hHL : L = H := by
    rw [hNm2High] at hNm2Low
    injection hNm2Low with h
    exact h.symm
  subst L
  subst nm2
  rcases sign_extend_index_context x m wideTerm W hXEoTy hSignEoTy with
    ⟨A, hM, hA0, hWideTerm⟩
  subst m
  subst wideTerm
  have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_all_ones_const_context c nm
      (Term.Numeral (native_zplus W A)) hCNe hNmNe
      (by simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
        hConstEoTy) with
    ⟨N, hNm, hWidthN, hN0, hCTy⟩
  have hN : N = native_zplus W A := by
    injection hWidthN with h
    exact h.symm
  subst N
  subst nm
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c (Term.UOp UserOp.Int) (__eo_to_smt c) rfl hCTrans hCTy
  have hConstSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type c (native_zplus W A)
        hCSmtTy hN0
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    have hRaw := smt_typeof_sign_extend_of_context x W A
      hXSmtTy hW0 hA0
    have hComm : native_zplus A W = native_zplus W A := by
      simp [SmtEval.native_zplus, Int.add_comm]
    simpa [bvSignExtendEqConstSign, hComm] using hRaw
  have hBitSmtTyRaw :=
    smt_typeof_extract_of_context x W H H hXSmtTy hW0 hL0 hHW hD0
  have hBitSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConstSignBit x (Term.Numeral H))) =
        SmtType.BitVec 1 := by
    have hWidthOne :
        native_int_to_nat
            (native_zplus (native_zplus H 1) (native_zneg H)) = 1 := by
      have hEq : native_zplus (native_zplus H 1) (native_zneg H) = 1 := by
        simp only [SmtEval.native_zplus, SmtEval.native_zneg]
        have hCancel : H + -H = 0 := by
          simpa using (Int.add_neg_cancel_right (0 : Int) H)
        calc
          H + 1 + -H = H + -H + 1 := by ac_rfl
          _ = 1 := by rw [hCancel, Int.zero_add]
      rw [hEq]
      rfl
    simpa [bvSignExtendUltConstSignBit, hWidthOne] using hBitSmtTyRaw
  have hOneBitSmtTy :
      __smtx_typeof (__eo_to_smt (bvSignExtendUltConstBit 1)) =
        SmtType.BitVec 1 := by
    have hsimpa :=
      smt_typeof_bv_const_of_int_type (Term.Numeral 1) 1 rfl (by decide)
    try simp [bvSignExtendUltConstBit, bvZeroExtendUltConstConst] at hsimpa ⊢
    exact hsimpa
  exact ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hL0, hHW,
    hXSmtTy, hConstSmtTy, hSignSmtTy, hBitSmtTy, hOneBitSmtTy⟩

private theorem typed_bv_sign_extend_ult_const_4_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst4Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst4Term x m c nm nm2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_sign_extend_ult_const_4_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, H, rfl, rfl, rfl, _hW0, _hA0, _hH0, _hHW,
      _hXSmtTy, hConstSmtTy, hSignSmtTy, hBitSmtTy, hOneBitSmtTy⟩
  have hLhsSmtTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstConst c (Term.Numeral (native_zplus W A)))
    (bvSignExtendEqConstSign x (Term.Numeral A))
    (native_int_to_nat (native_zplus W A)) hConstSmtTy hSignSmtTy
  have hRhsBool : RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst4Rhs x (Term.Numeral H)) := by
    unfold bvSignExtendUltConst4Rhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hBitSmtTy.trans hOneBitSmtTy.symm)
      (by rw [hBitSmtTy]; intro h; cases h)
  have hRhsSmtTy :
      __smtx_typeof
          (__eo_to_smt (bvSignExtendUltConst4Rhs x (Term.Numeral H))) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hRhsBool
  unfold bvSignExtendUltConst4Term bvZeroExtendEqConstEq
  have hLhsNN :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConst4Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) ≠ SmtType.None := by
    rw [show __smtx_typeof
        (__eo_to_smt
          (bvSignExtendUltConst4Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) = SmtType.Bool by
      simpa [bvSignExtendUltConst4Lhs] using hLhsSmtTy]
    intro h
    cases h
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvSignExtendUltConst4Lhs] using
      hLhsSmtTy.trans hRhsSmtTy.symm)
    hLhsNN

private theorem eval_bvule_binary_nat
    (N a b : Nat) :
    __smtx_model_eval_bvule
        (SmtValue.Binary (Int.ofNat N) (Int.ofNat a))
        (SmtValue.Binary (Int.ofNat N) (Int.ofNat b)) =
      SmtValue.Boolean (decide (a ≤ b)) := by
  simp only [__smtx_model_eval_bvule, __smtx_model_eval_bvuge,
    __smtx_model_eval_bvugt, __smtx_model_eval_or,
    __smtx_model_eval_eq, SmtEval.native_zlt, native_veq,
    SmtEval.native_or]
  congr 1
  rw [← Bool.decide_or, decide_eq_decide]
  constructor
  · intro h
    rcases h with hLt | hEq
    · exact Nat.le_of_lt (Int.ofNat_lt.mp hLt)
    · have hPayload : Int.ofNat b = Int.ofNat a := by injection hEq
      exact Nat.le_of_eq (Int.ofNat.inj hPayload).symm
  · intro hLe
    by_cases hEq : a = b
    · right
      rw [hEq]
    · left
      exact Int.ofNat_lt.mpr (by omega)

private theorem sign_bit_extract_eq_one
    (x : BitVec W) (hW : 0 < W) :
    decide (x.extractLsb' (W - 1) 1 = 1#1) =
      decide (x.msb = true) := by
  rw [decide_eq_decide]
  constructor
  · intro h
    have hBit := congrArg (fun z : BitVec 1 => z[0]) h
    simpa [BitVec.getElem_extractLsb', BitVec.getElem_one,
      BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_eq_getElem (by omega)] using hBit
  · intro h
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [BitVec.getElem_extractLsb', BitVec.getElem_one,
      BitVec.msb_eq_getLsbD_last,
      BitVec.getLsbD_eq_getElem (by omega)] using h

private theorem sign_extend_ult_const_4_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A H : native_Int) :
    native_zleq 0 W = true -> native_zleq 0 A = true ->
    native_zleq 0 H = true -> native_zlt H W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    eo_interprets M
      (bvSignExtendUltConst4LowerPrem x c
        (Term.Numeral (native_zplus W A))) true ->
    eo_interprets M
      (bvSignExtendUltConst4UpperPrem x c
        (Term.Numeral (native_zplus W A))) true ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral H)) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst4Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst4Rhs x (Term.Numeral H))) := by
  intro hW0 hA0 hH0 hHW hXSmtTy hConstSmtTy
    hLowerPrem hUpperPrem hWidthPrem
  have hHEq := bv_sign_extend_eq_const_nm2_numeric
    M x W H hW0 hXSmtTy hWidthPrem
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWRound : (Int.ofNat WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hARound : (Int.ofNat AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hWNatPos : 0 < WN := by
    have hHNonneg : (0 : Int) ≤ H := by
      change decide ((0 : Int) ≤ H) = true at hH0
      exact of_decide_eq_true hH0
    have hHLt : H < W := by
      change decide (H < W) = true at hHW
      exact of_decide_eq_true hHW
    have hWPos : (0 : Int) < W := Int.lt_of_le_of_lt hHNonneg hHLt
    have hWNatPosInt : (0 : Int) < Int.ofNat WN := by
      rw [hWRound]
      exact hWPos
    exact Int.natCast_pos.mp hWNatPosInt
  have hHCast : H = Int.ofNat (WN - 1) := by
    have hSub : H = W - 1 := by
      have hsimpa := hHEq
      try simp [SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
      exact hsimpa
    rw [← hWRound] at hSub
    calc
      H = (Int.ofNat WN : Int) - 1 := hSub
      _ = Int.ofNat (WN - 1) :=
        (Int.ofNat_sub (by omega : 1 ≤ WN)).symm
  have hWideCast :
      (Int.ofNat (WN + AN) : Int) = native_zplus W A := by
    calc
      (Int.ofNat (WN + AN) : Int) =
          (Int.ofNat WN : Int) + Int.ofNat AN := rfl
      _ = W + A := by rw [hWRound, hARound]
      _ = native_zplus W A := rfl
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    apply decide_eq_true
    have hWNonneg : (0 : Int) ≤ W := of_decide_eq_true hW0
    have hANonneg : (0 : Int) ≤ A := of_decide_eq_true hA0
    simpa [SmtEval.native_zplus] using Int.add_nonneg hWNonneg hANonneg
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    have hRound := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    have hRound' :
        (Int.ofNat (native_int_to_nat (native_zplus W A)) : Int) =
          native_zplus W A := by
      simpa [Smtm.native_nat_to_int, native_nat_to_int] using hRound
    exact Int.ofNat.inj (hRound'.trans hWideCast.symm)
  have hXSmtTyNat : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec WN := by
    simpa [WN] using hXSmtTy
  have hConstSmtTyNat :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (Int.ofNat (WN + AN))))) =
        SmtType.BitVec (WN + AN) := by
    rw [hWideCast, ← hWideNat]
    exact hConstSmtTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      hXSmtTyNat with ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (Int.ofNat WN) px := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, Smtm.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] using
      hXRange.2
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (Int.ofNat (WN + AN))))) (WN + AN)
      hConstSmtTyNat with ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (Int.ofNat (WN + AN))))) =
        SmtValue.Binary (Int.ofNat (WN + AN)) pc := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (Int.ofNat (WN + AN) : Int) :=
        Int.natCast_nonneg _
      have hsimpa := hnn; (try simp [SmtEval.native_zleq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢); exact decide_eq_true hsimpa) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    have hsimpa :=
      hConstRange.2
    try simp [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hConstPayload : (Int.ofNat cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat cBV.toNat) := by
    have h := hConstEval'
    rw [← hConstPayload] at h
    simpa only [← hWideCast] using h
  have hLowerEval := eval_sign_extend_ult_const_not_upper_bound
    M x WN AN hWNatPos hXSmtTyNat
  have hUpperEval := eval_sign_extend_ult_const_not_lower_bound
    M x WN AN hWNatPos hXSmtTyNat
  have hLowerRel := RuleProofs.eo_interprets_eq_rel M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvSignExtendUltConst4LowerBound x
          (Term.Numeral (native_zplus W A))))
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A))))
    (Term.Boolean true)
    (by have hsimpa := hLowerPrem; (try simp [bvSignExtendUltConst4LowerPrem] at hsimpa ⊢); exact hsimpa)
  rw [eval_bvule_term_local] at hLowerRel
  rw [show __smtx_model_eval M
      (__eo_to_smt
        (bvSignExtendUltConst4LowerBound x
          (Term.Numeral (native_zplus W A)))) =
      SmtValue.Binary (Int.ofNat (WN + AN))
        (Int.ofNat (2 ^ (WN - 1) - 1)) by
    simpa only [← hWideCast] using hLowerEval] at hLowerRel
  rw [hConstEvalBV, eval_bvule_binary_nat] at hLowerRel
  have hLowerEq :
      SmtValue.Boolean (decide (2 ^ (WN - 1) - 1 ≤ cBV.toNat)) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp (by have hsimpa := hLowerRel; (try simp at hsimpa ⊢); exact hsimpa)
  have hLower : 2 ^ (WN - 1) - 1 ≤ cBV.toNat := by
    apply of_decide_eq_true
    injection hLowerEq
  have hUpperRel := RuleProofs.eo_interprets_eq_rel M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))))
      (bvSignExtendUltConst4UpperBound x
        (Term.Numeral (native_zplus W A))))
    (Term.Boolean true)
    (by have hsimpa := hUpperPrem; (try simp [bvSignExtendUltConst4UpperPrem] at hsimpa ⊢); exact hsimpa)
  rw [eval_bvule_term_local, hConstEvalBV] at hUpperRel
  rw [show __smtx_model_eval M
      (__eo_to_smt
        (bvSignExtendUltConst4UpperBound x
          (Term.Numeral (native_zplus W A)))) =
      SmtValue.Binary (Int.ofNat (WN + AN))
        (Int.ofNat (2 ^ (WN + AN) - 2 ^ (WN - 1) - 1)) by
    simpa only [← hWideCast] using hUpperEval] at hUpperRel
  rw [eval_bvule_binary_nat] at hUpperRel
  have hUpperEq :
      SmtValue.Boolean
          (decide (cBV.toNat ≤ 2 ^ (WN + AN) - 2 ^ (WN - 1) - 1)) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp (by have hsimpa := hUpperRel; (try simp at hsimpa ⊢); exact hsimpa)
  have hUpper :
      cBV.toNat ≤ 2 ^ (WN + AN) - 2 ^ (WN - 1) - 1 := by
    apply of_decide_eq_true
    injection hUpperEq
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (xBV.signExtend (WN + AN)).toNat) := by
    rw [eval_sign_extend_term_local, hXEval', ← hARound]
    have hSign := sign_extend_val_bitvec WN AN px hPx0 hPx1
    rw [Nat.add_comm AN WN] at hSign
    exact hSign
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst4Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Boolean
          (decide (cBV.toNat < (xBV.signExtend (WN + AN)).toNat)) := by
    unfold bvSignExtendUltConst4Lhs
    rw [eval_bvult_term_local, hConstEvalBV, hSignEval]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
  have hSignBitEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstSignBit x (Term.Numeral H))) =
        SmtValue.Binary 1
          (Int.ofNat (xBV.extractLsb' (WN - 1) 1).toNat) := by
    unfold bvSignExtendUltConstSignBit
    rw [eval_extract_term, hXEval', hHCast]
    simpa [xBV] using
      extract_val_bitvec_start_len WN (WN - 1) 1 px
        (Int.ofNat (WN - 1)) (Int.ofNat (WN - 1))
        hPx0 hPx1 rfl (by push_cast; omega)
  have hOneBitEval :
      __smtx_model_eval M (__eo_to_smt (bvSignExtendUltConstBit 1)) =
        SmtValue.Binary 1 (Int.ofNat (1#1).toNat) := by
    simpa [bvSignExtendUltConstBit, bvSignExtendUltConstOne] using
      eval_sign_extend_ult_const_one M 1 (by decide)
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSignExtendUltConst4Rhs x (Term.Numeral H))) =
        SmtValue.Boolean
          (decide (xBV.extractLsb' (WN - 1) 1 = 1#1)) := by
    unfold bvSignExtendUltConst4Rhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvSignExtendUltConstSignBit x (Term.Numeral H)))
          (__eo_to_smt (bvSignExtendUltConstBit 1))) = _
    rw [smtx_eval_eq_term_eq, hSignBitEval, hOneBitEval]
    exact smt_eval_eq_bitvec_values _ _
  rw [hLhsEval, hRhsEval,
    sign_extend_ult_middle_range_rev xBV cBV hWNatPos hLower hUpper,
    sign_bit_extract_eq_one xBV hWNatPos]

private theorem facts_bv_sign_extend_ult_const_4_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst4Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvSignExtendUltConst4LowerPrem x c nm) true ->
    eo_interprets M (bvSignExtendUltConst4UpperPrem x c nm) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvSignExtendUltConst4Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
    hLowerPrem hUpperPrem hWidthPrem
  have hBool := typed_bv_sign_extend_ult_const_4_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_sign_extend_ult_const_4_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hH0, hHW,
      hXSmtTy, hConstSmtTy, _hSignSmtTy, _hBitSmtTy, _hOneBitSmtTy⟩
  unfold bvSignExtendUltConst4Term bvZeroExtendEqConstEq
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSignExtendUltConst4Term, bvZeroExtendEqConstEq] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst4Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst4Rhs x (Term.Numeral H))))
    rw [sign_extend_ult_const_4_eval_eq M hM x c W A H
      hW0 hA0 hH0 hHW hXSmtTy hConstSmtTy
      (by simpa using hLowerPrem) (by simpa using hUpperPrem)
      (by simpa using hWidthPrem)]
    exact RuleProofs.smt_value_rel_refl _

def bvSignExtendUltConst4Program
    (x m c nm nm2 P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_sign_extend_ult_const_4 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private def bvSignExtendUltConst4LowerPremRefs
    (nmZero nmAmount x nmConst c : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (Term.Apply (Term.UOp UserOp.bvnot)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvshl)
              (Term.Apply (Term.UOp UserOp.bvnot)
                (bvSignExtendUltConstZero nmZero)))
            (bvSignExtendUltConstAmount x nmAmount))))
      (bvZeroExtendUltConstConst c nmConst))
    (Term.Boolean true)

private def bvSignExtendUltConst4UpperPremRefs
    (nmConst c nmOne nmAmount x : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.bvule)
        (bvZeroExtendUltConstConst c nmConst))
      (Term.Apply (Term.UOp UserOp.bvnot)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvshl)
            (bvSignExtendUltConstOne nmOne))
          (bvSignExtendUltConstAmount x nmAmount))))
    (Term.Boolean true)

private theorem bv_sign_extend_ult_const_4_premise_shape
    (x m c nm nm2 P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3 ≠ Term.Stuck ->
    ∃ nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU nm2W xW,
      P1 = bvSignExtendUltConst4LowerPremRefs nmL1 nmL2 xL nmL3 cL ∧
      P2 = bvSignExtendUltConst4UpperPremRefs nmU1 cU nmU2 nmU3 xU ∧
      P3 = bvZeroExtendUltConstWidthPrem xW nm2W := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU nm2W xW,
        P1 = bvSignExtendUltConst4LowerPremRefs nmL1 nmL2 xL nmL3 cL ∧
        P2 = bvSignExtendUltConst4UpperPremRefs nmU1 cU nmU2 nmU3 xU ∧
        P3 = bvZeroExtendUltConstWidthPrem xW nm2W
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_ult_const_4.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hM hC hNm hNm2 (by
        intro nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU nm2W xW
          hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape ⟨nmL1, nmL2, xL, nmL3, cL, nmU1, cU, nmU2,
          nmU3, xU, nm2W, xW, rfl, rfl, rfl⟩)

private theorem bv_sign_extend_ult_const_4_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst4Program x m c nm nm2
        (bvSignExtendUltConst4LowerPrem x c nm)
        (bvSignExtendUltConst4UpperPrem x c nm)
        (bvZeroExtendUltConstWidthPrem x nm2) =
      bvSignExtendUltConst4Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvSignExtendUltConst4Program bvSignExtendUltConst4LowerPrem
    bvSignExtendUltConst4UpperPrem bvSignExtendUltConst4LowerBound
    bvSignExtendUltConst4UpperBound bvZeroExtendUltConstWidthPrem
    bvSignExtendUltConstLowerBound bvSignExtendUltConstUpperBound
    bvSignExtendUltConstOne bvSignExtendUltConstZero
    bvSignExtendUltConstAmount bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstConst bvZeroExtendEqConstEq
  rw [__eo_prog_bv_sign_extend_ult_const_4.eq_6
    x m c nm nm2 nm nm x nm c nm c nm nm x nm2 x
    hX hM hC hNm hNm2]
  simp [bvSignExtendUltConst2Guard, bvSignExtendUltConst4Term,
    bvSignExtendUltConst4Lhs, bvSignExtendUltConst4Rhs,
    bvSignExtendEqConstSign, bvSignExtendUltConstSignBit,
    bvSignExtendUltConstBit, bvZeroExtendEqConstEq,
    bvZeroExtendUltConstConst, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bvSignExtendUltConst4Program_normalize
    (x m c nm nm2 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvSignExtendUltConst4LowerPrem x c nm ∧
      P2 = bvSignExtendUltConst4UpperPrem x c nm ∧
      P3 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3 =
        bvSignExtendUltConst4Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_sign_extend_ult_const_4_premise_shape
      x m c nm nm2 P1 P2 P3 hX hM hC hNm hNm2 hProg with
    ⟨nmL1, nmL2, xL, nmL3, cL, nmU1, cU, nmU2, nmU3, xU,
      nm2W, xW, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvSignExtendUltConst4Program bvSignExtendUltConst4LowerPremRefs
    bvSignExtendUltConst4UpperPremRefs bvZeroExtendUltConstWidthPrem
    bvSignExtendUltConstOne bvSignExtendUltConstZero
    bvSignExtendUltConstAmount bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstConst bvZeroExtendEqConstEq at hReq
  rw [__eo_prog_bv_sign_extend_ult_const_4.eq_6
    x m c nm nm2 nmL1 nmL2 xL nmL3 cL nmU1 cU nmU2 nmU3 xU
    nm2W xW hX hM hC hNm hNm2] at hReq
  rcases bv_sign_extend_ult_const_2_guard_refs
      (by simpa [bvSignExtendUltConst2Guard] using hReq) with
    ⟨hNmL1, hNmL2, hXL, hNmL3, hCL, hNmU1, hCU, hNmU2, hNmU3,
      hXU, hNm2W, hXW⟩
  subst nmL1; subst nmL2; subst xL; subst nmL3; subst cL
  subst nmU1; subst cU; subst nmU2; subst nmU3; subst xU
  subst nm2W; subst xW
  have hP1Canonical : P1 = bvSignExtendUltConst4LowerPrem x c nm := by
    simpa [bvSignExtendUltConst4LowerPrem,
      bvSignExtendUltConst4LowerPremRefs,
      bvSignExtendUltConst4LowerBound,
      bvSignExtendUltConstUpperBound] using hP1
  have hP2Canonical : P2 = bvSignExtendUltConst4UpperPrem x c nm := by
    simpa [bvSignExtendUltConst4UpperPrem,
      bvSignExtendUltConst4UpperPremRefs,
      bvSignExtendUltConst4UpperBound,
      bvSignExtendUltConstLowerBound] using hP2
  have hP3Canonical : P3 = bvZeroExtendUltConstWidthPrem x nm2 := hP3
  refine ⟨hP1Canonical, hP2Canonical, hP3Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical, hP3Canonical]
  exact bv_sign_extend_ult_const_4_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

theorem typed_bv_sign_extend_ult_const_4_program
    (x m c nm nm2 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof (bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst4Program_normalize x m c nm nm2 P1 P2 P3
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst4Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_ult_const_4_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_sign_extend_ult_const_4_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof (bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvSignExtendUltConst4Program x m c nm nm2 P1 P2 P3) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst4Program_normalize x m c nm nm2 P1 P2 P3
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst4Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLowerPrem :
      eo_interprets M (bvSignExtendUltConst4LowerPrem x c nm) true := by
    simpa [hP1] using hP1True
  have hUpperPrem :
      eo_interprets M (bvSignExtendUltConst4UpperPrem x c nm) true := by
    simpa [hP2] using hP2True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_sign_extend_ult_const_4_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy
    hLowerPrem hUpperPrem hWidthPrem

private theorem sign_ult_pow_decomp (W A : Nat) (hW : 0 < W) (hA : 0 < A) :
    2 ^ (W + A) - 2 ^ (W - 1) =
      (2 ^ A - 1) * 2 ^ W + 2 ^ (W - 1) := by
  have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
    calc
      2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
  have hPowA : 1 ≤ 2 ^ A := Nat.one_le_two_pow
  have hWide : 2 ^ (W + A) = 2 ^ A * 2 ^ W := by
    rw [Nat.pow_add, Nat.mul_comm]
  have hSplit : 2 ^ A = (2 ^ A - 1) + 1 := by omega
  have hWide' :
      2 ^ (W + A) = (2 ^ A - 1) * 2 ^ W + 2 ^ W := by
    calc
      2 ^ (W + A) = 2 ^ A * 2 ^ W := hWide
      _ = ((2 ^ A - 1) + 1) * 2 ^ W :=
        congrArg (fun q : Nat => q * 2 ^ W) hSplit
      _ = (2 ^ A - 1) * 2 ^ W + 2 ^ W := by
        rw [Nat.add_mul, Nat.one_mul]
  rw [hWide']
  omega

private theorem sign_ult_extract_low_high
    (c : BitVec (W + A)) (hW : 0 < W) (hA : 0 < A)
    (hUpper : 2 ^ (W + A) - 2 ^ (W - 1) ≤ c.toNat) :
    (c.extractLsb' 0 W).toNat =
      2 ^ (W - 1) +
        (c.toNat - (2 ^ (W + A) - 2 ^ (W - 1))) := by
  have hDecomp := sign_ult_pow_decomp W A hW hA
  let d := c.toNat - (2 ^ (W + A) - 2 ^ (W - 1))
  have hCEq : c.toNat =
      (2 ^ (W + A) - 2 ^ (W - 1)) + d := by
    dsimp [d]
    exact (Nat.add_sub_of_le hUpper).symm
  have hDLt : d < 2 ^ (W - 1) := by
    have hc := c.isLt
    dsimp [d]
    omega
  have hLowLt : 2 ^ (W - 1) + d < 2 ^ W := by
    have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
      calc
        2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
    omega
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  change c.toNat % 2 ^ W = 2 ^ (W - 1) + d
  rw [hCEq, hDecomp]
  simp [Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt hLowLt]

private theorem sign_extend_ult_outside
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W)
    (hOutside : c.toNat ≤ 2 ^ (W - 1) ∨
      2 ^ (W + A) - 2 ^ (W - 1) ≤ c.toNat) :
    decide ((x.signExtend (W + A)).toNat < c.toNat) =
      decide (x.toNat < (c.extractLsb' 0 W).toNat) := by
  cases A with
  | zero => simp
  | succ A =>
    have hA : 0 < A + 1 := by omega
    have hWWide : W ≤ W + (A + 1) := by omega
    have hPowMono : 2 ^ W ≤ 2 ^ (W + (A + 1)) :=
      Nat.pow_le_pow_right (by decide) hWWide
    have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
      calc
        2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
    cases hx : x.msb
    · have hTwoLt : 2 * x.toNat < 2 ^ W :=
        BitVec.msb_eq_false_iff_two_mul_lt.mp hx
      have hXLt : x.toNat < 2 ^ (W - 1) := by omega
      have hXWide : x.toNat < 2 ^ (W + (A + 1)) :=
        Nat.lt_of_lt_of_le x.isLt hPowMono
      have hSignNat : (x.signExtend (W + (A + 1))).toNat = x.toNat := by
        rw [BitVec.signExtend_eq_setWidth_of_msb_false hx,
          BitVec.toNat_setWidth, Nat.mod_eq_of_lt hXWide]
      rcases hOutside with hLow | hHigh
      · have hCLt : c.toNat < 2 ^ W := by omega
        have hLowNat : (c.extractLsb' 0 W).toNat = c.toNat := by
          simp [Nat.mod_eq_of_lt hCLt]
        simp [hSignNat, hLowNat]
      · have hLowNat := sign_ult_extract_low_high c hW hA hHigh
        have hSignLt : (x.signExtend (W + (A + 1))).toNat < c.toNat := by
          rw [hSignNat]
          omega
        have hLowLt : x.toNat < (c.extractLsb' 0 W).toNat := by
          rw [hLowNat]
          omega
        have hSignDec :
            decide ((x.signExtend (W + (A + 1))).toNat < c.toNat) = true :=
          decide_eq_true hSignLt
        have hLowDec :
            decide (x.toNat < (c.extractLsb' 0 W).toNat) = true :=
          decide_eq_true hLowLt
        rw [hSignDec, hLowDec]
    · have hTwoGe : 2 ^ W ≤ 2 * x.toNat :=
        BitVec.msb_eq_true_iff_two_mul_ge.mp hx
      have hXGe : 2 ^ (W - 1) ≤ x.toNat := by omega
      have hXWide : x.toNat < 2 ^ (W + (A + 1)) :=
        Nat.lt_of_lt_of_le x.isLt hPowMono
      have hSignNat :
          (x.signExtend (W + (A + 1))).toNat =
            x.toNat + (2 ^ (W + (A + 1)) - 2 ^ W) := by
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt hXWide, hx]
        rfl
      rcases hOutside with hLow | hHigh
      · have hCLt : c.toNat < 2 ^ W := by omega
        have hLowNat : (c.extractLsb' 0 W).toNat = c.toNat := by
          simp [Nat.mod_eq_of_lt hCLt]
        have hSignNotLt : ¬(x.signExtend (W + (A + 1))).toNat < c.toNat := by
          rw [hSignNat]
          omega
        have hLowNotLt : ¬x.toNat < (c.extractLsb' 0 W).toNat := by
          rw [hLowNat]
          omega
        have hSignDec :
            decide ((x.signExtend (W + (A + 1))).toNat < c.toNat) = false :=
          decide_eq_false hSignNotLt
        have hLowDec :
            decide (x.toNat < (c.extractLsb' 0 W).toNat) = false :=
          decide_eq_false hLowNotLt
        rw [hSignDec, hLowDec]
      · have hLowNat := sign_ult_extract_low_high c hW hA hHigh
        rw [hSignNat, hLowNat]
        rw [decide_eq_decide]
        omega

private theorem sign_extend_ult_outside_rev
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W)
    (hOutside : c.toNat < 2 ^ (W - 1) ∨
      2 ^ (W + A) - 2 ^ (W - 1) - 1 ≤ c.toNat) :
    decide (c.toNat < (x.signExtend (W + A)).toNat) =
      decide ((c.extractLsb' 0 W).toNat < x.toNat) := by
  have sign_ult_extract_low_high_pred
      (c : BitVec (W + A)) (hW : 0 < W) (hA : 0 < A)
      (hUpper : 2 ^ (W + A) - 2 ^ (W - 1) - 1 ≤ c.toNat) :
      (c.extractLsb' 0 W).toNat =
        2 ^ (W - 1) - 1 +
          (c.toNat - (2 ^ (W + A) - 2 ^ (W - 1) - 1)) := by
    have hDecomp := sign_ult_pow_decomp W A hW hA
    have hHalfPos : 0 < 2 ^ (W - 1) := Nat.two_pow_pos _
    have hBaseDecomp :
        2 ^ (W + A) - 2 ^ (W - 1) - 1 =
          (2 ^ A - 1) * 2 ^ W + (2 ^ (W - 1) - 1) := by
      rw [hDecomp]
      omega
    let d := c.toNat - (2 ^ (W + A) - 2 ^ (W - 1) - 1)
    have hCEq : c.toNat =
        (2 ^ (W + A) - 2 ^ (W - 1) - 1) + d := by
      dsimp [d]
      exact (Nat.add_sub_of_le hUpper).symm
    have hDLe : d ≤ 2 ^ (W - 1) := by
      have hc := c.isLt
      dsimp [d]
      omega
    have hLowLt : 2 ^ (W - 1) - 1 + d < 2 ^ W := by
      have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
        calc
          2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
          _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
          _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
      omega
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    change c.toNat % 2 ^ W = 2 ^ (W - 1) - 1 + d
    rw [hCEq, hBaseDecomp]
    simp [Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt hLowLt]
  cases A with
  | zero => simp
  | succ A =>
    have hA : 0 < A + 1 := by omega
    have hWWide : W ≤ W + (A + 1) := by omega
    have hPowMono : 2 ^ W ≤ 2 ^ (W + (A + 1)) :=
      Nat.pow_le_pow_right (by decide) hWWide
    have hPowW : 2 ^ W = 2 * 2 ^ (W - 1) := by
      calc
        2 ^ W = 2 ^ ((W - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (W - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (W - 1) := Nat.mul_comm _ _
    cases hx : x.msb
    · have hTwoLt : 2 * x.toNat < 2 ^ W :=
        BitVec.msb_eq_false_iff_two_mul_lt.mp hx
      have hXLt : x.toNat < 2 ^ (W - 1) := by omega
      have hXWide : x.toNat < 2 ^ (W + (A + 1)) :=
        Nat.lt_of_lt_of_le x.isLt hPowMono
      have hSignNat : (x.signExtend (W + (A + 1))).toNat = x.toNat := by
        rw [BitVec.signExtend_eq_setWidth_of_msb_false hx,
          BitVec.toNat_setWidth, Nat.mod_eq_of_lt hXWide]
      rcases hOutside with hLow | hHigh
      · have hCLt : c.toNat < 2 ^ W := by omega
        have hLowNat : (c.extractLsb' 0 W).toNat = c.toNat := by
          simp [Nat.mod_eq_of_lt hCLt]
        rw [hSignNat, hLowNat]
      · have hLowNat := sign_ult_extract_low_high_pred c hW hA hHigh
        have hSignNotLt : ¬c.toNat <
            (x.signExtend (W + (A + 1))).toNat := by
          rw [hSignNat]
          have hWideAtLeast :
              2 ^ W * 2 ≤ 2 ^ (W + (A + 1)) := by
            rw [Nat.pow_add]
            have hTwoLe : 2 ≤ 2 ^ (A + 1) := by
              exact Nat.one_lt_two_pow (by omega)
            exact Nat.mul_le_mul_left _ hTwoLe
          omega
        have hLowNotLt : ¬(c.extractLsb' 0 W).toNat < x.toNat := by
          rw [hLowNat]
          omega
        have hSignDec := decide_eq_false hSignNotLt
        have hLowDec := decide_eq_false hLowNotLt
        rw [hSignDec, hLowDec]
    · have hTwoGe : 2 ^ W ≤ 2 * x.toNat :=
        BitVec.msb_eq_true_iff_two_mul_ge.mp hx
      have hXGe : 2 ^ (W - 1) ≤ x.toNat := by omega
      have hXWide : x.toNat < 2 ^ (W + (A + 1)) :=
        Nat.lt_of_lt_of_le x.isLt hPowMono
      have hSignNat :
          (x.signExtend (W + (A + 1))).toNat =
            x.toNat + (2 ^ (W + (A + 1)) - 2 ^ W) := by
        rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt hXWide, hx]
        rfl
      rcases hOutside with hLow | hHigh
      · have hCLt : c.toNat < 2 ^ W := by omega
        have hLowNat : (c.extractLsb' 0 W).toNat = c.toNat := by
          simp [Nat.mod_eq_of_lt hCLt]
        have hSignLt : c.toNat <
            (x.signExtend (W + (A + 1))).toNat := by
          rw [hSignNat]
          omega
        have hLowLt : (c.extractLsb' 0 W).toNat < x.toNat := by
          rw [hLowNat]
          omega
        have hSignDec := decide_eq_true hSignLt
        have hLowDec := decide_eq_true hLowLt
        rw [hSignDec, hLowDec]
      · have hLowNat := sign_ult_extract_low_high_pred c hW hA hHigh
        rw [hSignNat, hLowNat]
        rw [decide_eq_decide]
        have hc := c.isLt
        omega

/-! Support for the outside-range `bv_sign_extend_ult_const` rewrites. -/

def bvSignExtendUltConstOutside1Prem (x c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvule)
            (bvZeroExtendUltConstConst c nm))
          (bvSignExtendUltConstLowerBound x nm)))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvuge)
              (bvZeroExtendUltConstConst c nm))
            (bvSignExtendUltConstUpperBound x nm)))
        (Term.Boolean false)))
    (Term.Boolean true)

def bvSignExtendUltConstOutside3Prem (x c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvult)
            (bvZeroExtendUltConstConst c nm))
          (bvSignExtendUltConstLowerBound x nm)))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvuge)
              (bvZeroExtendUltConstConst c nm))
            (bvSignExtendUltConst4UpperBound x nm)))
        (Term.Boolean false)))
    (Term.Boolean true)

def bvSignExtendUltConst1Lhs (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult) (bvSignExtendEqConstSign x m))
    (bvZeroExtendUltConstConst c nm)

def bvSignExtendUltConst1Rhs (x c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult) x)
    (bvZeroExtendUltConstLow c nm nm2)

def bvSignExtendUltConst1Term (x m c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendUltConst1Lhs x m c nm)
    (bvSignExtendUltConst1Rhs x c nm nm2)

def bvSignExtendUltConst3Lhs (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstConst c nm))
    (bvSignExtendEqConstSign x m)

def bvSignExtendUltConst3Rhs (x c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstLow c nm nm2))
    x

def bvSignExtendUltConst3Term (x m c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendUltConst3Lhs x m c nm)
    (bvSignExtendUltConst3Rhs x c nm nm2)

private theorem bv_sign_extend_ult_outside_context_of_types
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    ∃ W A H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 H = true ∧ native_zlt H (native_zplus W A) = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes
  have hWideTypesZero :
      ∃ width,
        __eo_typeof (bvZeroExtendUltConstZero x m) =
            Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
            Term.Apply (Term.UOp UserOp.BitVec) width := by
    rcases hWideTypes with ⟨width, hSignTy, hConstTy⟩
    exact ⟨width, by
      have hsimpa := hSignTy; (try simp [bvZeroExtendUltConstZero, bvSignExtendEqConstSign] at hsimpa ⊢); exact hsimpa,
      hConstTy⟩
  rcases bv_zero_extend_ult_const_context_of_types x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hWideTypesZero hLowTypes with
    ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, _hZeroSmtTy⟩
  have hConstTrans : RuleProofs.eo_has_smt_translation
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rcases hLowTypes with ⟨width, _hXTy, hLowTy⟩
    rw [hLowTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wide, H, low, _hConstEoTy, hNm2, hLow, hWide0, hLow0,
      hHWide, _hD0, _hConstSmtTy'⟩
  have hLowEq : low = 0 := by
    injection hLow with h
    exact h.symm
  subst low
  subst nm2
  have hSum0 : native_zleq 0 (native_zplus W A) = true := by
    apply decide_eq_true
    have hWNonneg : (0 : Int) ≤ W := of_decide_eq_true hW0
    have hANonneg : (0 : Int) ≤ A := of_decide_eq_true hA0
    simpa [SmtEval.native_zplus] using Int.add_nonneg hWNonneg hANonneg
  have hWideEq : wide = native_zplus W A := by
    rw [hConstSmtTy] at _hConstSmtTy'
    injection _hConstSmtTy' with hNat
    have hWideRound := native_int_to_nat_roundtrip wide hWide0
    have hSumRound := native_int_to_nat_roundtrip (native_zplus W A) hSum0
    rw [hNat] at hSumRound
    exact hWideRound.symm.trans hSumRound
  subst wide
  have hH0 : native_zleq 0 H = true := by
    change decide ((0 : Int) ≤ H) = true
    apply decide_eq_true
    change decide
        ((0 : Int) < native_zplus (native_zplus H 1) (native_zneg 0)) =
      true at _hD0
    have hPos := of_decide_eq_true _hD0
    have hPos' : (0 : Int) < H + 1 := by
      simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hPos
    omega
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    have hRaw := smt_typeof_sign_extend_of_context x W A hXSmtTy hW0 hA0
    have hComm : native_zplus A W = native_zplus W A := by
      simp [SmtEval.native_zplus, Int.add_comm]
    simpa [bvSignExtendEqConstSign, hComm] using hRaw
  exact ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hH0, hHWide,
    hXSmtTy, hConstSmtTy, hLowSmtTy, hSignSmtTy⟩

private theorem bv_sign_extend_ult_const_1_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    ∃ W A H : native_Int,
      m = Term.Numeral A ∧ nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 H = true ∧ native_zlt H (native_zplus W A) = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hX hM hC hNm hTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof (bvSignExtendEqConstSign x m))
        (__eo_typeof (bvZeroExtendUltConstConst c nm)))
      (__eo_typeof_bvult (__eo_typeof x)
        (__eo_typeof (bvZeroExtendUltConstLow c nm nm2))) = Term.Bool at hTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy with
    ⟨hWideNe, hLowNe⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hWideNe with
    ⟨wide, hSignTy, hConstTy⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hLowNe with
    ⟨low, hXTy, hLowTy⟩
  exact bv_sign_extend_ult_outside_context_of_types x m c nm nm2
    hX hM hC hNm ⟨wide, hSignTy, hConstTy⟩ ⟨low, hXTy, hLowTy⟩

private theorem bv_sign_extend_ult_const_3_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst3Term x m c nm nm2) = Term.Bool ->
    ∃ W A H : native_Int,
      m = Term.Numeral A ∧ nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 H = true ∧ native_zlt H (native_zplus W A) = true ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hX hM hC hNm hTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof (bvZeroExtendUltConstConst c nm))
        (__eo_typeof (bvSignExtendEqConstSign x m)))
      (__eo_typeof_bvult (__eo_typeof (bvZeroExtendUltConstLow c nm nm2))
        (__eo_typeof x)) = Term.Bool at hTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hTy with
    ⟨hWideNe, hLowNe⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hWideNe with
    ⟨wide, hConstTy, hSignTy⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hLowNe with
    ⟨low, hLowTy, hXTy⟩
  exact bv_sign_extend_ult_outside_context_of_types x m c nm nm2
    hX hM hC hNm ⟨wide, hSignTy, hConstTy⟩ ⟨low, hXTy, hLowTy⟩

private theorem typed_bv_sign_extend_ult_const_1_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst1Term x m c nm nm2) := by
  intro hX hM hC hNm hTy
  rcases bv_sign_extend_ult_const_1_context x m c nm nm2
      hX hM hC hNm hTy with
    ⟨W, A, H, rfl, rfl, rfl, _hW0, _hA0, _hH0, _hHWide,
      hXSmtTy, hConstSmtTy, hLowSmtTy, hSignSmtTy⟩
  have hLhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvSignExtendEqConstSign x (Term.Numeral A))
    (bvZeroExtendUltConstConst c (Term.Numeral (native_zplus W A)))
    _ hSignSmtTy hConstSmtTy
  have hRhsTy := smt_typeof_bvult_of_same_bitvec_local
    x
    (bvZeroExtendUltConstLow c
      (Term.Numeral (native_zplus W A)) (Term.Numeral H))
    _ hXSmtTy hLowSmtTy
  unfold bvSignExtendUltConst1Term bvZeroExtendEqConstEq
  have hLhsNN :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConst1Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) ≠ SmtType.None := by
    rw [show __smtx_typeof
        (__eo_to_smt
          (bvSignExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) = SmtType.Bool by
      simpa [bvSignExtendUltConst1Lhs] using hLhsTy]
    intro h
    cases h
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvSignExtendUltConst1Lhs, bvSignExtendUltConst1Rhs] using
      hLhsTy.trans hRhsTy.symm)
    hLhsNN

private theorem typed_bv_sign_extend_ult_const_3_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst3Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst3Term x m c nm nm2) := by
  intro hX hM hC hNm hTy
  rcases bv_sign_extend_ult_const_3_context x m c nm nm2
      hX hM hC hNm hTy with
    ⟨W, A, H, rfl, rfl, rfl, _hW0, _hA0, _hH0, _hHWide,
      hXSmtTy, hConstSmtTy, hLowSmtTy, hSignSmtTy⟩
  have hLhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstConst c (Term.Numeral (native_zplus W A)))
    (bvSignExtendEqConstSign x (Term.Numeral A))
    _ hConstSmtTy hSignSmtTy
  have hRhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstLow c
      (Term.Numeral (native_zplus W A)) (Term.Numeral H))
    x _ hLowSmtTy hXSmtTy
  unfold bvSignExtendUltConst3Term bvZeroExtendEqConstEq
  have hLhsNN :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendUltConst3Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) ≠ SmtType.None := by
    rw [show __smtx_typeof
        (__eo_to_smt
          (bvSignExtendUltConst3Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) = SmtType.Bool by
      simpa [bvSignExtendUltConst3Lhs] using hLhsTy]
    intro h
    cases h
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvSignExtendUltConst3Lhs, bvSignExtendUltConst3Rhs] using
      hLhsTy.trans hRhsTy.symm)
    hLhsNN

private theorem eval_bvuge_term_local
    (M : SmtModel) (x y : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) x) y)) =
      __smtx_model_eval_bvuge
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  change __smtx_model_eval M
      (SmtTerm.bvuge (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bvuge_binary_nat (N a b : Nat) :
    __smtx_model_eval_bvuge
        (SmtValue.Binary (Int.ofNat N) (Int.ofNat a))
        (SmtValue.Binary (Int.ofNat N) (Int.ofNat b)) =
      SmtValue.Boolean (decide (b ≤ a)) := by
  exact eval_bvule_binary_nat N b a

private theorem eval_bvult_binary_nat (N a b : Nat) :
    __smtx_model_eval_bvult
        (SmtValue.Binary (Int.ofNat N) (Int.ofNat a))
        (SmtValue.Binary (Int.ofNat N) (Int.ofNat b)) =
      SmtValue.Boolean (decide (a < b)) := by
  simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
    SmtEval.native_zlt]

private theorem sign_extend_ult_const_outside_values
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A H : native_Int) :
    native_zleq 0 W = true -> native_zleq 0 A = true ->
    native_zleq 0 H = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral H)) true ->
    ∃ WN AN : Nat, ∃ xBV : BitVec WN, ∃ cBV : BitVec (WN + AN),
      0 < WN ∧
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (Int.ofNat WN) (Int.ofNat xBV.toNat) ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN)) (Int.ofNat cBV.toNat) ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (xBV.signExtend (WN + AN)).toNat) ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral H))) =
        SmtValue.Binary (Int.ofNat WN)
          (Int.ofNat (cBV.extractLsb' 0 WN).toNat) ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstLowerBound x
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (2 ^ (WN - 1))) ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConstUpperBound x
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (2 ^ (WN + AN) - 2 ^ (WN - 1))) ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst4UpperBound x
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (2 ^ (WN + AN) - 2 ^ (WN - 1) - 1)) := by
  intro hW0 hA0 hH0 hXSmtTy hConstSmtTy hWidthPrem
  have hHEq := bv_sign_extend_eq_const_nm2_numeric
    M x W H hW0 hXSmtTy hWidthPrem
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWRound : (Int.ofNat WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hARound : (Int.ofNat AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, Smtm.native_nat_to_int, native_nat_to_int] using h
  have hSub : H = W - 1 := by
    have hsimpa := hHEq
    try simp [SmtEval.native_zplus, SmtEval.native_zneg] at hsimpa ⊢
    exact hsimpa
  have hWNatPos : 0 < WN := by
    have hHNonneg : (0 : Int) ≤ H := of_decide_eq_true hH0
    rw [hSub] at hHNonneg
    have hWPos : (0 : Int) < W := by omega
    have hWNatPosInt : (0 : Int) < Int.ofNat WN := by
      rw [hWRound]
      exact hWPos
    exact Int.natCast_pos.mp hWNatPosInt
  have hHCast : H = Int.ofNat (WN - 1) := by
    rw [← hWRound] at hSub
    calc
      H = (Int.ofNat WN : Int) - 1 := hSub
      _ = Int.ofNat (WN - 1) :=
        (Int.ofNat_sub (by omega : 1 ≤ WN)).symm
  have hWideCast :
      (Int.ofNat (WN + AN) : Int) = native_zplus W A := by
    calc
      (Int.ofNat (WN + AN) : Int) =
          (Int.ofNat WN : Int) + Int.ofNat AN := rfl
      _ = W + A := by rw [hWRound, hARound]
      _ = native_zplus W A := rfl
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    apply decide_eq_true
    have hWNonneg : (0 : Int) ≤ W := of_decide_eq_true hW0
    have hANonneg : (0 : Int) ≤ A := of_decide_eq_true hA0
    simpa [SmtEval.native_zplus] using Int.add_nonneg hWNonneg hANonneg
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    have hRound := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    have hRound' :
        (Int.ofNat (native_int_to_nat (native_zplus W A)) : Int) =
          native_zplus W A := by
      simpa [Smtm.native_nat_to_int, native_nat_to_int] using hRound
    exact Int.ofNat.inj (hRound'.trans hWideCast.symm)
  have hXSmtTyNat : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec WN := by
    simpa [WN] using hXSmtTy
  have hConstSmtTyNat :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (WN + AN) := by
    simpa [hWideNat] using hConstSmtTy
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      hXSmtTyNat with ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (Int.ofNat WN) px := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, Smtm.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] using
      hXRange.2
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A)))) (WN + AN)
      hConstSmtTyNat with ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN)) pc := by
    simpa [Smtm.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (Int.ofNat (WN + AN) : Int) :=
        Int.natCast_nonneg _
      have hsimpa := hnn; (try simp [SmtEval.native_zleq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢); exact decide_eq_true hsimpa) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    have hsimpa :=
      hConstRange.2
    try simp [natpow2_eq, Smtm.native_nat_to_int, native_nat_to_int] at hsimpa ⊢
    exact hsimpa
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hXPayload : (Int.ofNat xBV.toNat : Int) = px := by
    have hToNat := ofInt_toNat_canonical WN px hPx0 hPx1
    simp [xBV, hToNat, Int.toNat_of_nonneg hPx0]
  have hConstPayload : (Int.ofNat cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hXEvalBV :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (Int.ofNat WN) (Int.ofNat xBV.toNat) := by
    rw [hXEval', hXPayload]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (Int.ofNat (WN + AN)) (Int.ofNat cBV.toNat) := by
    rw [hConstEval', hConstPayload]
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (Int.ofNat (WN + AN))
          (Int.ofNat (xBV.signExtend (WN + AN)).toNat) := by
    rw [eval_sign_extend_term_local, hXEval', ← hARound]
    have hSign := sign_extend_val_bitvec WN AN px hPx0 hPx1
    rw [Nat.add_comm AN WN] at hSign
    exact hSign
  have hLowStart : (0 : Int) = Int.ofNat 0 := rfl
  have hLowLen :
      native_zplus (native_zplus H 1) (native_zneg 0) =
        Int.ofNat WN := by
    calc
      native_zplus (native_zplus H 1) (native_zneg 0) = H + 1 := by
        simp [SmtEval.native_zplus, SmtEval.native_zneg]
      _ = Int.ofNat (WN - 1) + 1 := by rw [hHCast]
      _ = Int.ofNat ((WN - 1) + 1) :=
        Int.ofNat_add_ofNat (WN - 1) 1
      _ = Int.ofNat WN := by
        have hNat : WN - 1 + 1 = WN := by omega
        exact congrArg Int.ofNat hNat
  have hLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral H))) =
        SmtValue.Binary (Int.ofNat WN)
          (Int.ofNat (cBV.extractLsb' 0 WN).toNat) := by
    unfold bvZeroExtendUltConstLow
    change __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))
            (Term.Numeral H) (Term.Numeral 0))) = _
    rw [eval_extract_term, hConstEval]
    simpa [Smtm.native_nat_to_int, native_nat_to_int, cBV] using
      extract_val_bitvec_start_len (WN + AN) 0 WN pc H 0
        hPc0 hPc1 hLowStart hLowLen
  have hLowerEval :=
    eval_sign_extend_ult_const_lower_bound M x WN AN hWNatPos hXSmtTyNat
  have hUpperEval :=
    eval_sign_extend_ult_const_upper_bound M x WN AN hWNatPos hXSmtTyNat
  have hUpperPredEval :=
    eval_sign_extend_ult_const_not_lower_bound M x WN AN hWNatPos
      hXSmtTyNat
  exact ⟨WN, AN, xBV, cBV, hWNatPos, hXEvalBV, hConstEvalBV,
    hSignEval, hLowEval,
    by simpa only [← hWideCast] using hLowerEval,
    by simpa only [← hWideCast] using hUpperEval,
    by simpa only [← hWideCast] using hUpperPredEval⟩

private theorem eval_or_term_local
    (M : SmtModel) (x y : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) =
      __smtx_model_eval_or
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  change __smtx_model_eval M
      (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) = _
  exact smtx_eval_or_term_eq M (__eo_to_smt x) (__eo_to_smt y)

private theorem sign_extend_ult_const_1_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A H : native_Int) :
    native_zleq 0 W = true -> native_zleq 0 A = true ->
    native_zleq 0 H = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    eo_interprets M
      (bvSignExtendUltConstOutside1Prem x c
        (Term.Numeral (native_zplus W A))) true ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral H)) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst1Rhs x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral H))) := by
  intro hW0 hA0 hH0 hXSmtTy hConstSmtTy hOutsidePrem hWidthPrem
  rcases sign_extend_ult_const_outside_values M hM x c W A H
      hW0 hA0 hH0 hXSmtTy hConstSmtTy hWidthPrem with
    ⟨WN, AN, xBV, cBV, hWNatPos, hXEval, hConstEval, hSignEval,
      hLowEval, hLowerEval, hUpperEval, _hUpperPredEval⟩
  have hOutsideRel := RuleProofs.eo_interprets_eq_rel M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvule)
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))
          (bvSignExtendUltConstLowerBound x
            (Term.Numeral (native_zplus W A)))))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvuge)
              (bvZeroExtendUltConstConst c
                (Term.Numeral (native_zplus W A))))
            (bvSignExtendUltConstUpperBound x
              (Term.Numeral (native_zplus W A)))))
        (Term.Boolean false)))
    (Term.Boolean true)
    (by have hsimpa := hOutsidePrem; (try simp [bvSignExtendUltConstOutside1Prem] at hsimpa ⊢); exact hsimpa)
  rw [eval_or_term_local, eval_or_term_local,
    eval_bvule_term_local, hConstEval, hLowerEval, eval_bvule_binary_nat,
    eval_bvuge_term_local, hConstEval, hUpperEval, eval_bvuge_binary_nat]
      at hOutsideRel
  rw [show __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
      SmtValue.Boolean false by rfl,
    show __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
      SmtValue.Boolean true by rfl] at hOutsideRel
  have hOutsideEq :
      SmtValue.Boolean
          (decide (cBV.toNat ≤ 2 ^ (WN - 1)) ||
            (decide (2 ^ (WN + AN) - 2 ^ (WN - 1) ≤ cBV.toNat) ||
              false)) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp (by
        change RuleProofs.smt_value_rel
          (SmtValue.Boolean
            (decide (cBV.toNat ≤ 2 ^ (WN - 1)) ||
              (decide
                  (2 ^ (WN + AN) - 2 ^ (WN - 1) ≤ cBV.toNat) ||
                false)))
          (SmtValue.Boolean true) at hOutsideRel
        exact hOutsideRel)
  have hOutsideDec :
      (decide (cBV.toNat ≤ 2 ^ (WN - 1)) ||
          decide (2 ^ (WN + AN) - 2 ^ (WN - 1) ≤ cBV.toNat)) = true := by
    injection hOutsideEq with h
    simpa only [Bool.or_false] using h
  have hOutside :
      cBV.toNat ≤ 2 ^ (WN - 1) ∨
        2 ^ (WN + AN) - 2 ^ (WN - 1) ≤ cBV.toNat := by
    by_cases hLow : cBV.toNat ≤ 2 ^ (WN - 1)
    · exact Or.inl hLow
    · right
      rw [decide_eq_false hLow, Bool.false_or] at hOutsideDec
      exact of_decide_eq_true hOutsideDec
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst1Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Boolean
          (decide ((xBV.signExtend (WN + AN)).toNat < cBV.toNat)) := by
    unfold bvSignExtendUltConst1Lhs
    rw [eval_bvult_term_local, hSignEval, hConstEval]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst1Rhs x c
              (Term.Numeral (native_zplus W A)) (Term.Numeral H))) =
        SmtValue.Boolean
          (decide (xBV.toNat < (cBV.extractLsb' 0 WN).toNat)) := by
    unfold bvSignExtendUltConst1Rhs
    rw [eval_bvult_term_local, hXEval, hLowEval]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
    norm_cast
  rw [hLhsEval, hRhsEval,
    sign_extend_ult_outside xBV cBV hWNatPos hOutside]

private theorem facts_bv_sign_extend_ult_const_1_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvSignExtendUltConstOutside1Prem x c nm) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvSignExtendUltConst1Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
    hOutsidePrem hWidthPrem
  have hBool := typed_bv_sign_extend_ult_const_1_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_sign_extend_ult_const_1_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hH0, _hHWide,
      hXSmtTy, hConstSmtTy, _hLowSmtTy, _hSignSmtTy⟩
  unfold bvSignExtendUltConst1Term bvZeroExtendEqConstEq
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSignExtendUltConst1Term, bvZeroExtendEqConstEq] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst1Rhs x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral H))))
    rw [sign_extend_ult_const_1_eval_eq M hM x c W A H
      hW0 hA0 hH0 hXSmtTy hConstSmtTy
      (by simpa using hOutsidePrem) (by simpa using hWidthPrem)]
    exact RuleProofs.smt_value_rel_refl _

private theorem sign_extend_ult_const_3_eval_eq
    (M : SmtModel) (hM : model_wf M)
    (x c : Term) (W A H : native_Int) :
    native_zleq 0 W = true -> native_zleq 0 A = true ->
    native_zleq 0 H = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    eo_interprets M
      (bvSignExtendUltConstOutside3Prem x c
        (Term.Numeral (native_zplus W A))) true ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral H)) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst3Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst3Rhs x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral H))) := by
  intro hW0 hA0 hH0 hXSmtTy hConstSmtTy hOutsidePrem hWidthPrem
  rcases sign_extend_ult_const_outside_values M hM x c W A H
      hW0 hA0 hH0 hXSmtTy hConstSmtTy hWidthPrem with
    ⟨WN, AN, xBV, cBV, hWNatPos, hXEval, hConstEval, hSignEval,
      hLowEval, hLowerEval, _hUpperEval, hUpperPredEval⟩
  have hOutsideRel := RuleProofs.eo_interprets_eq_rel M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvult)
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))
          (bvSignExtendUltConstLowerBound x
            (Term.Numeral (native_zplus W A)))))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvuge)
              (bvZeroExtendUltConstConst c
                (Term.Numeral (native_zplus W A))))
            (bvSignExtendUltConst4UpperBound x
              (Term.Numeral (native_zplus W A)))))
        (Term.Boolean false)))
    (Term.Boolean true)
    (by have hsimpa := hOutsidePrem; (try simp [bvSignExtendUltConstOutside3Prem] at hsimpa ⊢); exact hsimpa)
  rw [eval_or_term_local, eval_or_term_local,
    eval_bvult_term_local, hConstEval, hLowerEval,
    eval_bvult_binary_nat,
    eval_bvuge_term_local, hConstEval, hUpperPredEval,
    eval_bvuge_binary_nat] at hOutsideRel
  rw [show __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
      SmtValue.Boolean false by rfl,
    show __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
      SmtValue.Boolean true by rfl] at hOutsideRel
  have hOutsideEq :
      SmtValue.Boolean
          (decide (cBV.toNat < 2 ^ (WN - 1)) ||
            (decide
                (2 ^ (WN + AN) - 2 ^ (WN - 1) - 1 ≤ cBV.toNat) ||
              false)) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp (by
        change RuleProofs.smt_value_rel
          (SmtValue.Boolean
            (decide (cBV.toNat < 2 ^ (WN - 1)) ||
              (decide
                  (2 ^ (WN + AN) - 2 ^ (WN - 1) - 1 ≤ cBV.toNat) ||
                false)))
          (SmtValue.Boolean true) at hOutsideRel
        exact hOutsideRel)
  have hOutsideDec :
      (decide (cBV.toNat < 2 ^ (WN - 1)) ||
        decide
          (2 ^ (WN + AN) - 2 ^ (WN - 1) - 1 ≤ cBV.toNat)) = true := by
    injection hOutsideEq with h
    simpa only [Bool.or_false] using h
  have hOutside :
      cBV.toNat < 2 ^ (WN - 1) ∨
        2 ^ (WN + AN) - 2 ^ (WN - 1) - 1 ≤ cBV.toNat := by
    by_cases hLow : cBV.toNat < 2 ^ (WN - 1)
    · exact Or.inl hLow
    · right
      rw [decide_eq_false hLow, Bool.false_or] at hOutsideDec
      exact of_decide_eq_true hOutsideDec
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst3Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Boolean
          (decide (cBV.toNat < (xBV.signExtend (WN + AN)).toNat)) := by
    unfold bvSignExtendUltConst3Lhs
    rw [eval_bvult_term_local, hConstEval, hSignEval]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendUltConst3Rhs x c
              (Term.Numeral (native_zplus W A)) (Term.Numeral H))) =
        SmtValue.Boolean
          (decide ((cBV.extractLsb' 0 WN).toNat < xBV.toNat)) := by
    unfold bvSignExtendUltConst3Rhs
    rw [eval_bvult_term_local, hLowEval, hXEval]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt,
      SmtEval.native_zlt]
    norm_cast
  rw [hLhsEval, hRhsEval,
    sign_extend_ult_outside_rev xBV cBV hWNatPos hOutside]

private theorem facts_bv_sign_extend_ult_const_3_term
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSignExtendUltConst3Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvSignExtendUltConstOutside3Prem x c nm) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvSignExtendUltConst3Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
    hOutsidePrem hWidthPrem
  have hBool := typed_bv_sign_extend_ult_const_3_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_sign_extend_ult_const_3_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, H, rfl, rfl, rfl, hW0, hA0, hH0, _hHWide,
      hXSmtTy, hConstSmtTy, _hLowSmtTy, _hSignSmtTy⟩
  unfold bvSignExtendUltConst3Term bvZeroExtendEqConstEq
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSignExtendUltConst3Term, bvZeroExtendEqConstEq] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst3Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendUltConst3Rhs x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral H))))
    rw [sign_extend_ult_const_3_eval_eq M hM x c W A H
      hW0 hA0 hH0 hXSmtTy hConstSmtTy
      (by simpa using hOutsidePrem) (by simpa using hWidthPrem)]
    exact RuleProofs.smt_value_rel_refl _

def bvSignExtendUltConst1Program
    (x m c nm nm2 P1 P2 : Term) : Term :=
  __eo_prog_bv_sign_extend_ult_const_1 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2)

def bvSignExtendUltConst3Program
    (x m c nm nm2 P1 P2 : Term) : Term :=
  __eo_prog_bv_sign_extend_ult_const_3 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2)

private def bvSignExtendUltConstOutsideGuard
    (x c nm nm2 nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmTop nmAmt2 x2
      nm2W xW : Term) : Term :=
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
                      (__eo_and (__eo_eq nm nmC1) (__eo_eq c c1))
                      (__eo_eq nm nmOne))
                    (__eo_eq nm nmAmt1))
                  (__eo_eq x x1))
                (__eo_eq nm nmC2))
              (__eo_eq c c2))
            (__eo_eq nm nmTop))
          (__eo_eq nm nmAmt2))
        (__eo_eq x x2))
      (__eo_eq nm2 nm2W))
    (__eo_eq x xW)

private theorem bv_sign_extend_ult_const_outside_guard_refs
    {x c nm nm2 nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmTop nmAmt2 x2
      nm2W xW body : Term} :
    __eo_requires
        (bvSignExtendUltConstOutsideGuard x c nm nm2 nmC1 c1 nmOne
          nmAmt1 x1 nmC2 c2 nmTop nmAmt2 x2 nm2W xW)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nmC1 = nm ∧ c1 = c ∧ nmOne = nm ∧ nmAmt1 = nm ∧ x1 = x ∧
      nmC2 = nm ∧ c2 = c ∧ nmTop = nm ∧ nmAmt2 = nm ∧ x2 = x ∧
      nm2W = nm2 ∧ xW = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvSignExtendUltConstOutsideGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG11, hXW⟩
  rcases bv_extract_support_and_true hG11 with ⟨hG10, hNm2W⟩
  rcases bv_extract_support_and_true hG10 with ⟨hG9, hX2⟩
  rcases bv_extract_support_and_true hG9 with ⟨hG8, hNmAmt2⟩
  rcases bv_extract_support_and_true hG8 with ⟨hG7, hNmTop⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hC2⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hNmC2⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hX1⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hNmAmt1⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNmOne⟩
  rcases bv_extract_support_and_true hG2 with ⟨hNmC1, hC1⟩
  exact ⟨(bv_extract_support_eq_true hNmC1).symm,
    (bv_extract_support_eq_true hC1).symm,
    (bv_extract_support_eq_true hNmOne).symm,
    (bv_extract_support_eq_true hNmAmt1).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hNmC2).symm,
    (bv_extract_support_eq_true hC2).symm,
    (bv_extract_support_eq_true hNmTop).symm,
    (bv_extract_support_eq_true hNmAmt2).symm,
    (bv_extract_support_eq_true hX2).symm,
    (bv_extract_support_eq_true hNm2W).symm,
    (bv_extract_support_eq_true hXW).symm⟩

private def bvSignExtendUltConstOutside1PremRefs
    (nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2 : Term) :
    Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvule)
            (bvZeroExtendUltConstConst c1 nmC1))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvshl)
              (bvSignExtendUltConstOne nmOne))
            (bvSignExtendUltConstAmount x1 nmAmt1))))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvuge)
              (bvZeroExtendUltConstConst c2 nmC2))
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.bvshl)
                (Term.Apply (Term.UOp UserOp.bvnot)
                  (bvSignExtendUltConstZero nmZero)))
              (bvSignExtendUltConstAmount x2 nmAmt2))))
        (Term.Boolean false)))
    (Term.Boolean true)

private theorem bv_sign_extend_ult_const_1_premise_shape
    (x m c nm nm2 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst1Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    ∃ nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2 nm2W xW,
      P1 = bvSignExtendUltConstOutside1PremRefs
        nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2 ∧
      P2 = bvZeroExtendUltConstWidthPrem xW nm2W := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2 nm2W xW,
        P1 = bvSignExtendUltConstOutside1PremRefs
          nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2 ∧
        P2 = bvZeroExtendUltConstWidthPrem xW nm2W
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_ult_const_1.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 (by
        intro nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2 nm2W xW
          hP1 hP2
        cases hP1
        cases hP2
        exact hShape
          ⟨nmC1, c1, nmOne, nmAmt1, x1, nmC2, c2, nmZero, nmAmt2,
            x2, nm2W, xW, rfl, rfl⟩)

private theorem bv_sign_extend_ult_const_1_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst1Program x m c nm nm2
        (bvSignExtendUltConstOutside1Prem x c nm)
        (bvZeroExtendUltConstWidthPrem x nm2) =
      bvSignExtendUltConst1Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvSignExtendUltConst1Program bvSignExtendUltConstOutside1Prem
    bvZeroExtendUltConstWidthPrem bvSignExtendUltConstLowerBound
    bvSignExtendUltConstUpperBound bvSignExtendUltConstOne
    bvSignExtendUltConstZero bvSignExtendUltConstAmount
    bvZeroExtendUltConstBvsize bvZeroExtendUltConstConst
    bvZeroExtendEqConstEq
  rw [__eo_prog_bv_sign_extend_ult_const_1.eq_6
    x m c nm nm2 nm c nm nm x nm c nm nm x nm2 x
    hX hM hC hNm hNm2]
  simp [bvSignExtendUltConstOutsideGuard, bvSignExtendUltConst1Term,
    bvSignExtendUltConst1Lhs, bvSignExtendUltConst1Rhs,
    bvSignExtendEqConstSign, bvZeroExtendUltConstLow, bvExtractTerm,
    bvZeroExtendUltConstConst, bvZeroExtendEqConstEq,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bvSignExtendUltConst1Program_normalize
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvSignExtendUltConst1Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    P1 = bvSignExtendUltConstOutside1Prem x c nm ∧
      P2 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      bvSignExtendUltConst1Program x m c nm nm2 P1 P2 =
        bvSignExtendUltConst1Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_sign_extend_ult_const_1_premise_shape
      x m c nm nm2 P1 P2 hX hM hC hNm hNm2 hProg with
    ⟨nmC1, c1, nmOne, nmAmt1, x1, nmC2, c2, nmZero, nmAmt2, x2,
      nm2W, xW, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvSignExtendUltConst1Program bvSignExtendUltConstOutside1PremRefs
    bvZeroExtendUltConstWidthPrem bvSignExtendUltConstOne
    bvSignExtendUltConstZero bvSignExtendUltConstAmount
    bvZeroExtendUltConstBvsize bvZeroExtendUltConstConst
    bvZeroExtendEqConstEq at hReq
  rw [__eo_prog_bv_sign_extend_ult_const_1.eq_6
    x m c nm nm2 nmC1 c1 nmOne nmAmt1 x1 nmC2 c2 nmZero nmAmt2 x2
    nm2W xW hX hM hC hNm hNm2] at hReq
  rcases bv_sign_extend_ult_const_outside_guard_refs
      (by simpa [bvSignExtendUltConstOutsideGuard] using hReq) with
    ⟨hNmC1, hC1, hNmOne, hNmAmt1, hX1, hNmC2, hC2, hNmZero,
      hNmAmt2, hX2, hNm2W, hXW⟩
  subst nmC1; subst c1; subst nmOne; subst nmAmt1; subst x1
  subst nmC2; subst c2; subst nmZero; subst nmAmt2; subst x2
  subst nm2W; subst xW
  have hP1Canonical :
      P1 = bvSignExtendUltConstOutside1Prem x c nm := by
    simpa [bvSignExtendUltConstOutside1Prem,
      bvSignExtendUltConstOutside1PremRefs,
      bvSignExtendUltConstLowerBound, bvSignExtendUltConstUpperBound] using hP1
  have hP2Canonical : P2 = bvZeroExtendUltConstWidthPrem x nm2 := hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_sign_extend_ult_const_1_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

theorem typed_bv_sign_extend_ult_const_1_program
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof (bvSignExtendUltConst1Program x m c nm nm2 P1 P2) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst1Program x m c nm nm2 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst1Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst1Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_ult_const_1_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_sign_extend_ult_const_1_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof (bvSignExtendUltConst1Program x m c nm nm2 P1 P2) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvSignExtendUltConst1Program x m c nm nm2 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst1Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst1Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hOutsidePrem :
      eo_interprets M (bvSignExtendUltConstOutside1Prem x c nm) true := by
    simpa [hP1] using hP1True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_sign_extend_ult_const_1_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy hOutsidePrem hWidthPrem

private def bvSignExtendUltConstOutside3PremRefs
    (nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2 : Term) :
    Term :=
  bvZeroExtendEqConstEq
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.or)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.bvult)
            (bvZeroExtendUltConstConst c1 nmC1))
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvshl)
              (bvSignExtendUltConstOne nmOne1))
            (bvSignExtendUltConstAmount x1 nmAmt1))))
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.bvuge)
              (bvZeroExtendUltConstConst c2 nmC2))
            (Term.Apply (Term.UOp UserOp.bvnot)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.bvshl)
                  (bvSignExtendUltConstOne nmOne2))
                (bvSignExtendUltConstAmount x2 nmAmt2)))))
        (Term.Boolean false)))
    (Term.Boolean true)

private theorem bv_sign_extend_ult_const_3_premise_shape
    (x m c nm nm2 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst3Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    ∃ nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2 nm2W xW,
      P1 = bvSignExtendUltConstOutside3PremRefs
        nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2 ∧
      P2 = bvZeroExtendUltConstWidthPrem xW nm2W := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2 nm2W xW,
        P1 = bvSignExtendUltConstOutside3PremRefs
          nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2 ∧
        P2 = bvZeroExtendUltConstWidthPrem xW nm2W
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_ult_const_3.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 (by
        intro nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2
          nm2W xW hP1 hP2
        cases hP1
        cases hP2
        exact hShape
          ⟨nmC1, c1, nmOne1, nmAmt1, x1, nmC2, c2, nmOne2, nmAmt2,
            x2, nm2W, xW, rfl, rfl⟩)

private theorem bv_sign_extend_ult_const_3_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvSignExtendUltConst3Program x m c nm nm2
        (bvSignExtendUltConstOutside3Prem x c nm)
        (bvZeroExtendUltConstWidthPrem x nm2) =
      bvSignExtendUltConst3Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvSignExtendUltConst3Program bvSignExtendUltConstOutside3Prem
    bvZeroExtendUltConstWidthPrem bvSignExtendUltConst4UpperBound
    bvSignExtendUltConstLowerBound bvSignExtendUltConstOne
    bvSignExtendUltConstAmount bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstConst bvZeroExtendEqConstEq
  rw [__eo_prog_bv_sign_extend_ult_const_3.eq_6
    x m c nm nm2 nm c nm nm x nm c nm nm x nm2 x
    hX hM hC hNm hNm2]
  simp [bvSignExtendUltConstOutsideGuard, bvSignExtendUltConst3Term,
    bvSignExtendUltConst3Lhs, bvSignExtendUltConst3Rhs,
    bvSignExtendEqConstSign, bvZeroExtendUltConstLow, bvExtractTerm,
    bvZeroExtendUltConstConst, bvZeroExtendEqConstEq,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bvSignExtendUltConst3Program_normalize
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvSignExtendUltConst3Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    P1 = bvSignExtendUltConstOutside3Prem x c nm ∧
      P2 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      bvSignExtendUltConst3Program x m c nm nm2 P1 P2 =
        bvSignExtendUltConst3Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_sign_extend_ult_const_3_premise_shape
      x m c nm nm2 P1 P2 hX hM hC hNm hNm2 hProg with
    ⟨nmC1, c1, nmOne1, nmAmt1, x1, nmC2, c2, nmOne2, nmAmt2, x2,
      nm2W, xW, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvSignExtendUltConst3Program bvSignExtendUltConstOutside3PremRefs
    bvZeroExtendUltConstWidthPrem bvSignExtendUltConstOne
    bvSignExtendUltConstAmount bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstConst bvZeroExtendEqConstEq at hReq
  rw [__eo_prog_bv_sign_extend_ult_const_3.eq_6
    x m c nm nm2 nmC1 c1 nmOne1 nmAmt1 x1 nmC2 c2 nmOne2 nmAmt2 x2
    nm2W xW hX hM hC hNm hNm2] at hReq
  rcases bv_sign_extend_ult_const_outside_guard_refs
      (by simpa [bvSignExtendUltConstOutsideGuard] using hReq) with
    ⟨hNmC1, hC1, hNmOne1, hNmAmt1, hX1, hNmC2, hC2, hNmOne2,
      hNmAmt2, hX2, hNm2W, hXW⟩
  subst nmC1; subst c1; subst nmOne1; subst nmAmt1; subst x1
  subst nmC2; subst c2; subst nmOne2; subst nmAmt2; subst x2
  subst nm2W; subst xW
  have hP1Canonical :
      P1 = bvSignExtendUltConstOutside3Prem x c nm := by
    simpa [bvSignExtendUltConstOutside3Prem,
      bvSignExtendUltConstOutside3PremRefs,
      bvSignExtendUltConstLowerBound, bvSignExtendUltConst4UpperBound] using hP1
  have hP2Canonical : P2 = bvZeroExtendUltConstWidthPrem x nm2 := hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_sign_extend_ult_const_3_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

theorem typed_bv_sign_extend_ult_const_3_program
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof (bvSignExtendUltConst3Program x m c nm nm2 P1 P2) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendUltConst3Program x m c nm nm2 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst3Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst3Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_ult_const_3_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_sign_extend_ult_const_3_program
    (M : SmtModel) (hM : model_wf M)
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof (bvSignExtendUltConst3Program x m c nm nm2 P1 P2) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvSignExtendUltConst3Program x m c nm nm2 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendUltConst3Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendUltConst3Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hOutsidePrem :
      eo_interprets M (bvSignExtendUltConstOutside3Prem x c nm) true := by
    simpa [hP1] using hP1True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_sign_extend_ult_const_3_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy hOutsidePrem hWidthPrem
