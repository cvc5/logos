module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
public import Cpc.Proofs.RuleSupport.BvOverflowSupport
import all Cpc.Proofs.RuleSupport.BvOverflowSupport
public import Cpc.Proofs.RuleSupport.BvSdivElimSupport
import all Cpc.Proofs.RuleSupport.BvSdivElimSupport
public import Cpc.Proofs.RuleSupport.BvSubElimSupport
import all Cpc.Proofs.RuleSupport.BvSubElimSupport
public import Cpc.Proofs.RuleSupport.BvUsuboElimSupport
import all Cpc.Proofs.RuleSupport.BvUsuboElimSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport

public section

/-! Support for the `bv_saddo_eliminate` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

def bvSaddoZeroBit : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 0)

def bvSaddoNil (x : Term) : Term :=
  __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x)

def bvSaddoSum (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) x)
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) (bvSaddoNil x))

def bvSaddoBitEq (nm z bit : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSdivExtract nm z)) bit

def bvSaddoAnd (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

def bvSaddoOr (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b

def bvSaddoBranch (xSign ySign sumSign : Term) : Term :=
  bvSaddoAnd
    (bvSaddoAnd xSign (bvSaddoAnd ySign (Term.Boolean true)))
    (bvSaddoAnd sumSign (Term.Boolean true))

def bvSaddoRhs (x y nm : Term) : Term :=
  bvSaddoOr
    (bvSaddoBranch (bvSdivSign nm x) (bvSdivSign nm y)
      (bvSaddoBitEq nm (bvSaddoSum x y) bvSaddoZeroBit))
    (bvSaddoOr
      (bvSaddoBranch (bvSaddoBitEq nm x bvSaddoZeroBit)
        (bvSaddoBitEq nm y bvSaddoZeroBit)
        (bvSdivSign nm (bvSaddoSum x y)))
      (Term.Boolean false))

def bvSaddoLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) x) y

def bvSaddoTerm (x y nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSaddoLhs x y))
    (bvSaddoRhs x y nm)

private theorem typeof_or_bool_args (A B : Term) :
    __eo_typeof_or A B = Term.Bool -> A = Term.Bool ∧ B = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_or_bool_args A B h

private theorem typeof_bvSaddoAnd_inv {a b : Term} :
    __eo_typeof (bvSaddoAnd a b) = Term.Bool ->
    __eo_typeof a = Term.Bool ∧ __eo_typeof b = Term.Bool := by
  intro h
  exact typeof_or_bool_args _ _ (by have hsimpa := h; (try simp [bvSaddoAnd] at hsimpa ⊢); exact hsimpa)

private theorem typeof_bvSaddoOr_inv {a b : Term} :
    __eo_typeof (bvSaddoOr a b) = Term.Bool ->
    __eo_typeof a = Term.Bool ∧ __eo_typeof b = Term.Bool := by
  intro h
  exact typeof_or_bool_args _ _ (by have hsimpa := h; (try simp [bvSaddoOr] at hsimpa ⊢); exact hsimpa)

private theorem bv_saddo_rhs_x_sign_bool {x y nm : Term} :
    __eo_typeof (bvSaddoRhs x y nm) = Term.Bool ->
    __eo_typeof (bvSdivSign nm x) = Term.Bool := by
  intro h
  have hOuter := typeof_bvSaddoOr_inv h
  have hBranch := typeof_bvSaddoAnd_inv hOuter.1
  have hSigns := typeof_bvSaddoAnd_inv hBranch.1
  exact hSigns.1

private theorem bv_saddo_rhs_sum_sign_bool {x y nm : Term} :
    __eo_typeof (bvSaddoRhs x y nm) = Term.Bool ->
    __eo_typeof (bvSdivSign nm (bvSaddoSum x y)) = Term.Bool := by
  intro h
  have hOuter := typeof_bvSaddoOr_inv h
  have hRight := typeof_bvSaddoOr_inv hOuter.2
  have hBranch := typeof_bvSaddoAnd_inv hRight.1
  have hSumTrue := typeof_bvSaddoAnd_inv hBranch.2
  exact hSumTrue.1

theorem bvSaddo_nil_ne (x y nm : Term) :
    __eo_typeof (bvSaddoTerm x y nm) = Term.Bool ->
    bvSaddoNil x ≠ Term.Stuck := by
  intro hTy hNil
  have hRhsTy : __eo_typeof (bvSaddoRhs x y nm) = Term.Bool := by
    have hEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _
      (by have hsimpa := hTy; (try simp [bvSaddoTerm] at hsimpa ⊢); exact hsimpa)
    have hLhsNe := (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hTy; (try simp [bvSaddoTerm] at hsimpa ⊢); exact hsimpa)).1
    change __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) ≠
      Term.Stuck at hLhsNe
    rcases typeof_bvult_args_of_ne_stuck hLhsNe with ⟨w, hXTy, hYTy⟩
    have hLhsTy : __eo_typeof (bvSaddoLhs x y) = Term.Bool := by
      change __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool
      rw [hXTy, hYTy] at hLhsNe ⊢
      cases w <;> simp [__eo_typeof_bvult, __eo_requires, __eo_eq,
        native_ite, native_teq, native_not] at hLhsNe ⊢
    rw [hLhsTy] at hEq
    exact hEq.symm
  have hSignTy := bv_saddo_rhs_sum_sign_bool hRhsTy
  have hExtractNe :
      __eo_typeof (bvSdivExtract nm (bvSaddoSum x y)) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hSignTy; (try simp [bvSdivSign] at hsimpa ⊢); exact hsimpa)).1
  apply hExtractNe
  unfold bvSdivExtract bvSaddoSum
  rw [show bvSaddoNil x = Term.Stuck from hNil]
  change __eo_typeof_extract (__eo_typeof nm) nm (__eo_typeof nm) nm
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof_bvand (__eo_typeof y) Term.Stuck)) = Term.Stuck
  simp [__eo_typeof_bvand]
  unfold __eo_typeof_extract
  split <;> simp_all

private theorem bv_saddo_context (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSaddoTerm x y nm) = Term.Bool ->
    ∃ w n : native_Int,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      __eo_typeof y =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      nm = Term.Numeral n ∧
      native_zleq 0 w = true ∧ native_zleq 0 n = true ∧
      native_zlt n w = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ∧
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) ∧
      bvSaddoNil x ≠ Term.Stuck := by
  intro hXTrans hYTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult (__eo_typeof x) (__eo_typeof y))
      (__eo_typeof (bvSaddoRhs x y nm)) = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases typeof_bvult_args_of_ne_stuck hOps.1 with
    ⟨widthTerm, hXTy, hYTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x widthTerm
      hXTrans hXTy with ⟨w, hWidth, hw0, hXSmtTy⟩
  subst widthTerm
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) := by
    have hsimpa :=
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        y (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
        (__eo_to_smt y) rfl hYTrans hYTy)
    try simp [__eo_to_smt_type, hw0] at hsimpa ⊢
    exact hsimpa
  have hLhsTy :
      __eo_typeof_bvult (__eo_typeof x) (__eo_typeof y) = Term.Bool := by
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvult, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  rw [hLhsTy] at hTypeEq
  have hRhsTy : __eo_typeof (bvSaddoRhs x y nm) = Term.Bool := hTypeEq.symm
  have hSignTy := bv_saddo_rhs_x_sign_bool hRhsTy
  have hExtractNe : __eo_typeof (bvSdivExtract nm x) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hSignTy; (try simp [bvSdivSign] at hsimpa ⊢); exact hsimpa)).1
  rcases bv_extract_context_of_non_stuck x nm nm hXTrans
      (by have hsimpa := hExtractNe; (try simp [bvSdivExtract] at hsimpa ⊢); exact hsimpa) with
    ⟨w', nHi, nLo, hXTy', hNmHi, hNmLo, hw'0, hn0, hnW,
      _hOne0, hXSmtTy'⟩
  have hWNat : native_int_to_nat w' = native_int_to_nat w := by
    rw [hXSmtTy] at hXSmtTy'
    exact (SmtType.BitVec.inj hXSmtTy').symm
  have hW' : w' = w :=
    nonneg_int_eq_of_toNat_eq w' w hw'0 hw0 hWNat
  subst w'
  have hN : nLo = nHi := by
    rw [hNmHi] at hNmLo
    injection hNmLo with h
    exact h.symm
  subst nLo
  exact ⟨w, nHi, hXTy, hYTy, hNmHi, hw0, hn0, hnW,
    hXSmtTy, hYSmtTy, bvSaddo_nil_ne x y nm (by
      have hsimpa := hResultTy; (try simp [bvSaddoTerm] at hsimpa ⊢); exact hsimpa)⟩

private theorem eo_has_bool_type_or_of_bool_args (a b : Term) :
    RuleProofs.eo_has_bool_type a -> RuleProofs.eo_has_bool_type b ->
    RuleProofs.eo_has_bool_type (bvSaddoOr a b) := by
  intro ha hb
  unfold RuleProofs.eo_has_bool_type at ha hb ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [ha, hb, native_ite]

private theorem eo_has_bool_type_false :
    RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  rfl

private theorem typed_bv_saddo_term (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSaddoTerm x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSaddoTerm x y nm) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_saddo_context x y nm hXTrans hYTrans hResultTy with
    ⟨w, n, _hXTy, _hYTy, rfl, hw0, hn0, hnW,
      hXSmtTy, hYSmtTy, hNilNe⟩
  let W := native_int_to_nat w
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  have hXTypeSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec W := by
    exact (TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans).symm.trans
      hXSmtTyW
  have hNilTy := smt_typeof_bvadd_nil x W hXTypeSmt hNilNe
  have hInnerSumTy :
      __smtx_typeof
          (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt (bvSaddoNil x))) =
        SmtType.BitVec W :=
    smt_typeof_bvbin_same SmtTerm.bvadd
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hYSmtTyW hNilTy
  have hSumTy :
      __smtx_typeof (__eo_to_smt (bvSaddoSum x y)) = SmtType.BitVec W := by
    change __smtx_typeof
      (SmtTerm.bvadd (__eo_to_smt x)
        (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt (bvSaddoNil x)))) = _
    exact smt_typeof_bvbin_same SmtTerm.bvadd
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hXSmtTyW hInnerSumTy
  have hOneIndex : native_zplus (native_zplus n 1) (native_zneg n) = 1 := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg]
    rw [Int.add_comm n 1]
    exact Int.add_neg_cancel_right 1 n
  have hOneWidth :
      native_zlt 0 (native_zplus (native_zplus n 1) (native_zneg n)) =
        true := by
    rw [hOneIndex]
    decide
  have extractTy (z : Term)
      (hz : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec W) :
      __smtx_typeof (__eo_to_smt (bvSdivExtract (Term.Numeral n) z)) =
        SmtType.BitVec 1 := by
    have h := smt_typeof_extract_of_context z w n n
      (by simpa [W] using hz) hw0 hn0 hnW hOneWidth
    have hsimpa := h
    try simp [bvSdivExtract, hOneIndex, native_int_to_nat, SmtEval.native_int_to_nat] at hsimpa ⊢
    exact hsimpa
  have hExtractXTy := extractTy x hXSmtTyW
  have hExtractYTy := extractTy y hYSmtTyW
  have hExtractSumTy := extractTy (bvSaddoSum x y) hSumTy
  have hOneTy :
      __smtx_typeof (__eo_to_smt bvSdivBitOne) = SmtType.BitVec 1 := by
    simpa [bvSdivBitOne, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 1 1 (by decide)
  have hZeroTy :
      __smtx_typeof (__eo_to_smt bvSaddoZeroBit) = SmtType.BitVec 1 := by
    simpa [bvSaddoZeroBit, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 0 1 (by decide)
  have eqBitTy (z bit : Term)
      (hz : __smtx_typeof (__eo_to_smt
        (bvSdivExtract (Term.Numeral n) z)) = SmtType.BitVec 1)
      (hb : __smtx_typeof (__eo_to_smt bit) = SmtType.BitVec 1) :
      RuleProofs.eo_has_bool_type
        (bvSaddoBitEq (Term.Numeral n) z bit) := by
    unfold bvSaddoBitEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hz.trans hb.symm) (by rw [hz]; intro h; cases h)
  have hXOne := eqBitTy x bvSdivBitOne hExtractXTy hOneTy
  have hYOne := eqBitTy y bvSdivBitOne hExtractYTy hOneTy
  have hSumZero := eqBitTy (bvSaddoSum x y) bvSaddoZeroBit
    hExtractSumTy hZeroTy
  have hXZero := eqBitTy x bvSaddoZeroBit hExtractXTy hZeroTy
  have hYZero := eqBitTy y bvSaddoZeroBit hExtractYTy hZeroTy
  have hSumOne := eqBitTy (bvSaddoSum x y) bvSdivBitOne
    hExtractSumTy hOneTy
  have hTrue := RuleProofs.eo_has_bool_type_true
  have branchTy (a b c : Term)
      (ha : RuleProofs.eo_has_bool_type a)
      (hb : RuleProofs.eo_has_bool_type b)
      (hc : RuleProofs.eo_has_bool_type c) :
      RuleProofs.eo_has_bool_type (bvSaddoBranch a b c) := by
    unfold bvSaddoBranch bvSaddoAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ ha
        (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hb hTrue))
      (RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hc hTrue)
  have hNegBranch := branchTy _ _ _
    (by simpa [bvSaddoBitEq, bvSdivSign] using hXOne)
    (by simpa [bvSaddoBitEq, bvSdivSign] using hYOne) hSumZero
  have hPosBranch := branchTy _ _ _ hXZero hYZero
    (by simpa [bvSaddoBitEq, bvSdivSign] using hSumOne)
  have hRhsBool : RuleProofs.eo_has_bool_type
      (bvSaddoRhs x y (Term.Numeral n)) := by
    unfold bvSaddoRhs
    exact eo_has_bool_type_or_of_bool_args _ _ hNegBranch
      (eo_has_bool_type_or_of_bool_args _ _ hPosBranch eo_has_bool_type_false)
  have hLhsBool : RuleProofs.eo_has_bool_type (bvSaddoLhs x y) := by
    change __smtx_typeof
      (SmtTerm.bvsaddo (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_bv_op_2_ret, hXSmtTyW, hYSmtTyW,
      native_nateq, native_ite]
  unfold bvSaddoTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm) (by rw [hLhsBool]; intro h; cases h)

def bvSaddoFormula (sx sy ss : Bool) : Bool :=
  (sx && sy && !ss) || (!sx && !sy && ss)

theorem bv1_eq_zero (b : Bool) :
    __smtx_model_eval_eq (bv1 b) (SmtValue.Binary 1 0) =
      SmtValue.Boolean (!b) := by
  cases b <;> simp [bv1, __smtx_model_eval_eq, native_veq]

theorem eval_bvSaddo_one_bit (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt bvSdivBitOne) =
      SmtValue.Binary 1 1 := by
  have h := eval_bv_const M 1 1 (by decide)
  have hsimpa := h
  try simp [bvSdivBitOne, SmtEval.native_mod_total] at hsimpa ⊢
  exact hsimpa

theorem eval_bvSaddo_zero_bit (M : SmtModel) :
    __smtx_model_eval M (__eo_to_smt bvSaddoZeroBit) =
      SmtValue.Binary 1 0 := by
  have h := eval_bv_const M 0 1 (by decide)
  simpa [bvSaddoZeroBit, SmtEval.native_mod_total] using h

theorem eval_bvSaddoBitEq_one
    (M : SmtModel) (nm z : Term) (b : Bool) :
    __smtx_model_eval M (__eo_to_smt (bvSdivExtract nm z)) = bv1 b ->
    __smtx_model_eval M
        (__eo_to_smt (bvSaddoBitEq nm z bvSdivBitOne)) =
      SmtValue.Boolean b := by
  intro h
  unfold bvSaddoBitEq
  change __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt (bvSdivExtract nm z))
        (__eo_to_smt bvSdivBitOne)) = _
  rw [smtx_eval_eq_term_eq, h, eval_bvSaddo_one_bit]
  exact bv1_eq_one b

theorem eval_bvSaddoBitEq_zero
    (M : SmtModel) (nm z : Term) (b : Bool) :
    __smtx_model_eval M (__eo_to_smt (bvSdivExtract nm z)) = bv1 b ->
    __smtx_model_eval M
        (__eo_to_smt (bvSaddoBitEq nm z bvSaddoZeroBit)) =
      SmtValue.Boolean (!b) := by
  intro h
  unfold bvSaddoBitEq
  change __smtx_model_eval M
      (SmtTerm.eq (__eo_to_smt (bvSdivExtract nm z))
        (__eo_to_smt bvSaddoZeroBit)) = _
  rw [smtx_eval_eq_term_eq, h, eval_bvSaddo_zero_bit]
  exact bv1_eq_zero b

theorem eval_bvSaddoAnd
    (M : SmtModel) (a b : Term) (ba bb : Bool) :
    __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean ba ->
    __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean bb ->
    __smtx_model_eval M (__eo_to_smt (bvSaddoAnd a b)) =
      SmtValue.Boolean (ba && bb) := by
  intro ha hb
  unfold bvSaddoAnd
  change __smtx_model_eval M
      (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [smtx_eval_and_term_eq, ha, hb]
  rfl

theorem eval_bvSaddoOr
    (M : SmtModel) (a b : Term) (ba bb : Bool) :
    __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean ba ->
    __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean bb ->
    __smtx_model_eval M (__eo_to_smt (bvSaddoOr a b)) =
      SmtValue.Boolean (ba || bb) := by
  intro ha hb
  unfold bvSaddoOr
  change __smtx_model_eval M
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [smtx_eval_or_term_eq, ha, hb]
  rfl

theorem eval_bvSaddoBranch
    (M : SmtModel) (a b c : Term) (ba bb bc : Bool) :
    __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean ba ->
    __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean bb ->
    __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean bc ->
    __smtx_model_eval M (__eo_to_smt (bvSaddoBranch a b c)) =
      SmtValue.Boolean (ba && bb && bc) := by
  intro ha hb hc
  have hTrue :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  have hBTrue := eval_bvSaddoAnd M b (Term.Boolean true) bb true hb hTrue
  have hAB := eval_bvSaddoAnd M a
    (bvSaddoAnd b (Term.Boolean true)) ba (bb && true) ha hBTrue
  have hCTrue := eval_bvSaddoAnd M c (Term.Boolean true) bc true hc hTrue
  have hAll := eval_bvSaddoAnd M
    (bvSaddoAnd a (bvSaddoAnd b (Term.Boolean true)))
    (bvSaddoAnd c (Term.Boolean true))
    (ba && (bb && true)) (bc && true) hAB hCTrue
  simpa [bvSaddoBranch] using hAll

private theorem smtx_eval_bvadd_term_eq_saddo
    (M : SmtModel) (a b : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvadd a b) =
      __smtx_model_eval_bvadd
        (__smtx_model_eval M a) (__smtx_model_eval M b) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem eval_bvSaddoSum
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int))
    (hA : A < 2 ^ W) (hB : B < 2 ^ W)
    (hXTypeSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec W)
    (hNilNe : bvSaddoNil x ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (bvSaddoSum x y)) =
      SmtValue.Binary (native_nat_to_int W)
        (((A + B) % 2 ^ W : Nat) : Int) := by
  have hNilEval :
      __smtx_model_eval M (__eo_to_smt (bvSaddoNil x)) =
        SmtValue.Binary (native_nat_to_int W) 0 := by
    simpa [bvSaddoNil] using
      smt_eval_bvadd_nil M x W hXTypeSmt hNilNe
  have hBMod :
      native_mod_total (B : Int)
          (native_int_pow2 (native_nat_to_int W)) = (B : Int) := by
    rw [native_int_pow2_nat]
    exact native_mod_nat_of_lt (Nat.two_pow_pos W) hB
  have hSumMod :
      native_mod_total ((A + B : Nat) : Int)
          (native_int_pow2 (native_nat_to_int W)) =
        (((A + B) % 2 ^ W : Nat) : Int) := by
    rw [native_int_pow2_nat]
    unfold native_mod_total
    exact (Int.natCast_emod (A + B) (2 ^ W)).symm
  change __smtx_model_eval M
      (SmtTerm.bvadd (__eo_to_smt x)
        (SmtTerm.bvadd (__eo_to_smt y) (__eo_to_smt (bvSaddoNil x)))) = _
  rw [smtx_eval_bvadd_term_eq_saddo,
    smtx_eval_bvadd_term_eq_saddo, hx, hy, hNilEval]
  change SmtValue.Binary (native_nat_to_int W)
      (native_mod_total
        (native_zplus (A : Int)
          (native_mod_total (native_zplus (B : Int) 0)
            (native_int_pow2 (native_nat_to_int W))))
        (native_int_pow2 (native_nat_to_int W))) = _
  simp only [SmtEval.native_zplus, Int.add_zero]
  rw [hBMod]
  have hCast : (A : Int) + (B : Int) = ((A + B : Nat) : Int) := by
    norm_cast
  rw [hCast, hSumMod]

theorem eval_bvSaddoRhs
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hW : 0 < W)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int))
    (hA : A < 2 ^ W) (hB : B < 2 ^ W)
    (hXTypeSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec W)
    (hNilNe : bvSaddoNil x ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvSaddoRhs x y
            (Term.Numeral (native_nat_to_int (W - 1))))) =
      SmtValue.Boolean
        (bvSaddoFormula (A.testBit (W - 1)) (B.testBit (W - 1))
          (((A + B) % 2 ^ W).testBit (W - 1))) := by
  let S := (A + B) % 2 ^ W
  have hSum := eval_bvSaddoSum M x y W A B hx hy hA hB hXTypeSmt hNilNe
  have hSNonneg : (0 : Int) ≤ (S : Int) := Int.natCast_nonneg S
  have hXBit := eval_extract_bit_term M x (native_nat_to_int W) (A : Int)
    (W - 1) hx (Int.natCast_nonneg A)
  have hYBit := eval_extract_bit_term M y (native_nat_to_int W) (B : Int)
    (W - 1) hy (Int.natCast_nonneg B)
  have hSumBit := eval_extract_bit_term M (bvSaddoSum x y)
    (native_nat_to_int W) (S : Int) (W - 1)
    (by simpa [S] using hSum) hSNonneg
  let nm := Term.Numeral (native_nat_to_int (W - 1))
  have hXOne :
      __smtx_model_eval M (__eo_to_smt (bvSdivSign nm x)) =
        SmtValue.Boolean (A.testBit (W - 1)) := by
    simpa [bvSdivSign, bvSaddoBitEq] using
      eval_bvSaddoBitEq_one M nm x (A.testBit (W - 1))
        (by simpa [nm, bvSdivExtract] using hXBit)
  have hYOne :
      __smtx_model_eval M (__eo_to_smt (bvSdivSign nm y)) =
        SmtValue.Boolean (B.testBit (W - 1)) := by
    simpa [bvSdivSign, bvSaddoBitEq] using
      eval_bvSaddoBitEq_one M nm y (B.testBit (W - 1))
        (by simpa [nm, bvSdivExtract] using hYBit)
  have hSumOne :
      __smtx_model_eval M
          (__eo_to_smt (bvSdivSign nm (bvSaddoSum x y))) =
        SmtValue.Boolean (S.testBit (W - 1)) := by
    simpa [bvSdivSign, bvSaddoBitEq] using
      eval_bvSaddoBitEq_one M nm (bvSaddoSum x y) (S.testBit (W - 1))
        (by simpa [nm, bvSdivExtract] using hSumBit)
  have hXZero := eval_bvSaddoBitEq_zero M nm x (A.testBit (W - 1))
    (by simpa [nm, bvSdivExtract] using hXBit)
  have hYZero := eval_bvSaddoBitEq_zero M nm y (B.testBit (W - 1))
    (by simpa [nm, bvSdivExtract] using hYBit)
  have hSumZero := eval_bvSaddoBitEq_zero M nm (bvSaddoSum x y)
    (S.testBit (W - 1))
    (by simpa [nm, bvSdivExtract] using hSumBit)
  have hNegBranch := eval_bvSaddoBranch M
    (bvSdivSign nm x) (bvSdivSign nm y)
    (bvSaddoBitEq nm (bvSaddoSum x y) bvSaddoZeroBit)
    (A.testBit (W - 1)) (B.testBit (W - 1))
    (!(S.testBit (W - 1))) hXOne hYOne hSumZero
  have hPosBranch := eval_bvSaddoBranch M
    (bvSaddoBitEq nm x bvSaddoZeroBit)
    (bvSaddoBitEq nm y bvSaddoZeroBit)
    (bvSdivSign nm (bvSaddoSum x y))
    (!(A.testBit (W - 1))) (!(B.testBit (W - 1)))
    (S.testBit (W - 1)) hXZero hYZero hSumOne
  have hFalse :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by rfl
  have hRight := eval_bvSaddoOr M
    (bvSaddoBranch (bvSaddoBitEq nm x bvSaddoZeroBit)
      (bvSaddoBitEq nm y bvSaddoZeroBit)
      (bvSdivSign nm (bvSaddoSum x y)))
    (Term.Boolean false)
    ((!A.testBit (W - 1)) && (!B.testBit (W - 1)) &&
      S.testBit (W - 1)) false hPosBranch hFalse
  have hOuter := eval_bvSaddoOr M
    (bvSaddoBranch (bvSdivSign nm x) (bvSdivSign nm y)
      (bvSaddoBitEq nm (bvSaddoSum x y) bvSaddoZeroBit))
    (bvSaddoOr
      (bvSaddoBranch (bvSaddoBitEq nm x bvSaddoZeroBit)
        (bvSaddoBitEq nm y bvSaddoZeroBit)
        (bvSdivSign nm (bvSaddoSum x y)))
      (Term.Boolean false))
    (A.testBit (W - 1) && B.testBit (W - 1) &&
      !S.testBit (W - 1))
    (((!A.testBit (W - 1)) && (!B.testBit (W - 1)) &&
      S.testBit (W - 1)) || false) hNegBranch hRight
  simpa [bvSaddoRhs, bvSaddoFormula, nm, S] using hOuter

private theorem bvSaddoFormula_eq_sign_circuit (sx sy ss : Bool) :
    bvSaddoFormula sx sy ss =
      ((sx == sy) && !((ss == sx))) := by
  cases sx <;> cases sy <;> cases ss <;> native_decide

theorem bitvec_msb_of_canonical
    (W A : Nat) (hA : A < 2 ^ W) :
    (BitVec.ofInt W (A : Int)).msb = A.testBit (W - 1) := by
  let a := BitVec.ofInt W (A : Int)
  have hToNat : a.toNat = A := by
    simpa [a] using ofInt_toNat_canonical W (A : Int)
      (Int.natCast_nonneg A) (by exact_mod_cast hA)
  rw [BitVec.msb_eq_getLsbD_last, ← BitVec.testBit_toNat, hToNat]

private theorem bitvec_add_msb_of_canonical
    (W A B : Nat) (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    (BitVec.ofInt W (A : Int) + BitVec.ofInt W (B : Int)).msb =
      ((A + B) % 2 ^ W).testBit (W - 1) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  have hAToNat : a.toNat = A := by
    simpa [a] using ofInt_toNat_canonical W (A : Int)
      (Int.natCast_nonneg A) (by exact_mod_cast hA)
  have hBToNat : b.toNat = B := by
    simpa [b] using ofInt_toNat_canonical W (B : Int)
      (Int.natCast_nonneg B) (by exact_mod_cast hB)
  rw [BitVec.msb_eq_getLsbD_last, ← BitVec.testBit_toNat,
    BitVec.toNat_add, hAToNat, hBToNat]

private theorem bvSaddoFormula_eq_saddOverflow
    (W A B : Nat) (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    bvSaddoFormula (A.testBit (W - 1)) (B.testBit (W - 1))
        (((A + B) % 2 ^ W).testBit (W - 1)) =
      BitVec.saddOverflow (BitVec.ofInt W (A : Int))
        (BitVec.ofInt W (B : Int)) := by
  rw [BitVec.saddOverflow_eq,
    bitvec_msb_of_canonical W A hA,
    bitvec_msb_of_canonical W B hB,
    bitvec_add_msb_of_canonical W A B hA hB]
  exact bvSaddoFormula_eq_sign_circuit _ _ _

theorem bvsaddo_value_eq_saddOverflow
    (W A B : Nat) (hW : 0 < W)
    (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval_bvsaddo
        (SmtValue.Binary (native_nat_to_int W) (A : Int))
        (SmtValue.Binary (native_nat_to_int W) (B : Int)) =
      SmtValue.Boolean
        (BitVec.saddOverflow (BitVec.ofInt W (A : Int))
          (BitVec.ofInt W (B : Int))) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  have hUtsA :
      native_binary_uts (native_nat_to_int W) (A : Int) = a.toInt := by
    simpa [a, native_nat_to_int] using
      native_binary_uts_eq_bitvec_toInt W (A : Int)
        (Int.natCast_nonneg A) (by exact_mod_cast hA)
  have hUtsB :
      native_binary_uts (native_nat_to_int W) (B : Int) = b.toInt := by
    simpa [b, native_nat_to_int] using
      native_binary_uts_eq_bitvec_toInt W (B : Int)
        (Int.natCast_nonneg B) (by exact_mod_cast hB)
  have hPred :
      native_zplus (native_nat_to_int W) (native_zneg 1) =
        native_nat_to_int (W - 1) := by
    have hOneLe : 1 ≤ W := hW
    change (W : Int) + -(1 : Int) = ((W - 1 : Nat) : Int)
    rw [Int.ofNat_sub hOneLe]
    rfl
  change SmtValue.Boolean
      (native_or
        (native_zleq
          (native_int_pow2
            (native_zplus (native_nat_to_int W) (native_zneg 1)))
          (native_zplus
            (native_binary_uts (native_nat_to_int W) (A : Int))
            (native_binary_uts (native_nat_to_int W) (B : Int))))
        (native_zlt
          (native_zplus
            (native_binary_uts (native_nat_to_int W) (A : Int))
            (native_binary_uts (native_nat_to_int W) (B : Int)))
          (native_zneg
            (native_int_pow2
              (native_zplus (native_nat_to_int W) (native_zneg 1)))))) = _
  rw [hPred, native_int_pow2_nat, hUtsA, hUtsB]
  rfl

theorem eval_bvSaddoLhs
    (M : SmtModel) (x y : Term) (W A B : Nat)
    (hW : 0 < W)
    (hx : __smtx_model_eval M (__eo_to_smt x) =
      SmtValue.Binary (native_nat_to_int W) (A : Int))
    (hy : __smtx_model_eval M (__eo_to_smt y) =
      SmtValue.Binary (native_nat_to_int W) (B : Int))
    (hA : A < 2 ^ W) (hB : B < 2 ^ W) :
    __smtx_model_eval M (__eo_to_smt (bvSaddoLhs x y)) =
      SmtValue.Boolean
        (bvSaddoFormula (A.testBit (W - 1)) (B.testBit (W - 1))
          (((A + B) % 2 ^ W).testBit (W - 1))) := by
  let a := BitVec.ofInt W (A : Int)
  let b := BitVec.ofInt W (B : Int)
  have hUtsA :
      native_binary_uts (native_nat_to_int W) (A : Int) = a.toInt := by
    simpa [a, native_nat_to_int] using
      native_binary_uts_eq_bitvec_toInt W (A : Int)
        (Int.natCast_nonneg A) (by exact_mod_cast hA)
  have hUtsB :
      native_binary_uts (native_nat_to_int W) (B : Int) = b.toInt := by
    simpa [b, native_nat_to_int] using
      native_binary_uts_eq_bitvec_toInt W (B : Int)
        (Int.natCast_nonneg B) (by exact_mod_cast hB)
  have hPred :
      native_zplus (native_nat_to_int W) (native_zneg 1) =
        native_nat_to_int (W - 1) := by
    have hOneLe : 1 ≤ W := by omega
    change (W : Int) + -(1 : Int) = ((W - 1 : Nat) : Int)
    rw [Int.ofNat_sub hOneLe]
    rfl
  have hOverflow :
      bvSaddoFormula (A.testBit (W - 1)) (B.testBit (W - 1))
          (((A + B) % 2 ^ W).testBit (W - 1)) =
        BitVec.saddOverflow a b := by
    simpa [a, b] using bvSaddoFormula_eq_saddOverflow W A B hA hB
  change __smtx_model_eval M
      (SmtTerm.bvsaddo (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def]
  simp only
  rw [hx, hy]
  change SmtValue.Boolean
      (native_or
        (native_zleq
          (native_int_pow2
            (native_zplus (native_nat_to_int W) (native_zneg 1)))
          (native_zplus
            (native_binary_uts (native_nat_to_int W) (A : Int))
            (native_binary_uts (native_nat_to_int W) (B : Int))))
        (native_zlt
          (native_zplus
            (native_binary_uts (native_nat_to_int W) (A : Int))
            (native_binary_uts (native_nat_to_int W) (B : Int)))
          (native_zneg
            (native_int_pow2
              (native_zplus (native_nat_to_int W) (native_zneg 1)))))) = _
  rw [hPred, native_int_pow2_nat, hUtsA, hUtsB]
  rw [hOverflow]
  rfl

private theorem facts_bv_saddo_term
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSaddoTerm x y nm) = Term.Bool ->
    eo_interprets M (bvSaddoTerm x y nm) true := by
  intro hXTrans hYTrans hPrem hResultTy
  rcases bv_saddo_context x y nm hXTrans hYTrans hResultTy with
    ⟨w, n, _hXTy, _hYTy, rfl, hw0, hn0, hnW,
      hXSmtTy, hYSmtTy, hNilNe⟩
  have hIndex : n = w - 1 :=
    bv_sdiv_index_eq_of_premise M x w n hPrem hw0 hXSmtTy
  let W := native_int_to_nat w
  have hRound : native_nat_to_int W = w :=
    native_nat_to_int_int_to_nat_eq w hw0
  have hnNonneg : 0 ≤ n := by
    simpa [SmtEval.native_zleq] using hn0
  have hnLtW : n < w := by
    simpa [SmtEval.native_zlt] using hnW
  have hwPos : 0 < w := Int.lt_of_le_of_lt hnNonneg hnLtW
  have hW : 0 < W := by
    rw [← hRound] at hwPos
    have hwPos' : (0 : Int) < (W : Int) := by
      simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hwPos
    exact_mod_cast hwPos'
  have hOneLe : 1 ≤ W := hW
  have hIndexNat : n = native_nat_to_int (W - 1) := by
    rw [hIndex, ← hRound]
    change (W : Int) - 1 = ((W - 1 : Nat) : Int)
    rw [Int.ofNat_sub hOneLe]
    rfl
  have hXSmtTyW : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  have hXTypeSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec W :=
    (TranslationProofs.eo_to_smt_typeof_matches_translation x hXTrans).symm.trans
      hXSmtTyW
  rcases bitvec_eval_nat_payload M hM x W hXSmtTyW with
    ⟨A, hXEval, hABound⟩
  rcases bitvec_eval_nat_payload M hM y W hYSmtTyW with
    ⟨B, hYEval, hBBound⟩
  have hLhsEval := eval_bvSaddoLhs M x y W A B hW
    hXEval hYEval hABound hBBound
  have hRhsEval := eval_bvSaddoRhs M x y W A B hW
    hXEval hYEval hABound hBBound hXTypeSmt hNilNe
  have hBool := typed_bv_saddo_term x y (Term.Numeral n)
    hXTrans hYTrans hResultTy
  unfold bvSaddoTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSaddoTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvSaddoLhs x y)))
      (__smtx_model_eval M
        (__eo_to_smt (bvSaddoRhs x y (Term.Numeral n))))
    rw [hLhsEval]
    simpa [hIndexNat] using
      (show RuleProofs.smt_value_rel
          (SmtValue.Boolean
            (bvSaddoFormula (A.testBit (W - 1)) (B.testBit (W - 1))
              (((A + B) % 2 ^ W).testBit (W - 1))))
          (__smtx_model_eval M
            (__eo_to_smt
              (bvSaddoRhs x y
                (Term.Numeral (native_nat_to_int (W - 1)))))) from by
        rw [hRhsEval]
        exact RuleProofs.smt_value_rel_refl _)

def bvSaddoProgram (x y nm : Term) : Term :=
  __eo_prog_bv_saddo_eliminate x y nm (Proof.pf (bvSdivPrem x nm))

private theorem bv_saddo_program_eq_term_of_ne_stuck_and_nil
    (x y nm : Term) :
    x ≠ Term.Stuck -> y ≠ Term.Stuck -> nm ≠ Term.Stuck ->
    bvSaddoNil x ≠ Term.Stuck ->
    bvSaddoProgram x y nm = bvSaddoTerm x y nm := by
  intro hXNe hYNe hNmNe hNilNe
  have hNilNe' :
      __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) ≠ Term.Stuck := by
    simpa [bvSaddoNil] using hNilNe
  unfold bvSaddoProgram bvSdivPrem
  rw [__eo_prog_bv_saddo_eliminate.eq_4 x y nm nm x
    hXNe hYNe hNmNe]
  simp [bvSaddoTerm, bvSaddoLhs, bvSaddoRhs, bvSaddoBranch,
    bvSaddoAnd, bvSaddoOr, bvSaddoSum, bvSaddoNil, bvSaddoBitEq,
    bvSaddoZeroBit, bvSdivSign, bvSdivExtract, bvSdivBitOne,
    __eo_requires, __eo_and, __eo_eq, __eo_mk_apply,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hXNe, hNmNe, hNilNe']

theorem bv_saddo_program_eq_term_of_type_bool (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSaddoProgram x y nm) = Term.Bool ->
    bvSaddoProgram x y nm = bvSaddoTerm x y nm := by
  intro hXTrans hYTrans hNmTrans hTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNilNe : bvSaddoNil x ≠ Term.Stuck := by
    intro hNil
    have hNil' :
        __eo_nil (Term.UOp UserOp.bvadd) (__eo_typeof x) = Term.Stuck := by
      simpa [bvSaddoNil] using hNil
    have hProgStuck : bvSaddoProgram x y nm = Term.Stuck := by
      unfold bvSaddoProgram bvSdivPrem
      rw [__eo_prog_bv_saddo_eliminate.eq_4 x y nm nm x
        hXNe hYNe hNmNe]
      simp [bvSaddoNil, __eo_requires, __eo_and, __eo_eq, __eo_mk_apply,
        native_ite, native_teq, native_not, SmtEval.native_not,
        native_and, SmtEval.native_and, hXNe, hNmNe, hNil']
    rw [hProgStuck] at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
    exact hBad hTy
  exact bv_saddo_program_eq_term_of_ne_stuck_and_nil x y nm
    hXNe hYNe hNmNe hNilNe

theorem bv_saddo_eliminate_shape_of_ne_stuck (x y nm P : Term) :
    __eo_prog_bv_saddo_eliminate x y nm (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ nm ≠ Term.Stuck ∧
      ∃ pnm px, P = bvSdivPrem px pnm := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_saddo_eliminate.eq_1 y nm (Proof.pf P))
  have hYNe : y ≠ Term.Stuck := by
    intro hY
    subst y
    exact hProg
      (__eo_prog_bv_saddo_eliminate.eq_2 x nm (Proof.pf P) hXNe)
  have hNmNe : nm ≠ Term.Stuck := by
    intro hNm
    subst nm
    exact hProg
      (__eo_prog_bv_saddo_eliminate.eq_3 x y (Proof.pf P) hXNe hYNe)
  refine ⟨hXNe, hYNe, hNmNe, ?_⟩
  by_cases hShape : ∃ pnm px, P = bvSdivPrem px pnm
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_saddo_eliminate.eq_5 x y nm (Proof.pf P)
        hXNe hYNe hNmNe (by
          intro pnm px hP
          cases hP
          exact hShape ⟨pnm, px, rfl⟩)))

theorem typed_bv_saddo_program (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSaddoProgram x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSaddoProgram x y nm) := by
  intro hXTrans hYTrans hNmTrans hResultTy
  have hEq := bv_saddo_program_eq_term_of_type_bool x y nm
    hXTrans hYTrans hNmTrans hResultTy
  have hTermTy : __eo_typeof (bvSaddoTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_saddo_term x y nm hXTrans hYTrans hTermTy

theorem facts_bv_saddo_program
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSaddoProgram x y nm) = Term.Bool ->
    eo_interprets M (bvSaddoProgram x y nm) true := by
  intro hXTrans hYTrans hNmTrans hPrem hResultTy
  have hEq := bv_saddo_program_eq_term_of_type_bool x y nm
    hXTrans hYTrans hNmTrans hResultTy
  have hTermTy : __eo_typeof (bvSaddoTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_saddo_term M hM x y nm
    hXTrans hYTrans hPrem hTermTy
