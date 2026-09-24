module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
public import Cpc.Proofs.RuleSupport.TypeInversionSupport
import all Cpc.Proofs.RuleSupport.TypeInversionSupport
public import Cpc.Proofs.RuleSupport.BvNegoEliminateSupport
import all Cpc.Proofs.RuleSupport.BvNegoEliminateSupport

public section

/-! Support for the `bv_sdiv_eliminate` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvSdivBitOne : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 1)) (Term.Numeral 1)

def bvSdivExtract (nm z : Term) : Term :=
  Term.Apply (Term.UOp2 UserOp2.extract nm nm) z

def bvSdivSign (nm z : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSdivExtract nm z))
    bvSdivBitOne

def bvSdivAbs (nm z : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply (Term.UOp UserOp.ite) (bvSdivSign nm z))
      (Term.Apply (Term.UOp UserOp.bvneg) z)) z

def bvSdivQuot (x y nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) (bvSdivAbs nm x))
    (bvSdivAbs nm y)

def bvSdivRhs (x y nm : Term) : Term :=
  let q := bvSdivQuot x y nm
  Term.Apply
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.ite)
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) (bvSdivSign nm x))
          (bvSdivSign nm y)))
      (Term.Apply (Term.UOp UserOp.bvneg) q)) q

def bvSdivLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) x) y

def bvSdivTerm (x y nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSdivLhs x y))
    (bvSdivRhs x y nm)

def bvSdivPrem (x nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (Term.Apply (Term.UOp UserOp._at_bvsize) x)) (Term.Numeral 1))

theorem eo_typeof_bvbin_arg_types_of_ne_stuck
    {A B : Term} (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
      B = Term.Apply (Term.UOp UserOp.BitVec) w := by
  rcases RuleProofs.eo_typeof_bvand_args_of_ne_stuck A B h with
    ⟨w, hA, hB, _hW⟩
  exact ⟨w, hA, hB⟩

theorem typeof_ite_inv_nonstuck (C A B T : Term) :
    __eo_typeof_ite C A B = T -> T ≠ Term.Stuck ->
    C = Term.Bool ∧ A = T ∧ B = T := by
  intro h hT
  exact RuleProofs.eo_typeof_ite_eq_nonstuck_args C A B T h hT

private theorem typeof_or_bool_args (A B : Term) :
    __eo_typeof_or A B = Term.Bool -> A = Term.Bool ∧ B = Term.Bool := by
  intro h
  exact RuleProofs.eo_typeof_or_bool_args A B h

private theorem bv_sdiv_context (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSdivTerm x y nm) = Term.Bool ->
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
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hYTrans hResultTy
  change __eo_typeof_eq (__eo_typeof_bvand (__eo_typeof x) (__eo_typeof y))
      (__eo_typeof (bvSdivRhs x y nm)) = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hOps.1 with
    ⟨widthTerm, hXTy, hYTy⟩
  rcases _root_.smt_bitvec_type_of_eo_bitvec_type_with_width x widthTerm
      hXTrans hXTy with ⟨w, hWidth, hw0, hXSmtTy⟩
  subst widthTerm
  have hYSmtTy :
      __smtx_typeof (__eo_to_smt y) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [__eo_to_smt_type, hw0, __eo_to_smt, __smtx_typeof, native_int_to_nat, native_ite] using
      (RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        y (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
        (__eo_to_smt y) rfl hYTrans hYTy)
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hDivReduce :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRhsTy :
      __eo_typeof (bvSdivRhs x y nm) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
    rw [hDivReduce] at hTypeEq
    exact hTypeEq.symm
  have hWidthNe :
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ≠ Term.Stuck := by
    intro h
    cases h
  have hOuter := typeof_ite_inv_nonstuck
    (__eo_typeof
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) (bvSdivSign nm x))
        (bvSdivSign nm y)))
    (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg)
      (bvSdivQuot x y nm)))
    (__eo_typeof (bvSdivQuot x y nm))
    (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (by simpa [bvSdivRhs, __eo_typeof, __eo_typeof_ite, bvSdivQuot, bvSdivSign] using hRhsTy) hWidthNe
  have hSigns :
      __eo_typeof (bvSdivSign nm x) = Term.Bool ∧
        __eo_typeof (bvSdivSign nm y) = Term.Bool := by
    apply typeof_or_bool_args
    have hsimpa := hOuter.1
    try simp at hsimpa ⊢
    exact hsimpa
  have hExtractNe : __eo_typeof (bvSdivExtract nm x) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by simpa [bvSdivSign, __eo_typeof, __eo_typeof_or, __eo_typeof_eq, bvSdivBitOne, bvSdivExtract] using hSigns.1)).1
  rcases bv_extract_context_of_non_stuck x nm nm hXTrans
      (by simpa [bvSdivExtract, __eo_typeof, bvExtractTerm] using hExtractNe) with
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
    hXSmtTy, hYSmtTy⟩

theorem smt_typeof_bvneg_same (t : SmtTerm) (w : Nat) :
    __smtx_typeof t = SmtType.BitVec w ->
    __smtx_typeof (SmtTerm.bvneg t) = SmtType.BitVec w := by
  intro h
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, h]

theorem smt_typeof_bvbin_same
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hOp : ∀ a b, __smtx_typeof (op a b) =
      __smtx_typeof_bv_op_2 (__smtx_typeof a) (__smtx_typeof b))
    (a b : SmtTerm) (w : Nat) :
    __smtx_typeof a = SmtType.BitVec w ->
    __smtx_typeof b = SmtType.BitVec w ->
    __smtx_typeof (op a b) = SmtType.BitVec w := by
  intro ha hb
  rw [hOp]
  simp [__smtx_typeof_bv_op_2, ha, hb, native_nateq, native_ite]

private theorem typed_bv_sdiv_term (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSdivTerm x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSdivTerm x y nm) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_sdiv_context x y nm hXTrans hYTrans hResultTy with
    ⟨w, n, _hXTy, _hYTy, rfl, hw0, hn0, hnW, hXSmtTy, hYSmtTy⟩
  let W := native_int_to_nat w
  have hXSmtTyW :
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec W := by
    simpa [W] using hXSmtTy
  have hYSmtTyW :
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec W := by
    simpa [W] using hYSmtTy
  have hOneIndex :
      native_zplus (native_zplus n 1) (native_zneg n) = 1 := by
    simp [SmtEval.native_zplus, SmtEval.native_zneg]
    rw [Int.add_comm n 1]
    exact Int.add_neg_cancel_right 1 n
  have hOneWidth :
      native_zlt 0 (native_zplus (native_zplus n 1) (native_zneg n)) =
        true := by
    rw [hOneIndex]
    decide
  have hExtractXTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivExtract (Term.Numeral n) x)) = SmtType.BitVec 1 := by
    have h := smt_typeof_extract_of_context x w n n hXSmtTy hw0 hn0 hnW
      hOneWidth
    simpa [bvSdivExtract, hOneIndex, native_int_to_nat, SmtEval.native_int_to_nat, __eo_to_smt, __smtx_typeof, bvExtractTerm]
      using h
  have hExtractYTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivExtract (Term.Numeral n) y)) = SmtType.BitVec 1 := by
    have h := smt_typeof_extract_of_context y w n n hYSmtTy hw0 hn0 hnW
      hOneWidth
    have hsimpa := h
    try simp [bvSdivExtract, hOneIndex, native_int_to_nat, SmtEval.native_int_to_nat] at hsimpa ⊢
    exact hsimpa
  have hBitOneTy :
      __smtx_typeof (__eo_to_smt bvSdivBitOne) = SmtType.BitVec 1 := by
    simpa [bvSdivBitOne, native_int_to_nat, SmtEval.native_int_to_nat]
      using smt_typeof_bv_const 1 1 (by decide)
  have hSignXTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivSign (Term.Numeral n) x)) = SmtType.Bool := by
    unfold bvSdivSign
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hExtractXTy.trans hBitOneTy.symm) (by rw [hExtractXTy]; decide)
  have hSignYTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivSign (Term.Numeral n) y)) = SmtType.Bool := by
    unfold bvSdivSign
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hExtractYTy.trans hBitOneTy.symm) (by rw [hExtractYTy]; decide)
  have hNegXTy := smt_typeof_bvneg_same (__eo_to_smt x) W hXSmtTyW
  have hNegYTy := smt_typeof_bvneg_same (__eo_to_smt y) W hYSmtTyW
  have hAbsXTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivAbs (Term.Numeral n) x)) = SmtType.BitVec W := by
    change __smtx_typeof
      (SmtTerm.ite (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
        (SmtTerm.bvneg (__eo_to_smt x)) (__eo_to_smt x)) = _
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_ite, hSignXTy, hNegXTy, hXSmtTyW,
      native_Teq, native_ite]
  have hAbsYTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivAbs (Term.Numeral n) y)) = SmtType.BitVec W := by
    change __smtx_typeof
      (SmtTerm.ite (__eo_to_smt (bvSdivSign (Term.Numeral n) y))
        (SmtTerm.bvneg (__eo_to_smt y)) (__eo_to_smt y)) = _
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_ite, hSignYTy, hNegYTy, hYSmtTyW,
      native_Teq, native_ite]
  have hQuotTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivQuot x y (Term.Numeral n))) = SmtType.BitVec W := by
    apply smt_typeof_bvbin_same SmtTerm.bvudiv
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hAbsXTy hAbsYTy
  have hNegQuotTy := smt_typeof_bvneg_same
    (__eo_to_smt (bvSdivQuot x y (Term.Numeral n))) W hQuotTy
  have hCondTy :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor)
          (bvSdivSign (Term.Numeral n) x))
          (bvSdivSign (Term.Numeral n) y))) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.xor
      (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
      (__eo_to_smt (bvSdivSign (Term.Numeral n) y))) = _
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [hSignXTy, hSignYTy, native_Teq, native_ite]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt
        (bvSdivRhs x y (Term.Numeral n))) = SmtType.BitVec W := by
    change __smtx_typeof
      (SmtTerm.ite
        (SmtTerm.xor
          (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
          (__eo_to_smt (bvSdivSign (Term.Numeral n) y)))
        (SmtTerm.bvneg (__eo_to_smt (bvSdivQuot x y (Term.Numeral n))))
        (__eo_to_smt (bvSdivQuot x y (Term.Numeral n)))) = _
    change __smtx_typeof
      (SmtTerm.xor
        (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
        (__eo_to_smt (bvSdivSign (Term.Numeral n) y))) = SmtType.Bool at hCondTy
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_ite, hCondTy, hNegQuotTy, hQuotTy,
      native_Teq, native_ite]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (bvSdivLhs x y)) = SmtType.BitVec W := by
    apply smt_typeof_bvbin_same SmtTerm.bvsdiv
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hXSmtTyW hYSmtTyW
  unfold bvSdivTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; intro h; cases h)

noncomputable def bvSdivSignValue
    (n : native_Int) (v : SmtValue) : SmtValue :=
  __smtx_model_eval_eq
    (__smtx_model_eval_extract (SmtValue.Numeral n) (SmtValue.Numeral n) v)
    (SmtValue.Binary 1 1)

noncomputable def bvSdivAbsValue
    (n : native_Int) (v : SmtValue) : SmtValue :=
  __smtx_model_eval_ite (bvSdivSignValue n v)
    (__smtx_model_eval_bvneg v) v

private noncomputable def bvSdivRhsValue
    (n : native_Int) (x y : SmtValue) : SmtValue :=
  let q := __smtx_model_eval_bvudiv
    (bvSdivAbsValue n x) (bvSdivAbsValue n y)
  __smtx_model_eval_ite
    (__smtx_model_eval_xor (bvSdivSignValue n x) (bvSdivSignValue n y))
    (__smtx_model_eval_bvneg q) q

private noncomputable def bvSdivExpandedValue
    (sx sy x y : SmtValue) : SmtValue :=
  __smtx_model_eval_ite
    (__smtx_model_eval_and (__smtx_model_eval_not sx)
      (__smtx_model_eval_not sy))
    (__smtx_model_eval_bvudiv x y)
    (__smtx_model_eval_ite
      (__smtx_model_eval_and sx (__smtx_model_eval_not sy))
      (__smtx_model_eval_bvneg
        (__smtx_model_eval_bvudiv (__smtx_model_eval_bvneg x) y))
      (__smtx_model_eval_ite
        (__smtx_model_eval_and (__smtx_model_eval_not sx) sy)
        (__smtx_model_eval_bvneg
          (__smtx_model_eval_bvudiv x (__smtx_model_eval_bvneg y)))
        (__smtx_model_eval_bvudiv
          (__smtx_model_eval_bvneg x) (__smtx_model_eval_bvneg y))))

private theorem bv_sdiv_compact_value
    (x y : SmtValue) (bx bY : Bool) :
    (let sx := SmtValue.Boolean bx
     let sy := SmtValue.Boolean bY
     let q := __smtx_model_eval_bvudiv
       (__smtx_model_eval_ite sx (__smtx_model_eval_bvneg x) x)
       (__smtx_model_eval_ite sy (__smtx_model_eval_bvneg y) y)
     __smtx_model_eval_ite (__smtx_model_eval_xor sx sy)
       (__smtx_model_eval_bvneg q) q) =
      bvSdivExpandedValue
        (SmtValue.Boolean bx) (SmtValue.Boolean bY) x y := by
  cases bx <;> cases bY <;>
    simp [bvSdivExpandedValue, __smtx_model_eval_and,
      __smtx_model_eval_not, __smtx_model_eval_xor,
      __smtx_model_eval_eq, native_veq, __smtx_model_eval_ite,
      native_not, SmtEval.native_not, native_and, SmtEval.native_and]

theorem bv_sdiv_sign_value_binary_bool
    (w p n : native_Int) :
    ∃ b, bvSdivSignValue n (SmtValue.Binary w p) = SmtValue.Boolean b := by
  simp [bvSdivSignValue, __smtx_model_eval_extract,
    __smtx_model_eval_eq, native_veq]

private theorem bv_sdiv_rhs_value_eq_bvsdiv
    (w px py : native_Int) :
    bvSdivRhsValue (w - 1)
        (SmtValue.Binary w px) (SmtValue.Binary w py) =
      __smtx_model_eval_bvsdiv
        (SmtValue.Binary w px) (SmtValue.Binary w py) := by
  rcases bv_sdiv_sign_value_binary_bool w px (w - 1) with ⟨bx, hx⟩
  rcases bv_sdiv_sign_value_binary_bool w py (w - 1) with ⟨bY, hy⟩
  rw [show bvSdivRhsValue (w - 1)
      (SmtValue.Binary w px) (SmtValue.Binary w py) =
      (let sx := SmtValue.Boolean bx
       let sy := SmtValue.Boolean bY
       let q := __smtx_model_eval_bvudiv
         (__smtx_model_eval_ite sx
           (__smtx_model_eval_bvneg (SmtValue.Binary w px))
           (SmtValue.Binary w px))
         (__smtx_model_eval_ite sy
           (__smtx_model_eval_bvneg (SmtValue.Binary w py))
           (SmtValue.Binary w py))
       __smtx_model_eval_ite (__smtx_model_eval_xor sx sy)
         (__smtx_model_eval_bvneg q) q) by
           simp [bvSdivRhsValue, bvSdivAbsValue, hx, hy]]
  rw [bv_sdiv_compact_value]
  rw [show __smtx_model_eval_bvsdiv
      (SmtValue.Binary w px) (SmtValue.Binary w py) =
      bvSdivExpandedValue
        (bvSdivSignValue (w + -1) (SmtValue.Binary w px))
        (bvSdivSignValue (w + -1) (SmtValue.Binary w py))
        (SmtValue.Binary w px) (SmtValue.Binary w py) from rfl]
  have hIdx : w + -1 = w - 1 :=
    (Int.sub_eq_add_neg (a := w) (b := 1)).symm
  rw [hIdx, hx, hy]

private theorem smtx_eval_xor_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.xor x y) =
      __smtx_model_eval_xor
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_bvneg_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvneg x) =
      __smtx_model_eval_bvneg (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvudiv_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvudiv x y) =
      __smtx_model_eval_bvudiv
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvsdiv_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsdiv x y) =
      __smtx_model_eval_bvsdiv
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem eval_bv_sdiv_sign
    (M : SmtModel) (z : Term) (n : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSdivSign (Term.Numeral n) z)) =
      bvSdivSignValue n (__smtx_model_eval M (__eo_to_smt z)) := by
  unfold bvSdivSign bvSdivExtract bvSdivSignValue
  change __smtx_model_eval M
      (SmtTerm.eq
        (SmtTerm.extract (SmtTerm.Numeral n) (SmtTerm.Numeral n)
          (__eo_to_smt z))
        (__eo_to_smt bvSdivBitOne)) = _
  rw [smtx_eval_eq_term_eq, smtx_eval_extract_term_eq]
  have hOne := eval_bv_const M 1 1 (by decide)
  have hOne' :
      __smtx_model_eval M (__eo_to_smt bvSdivBitOne) =
        SmtValue.Binary 1 1 := by
    have hsimpa := hOne
    try simp [bvSdivBitOne] at hsimpa ⊢
    exact hsimpa
  rw [hOne']
  rfl

theorem eval_bv_sdiv_abs
    (M : SmtModel) (z : Term) (n : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSdivAbs (Term.Numeral n) z)) =
      bvSdivAbsValue n (__smtx_model_eval M (__eo_to_smt z)) := by
  unfold bvSdivAbs bvSdivAbsValue
  change __smtx_model_eval M
      (SmtTerm.ite
        (__eo_to_smt (bvSdivSign (Term.Numeral n) z))
        (SmtTerm.bvneg (__eo_to_smt z)) (__eo_to_smt z)) = _
  rw [smtx_eval_ite_term_eq, eval_bv_sdiv_sign,
    smtx_eval_bvneg_term_eq]

private theorem eval_bv_sdiv_quot
    (M : SmtModel) (x y : Term) (n : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSdivQuot x y (Term.Numeral n))) =
      __smtx_model_eval_bvudiv
        (bvSdivAbsValue n (__smtx_model_eval M (__eo_to_smt x)))
        (bvSdivAbsValue n (__smtx_model_eval M (__eo_to_smt y))) := by
  unfold bvSdivQuot
  change __smtx_model_eval M
      (SmtTerm.bvudiv
        (__eo_to_smt (bvSdivAbs (Term.Numeral n) x))
        (__eo_to_smt (bvSdivAbs (Term.Numeral n) y))) = _
  rw [smtx_eval_bvudiv_term_eq, eval_bv_sdiv_abs, eval_bv_sdiv_abs]

private theorem eval_bv_sdiv_rhs
    (M : SmtModel) (x y : Term) (n : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSdivRhs x y (Term.Numeral n))) =
      bvSdivRhsValue n
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  unfold bvSdivRhs bvSdivRhsValue
  change __smtx_model_eval M
      (SmtTerm.ite
        (SmtTerm.xor
          (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
          (__eo_to_smt (bvSdivSign (Term.Numeral n) y)))
        (SmtTerm.bvneg
          (__eo_to_smt (bvSdivQuot x y (Term.Numeral n))))
        (__eo_to_smt (bvSdivQuot x y (Term.Numeral n)))) = _
  rw [smtx_eval_ite_term_eq, smtx_eval_xor_term_eq,
    eval_bv_sdiv_sign, eval_bv_sdiv_sign, smtx_eval_bvneg_term_eq,
    eval_bv_sdiv_quot]

private theorem smtx_eval_neg_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.neg x y) =
      __smtx_model_eval__
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_sdiv_bvsize
    (M : SmtModel) (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  intro hw0 hXSmtTy
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__eo_to_smt_bv_size (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  have hRound := native_int_to_nat_roundtrip w hw0
  have hNN :
      native_zleq 0 (native_nat_to_int (native_int_to_nat w)) = true := by
    simp [native_zleq, SmtEval.native_zleq, native_nat_to_int]
  rw [hXSmtTy]
  simp [__eo_to_smt_bv_size, native_ite, hw0, hNN, hRound,
    __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem bool_of_true_eval
    {M : SmtModel} {t : Term} {b : Bool} :
    eo_interprets M t true ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
    b = true := by
  intro hTrue hEval
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue
  cases hTrue with
  | intro_true _ hEvalTrue =>
      rw [hEval] at hEvalTrue
      cases b <;> simp at hEvalTrue ⊢

theorem bv_sdiv_index_eq_of_premise
    (M : SmtModel) (x : Term) (w n : native_Int) :
    eo_interprets M (bvSdivPrem x (Term.Numeral n)) true ->
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    n = w - 1 := by
  intro hPrem hw0 hXSmtTy
  have hSize := eval_bv_sdiv_bvsize M x w hw0 hXSmtTy
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSdivPrem x (Term.Numeral n))) =
        SmtValue.Boolean (native_zeq n (w - 1)) := by
    unfold bvSdivPrem
    change __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.Numeral n)
          (SmtTerm.neg
            (__eo_to_smt
              (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (SmtTerm.Numeral 1))) = _
    rw [smtx_eval_eq_term_eq, smtx_eval_neg_term_eq, hSize]
    simp [__smtx_model_eval, __smtx_model_eval__,
      __smtx_model_eval_eq, native_veq, SmtEval.native_zplus,
      SmtEval.native_zneg, SmtEval.native_zeq, Int.sub_eq_add_neg]
  have hEq := bool_of_true_eval hPrem hEval
  simpa [SmtEval.native_zeq] using hEq

private theorem facts_bv_sdiv_term
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSdivTerm x y nm) = Term.Bool ->
    eo_interprets M (bvSdivTerm x y nm) true := by
  intro hXTrans hYTrans hPrem hResultTy
  rcases bv_sdiv_context x y nm hXTrans hYTrans hResultTy with
    ⟨w, n, _hXTy, _hYTy, rfl, hw0, _hn0, _hnW, hXSmtTy, hYSmtTy⟩
  have hIndex : n = w - 1 :=
    bv_sdiv_index_eq_of_premise M x w n hPrem hw0 hXSmtTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
        (by
          simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
            using hXTrans)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.BitVec (native_int_to_nat w) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y)
        (by
          simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type]
            using hYTrans)
  rcases bitvec_value_canonical hXEvalTy with ⟨px, hXEval⟩
  rcases bitvec_value_canonical hYEvalTy with ⟨py, hYEval⟩
  have hRound := native_int_to_nat_roundtrip w hw0
  rw [hRound] at hXEval hYEval
  have hBool := typed_bv_sdiv_term x y (Term.Numeral n)
    hXTrans hYTrans hResultTy
  unfold bvSdivTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSdivTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.bvsdiv (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M
        (__eo_to_smt (bvSdivRhs x y (Term.Numeral n))))
    rw [smtx_eval_bvsdiv_term_eq, eval_bv_sdiv_rhs, hXEval, hYEval, hIndex,
      bv_sdiv_rhs_value_eq_bvsdiv]
    exact RuleProofs.smt_value_rel_refl _

def bvSdivProgram (x y nm : Term) : Term :=
  __eo_prog_bv_sdiv_eliminate x y nm (Proof.pf (bvSdivPrem x nm))

theorem bv_sdiv_program_eq_term_of_ne_stuck (x y nm : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvSdivProgram x y nm = bvSdivTerm x y nm := by
  intro hXNe hYNe hNmNe
  unfold bvSdivProgram bvSdivPrem
  rw [__eo_prog_bv_sdiv_eliminate.eq_4 x y nm nm x hXNe hYNe hNmNe]
  simp [bvSdivTerm, bvSdivLhs, bvSdivRhs, bvSdivQuot, bvSdivAbs, bvSdivSign,
    bvSdivExtract, bvSdivBitOne, __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hXNe, hNmNe]

theorem bv_sdiv_eliminate_shape_of_ne_stuck
    (x y nm P : Term) :
    __eo_prog_bv_sdiv_eliminate x y nm (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ nm ≠ Term.Stuck ∧
      ∃ pnm px, P = bvSdivPrem px pnm := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_sdiv_eliminate.eq_1 y nm (Proof.pf P))
  have hYNe : y ≠ Term.Stuck := by
    intro hY
    subst y
    exact hProg
      (__eo_prog_bv_sdiv_eliminate.eq_2 x nm (Proof.pf P) hXNe)
  have hNmNe : nm ≠ Term.Stuck := by
    intro hNm
    subst nm
    exact hProg
      (__eo_prog_bv_sdiv_eliminate.eq_3 x y (Proof.pf P) hXNe hYNe)
  refine ⟨hXNe, hYNe, hNmNe, ?_⟩
  by_cases hShape : ∃ pnm px, P = bvSdivPrem px pnm
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_sdiv_eliminate.eq_5 x y nm (Proof.pf P)
        hXNe hYNe hNmNe (by
          intro pnm px hP
          cases hP
          exact hShape ⟨pnm, px, rfl⟩)))

theorem typed_bv_sdiv_program (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSdivProgram x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSdivProgram x y nm) := by
  intro hXTrans hYTrans hNmTrans hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hEq := bv_sdiv_program_eq_term_of_ne_stuck x y nm hXNe hYNe hNmNe
  have hTermTy : __eo_typeof (bvSdivTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_sdiv_term x y nm hXTrans hYTrans hTermTy

theorem facts_bv_sdiv_program
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSdivProgram x y nm) = Term.Bool ->
    eo_interprets M (bvSdivProgram x y nm) true := by
  intro hXTrans hYTrans hNmTrans hPrem hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hEq := bv_sdiv_program_eq_term_of_ne_stuck x y nm hXNe hYNe hNmNe
  have hTermTy : __eo_typeof (bvSdivTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_sdiv_term M hM x y nm hXTrans hYTrans hPrem hTermTy
