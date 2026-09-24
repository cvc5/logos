module

public import Cpc.Proofs.RuleSupport.BvSdivElimSupport
import all Cpc.Proofs.RuleSupport.BvSdivElimSupport

public section

/-! Support for the `bv_srem_eliminate` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvSremRem (x y nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) (bvSdivAbs nm x))
    (bvSdivAbs nm y)

def bvSremRhs (x y nm : Term) : Term :=
  let r := bvSremRem x y nm
  Term.Apply
    (Term.Apply (Term.Apply (Term.UOp UserOp.ite) (bvSdivSign nm x))
      (Term.Apply (Term.UOp UserOp.bvneg) r)) r

def bvSremLhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) x) y

def bvSremTerm (x y nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (bvSremLhs x y))
    (bvSremRhs x y nm)

private theorem bv_srem_context (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSremTerm x y nm) = Term.Bool ->
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
      (__eo_typeof (bvSremRhs x y nm)) = Term.Bool at hResultTy
  have hOps := RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases eo_typeof_bvbin_arg_types_of_ne_stuck hOps.1 with
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
  have hTypeEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRemReduce :
      __eo_typeof_bvand (__eo_typeof x) (__eo_typeof y) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
    rw [hXTy, hYTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRhsTy :
      __eo_typeof (bvSremRhs x y nm) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) := by
    rw [hRemReduce] at hTypeEq
    exact hTypeEq.symm
  have hWidthNe :
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ≠ Term.Stuck := by
    intro h
    cases h
  have hOuter := typeof_ite_inv_nonstuck
    (__eo_typeof (bvSdivSign nm x))
    (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg)
      (bvSremRem x y nm)))
    (__eo_typeof (bvSremRem x y nm))
    (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w))
    (by have hsimpa := hRhsTy; (try simp [bvSremRhs] at hsimpa ⊢); exact hsimpa) hWidthNe
  have hExtractNe : __eo_typeof (bvSdivExtract nm x) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _
      (by have hsimpa := hOuter.1; (try simp [bvSdivSign] at hsimpa ⊢); exact hsimpa)).1
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
    hXSmtTy, hYSmtTy⟩

private theorem typed_bv_srem_term (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof (bvSremTerm x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSremTerm x y nm) := by
  intro hXTrans hYTrans hResultTy
  rcases bv_srem_context x y nm hXTrans hYTrans hResultTy with
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
    have hsimpa := h
    try simp [bvSdivExtract, hOneIndex, native_int_to_nat, SmtEval.native_int_to_nat] at hsimpa ⊢
    exact hsimpa
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
  have hRemTy :
      __smtx_typeof (__eo_to_smt
        (bvSremRem x y (Term.Numeral n))) = SmtType.BitVec W := by
    apply smt_typeof_bvbin_same SmtTerm.bvurem
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hAbsXTy hAbsYTy
  have hNegRemTy := smt_typeof_bvneg_same
    (__eo_to_smt (bvSremRem x y (Term.Numeral n))) W hRemTy
  have hRhsTy :
      __smtx_typeof (__eo_to_smt
        (bvSremRhs x y (Term.Numeral n))) = SmtType.BitVec W := by
    change __smtx_typeof
      (SmtTerm.ite
        (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
        (SmtTerm.bvneg
          (__eo_to_smt (bvSremRem x y (Term.Numeral n))))
        (__eo_to_smt (bvSremRem x y (Term.Numeral n)))) = _
    rw [__smtx_typeof.eq_def] <;> simp only
    simp [__smtx_typeof_ite, hSignXTy, hNegRemTy, hRemTy,
      native_Teq, native_ite]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (bvSremLhs x y)) = SmtType.BitVec W := by
    apply smt_typeof_bvbin_same SmtTerm.bvsrem
      (fun a b => by rw [__smtx_typeof.eq_def] <;> simp only)
      _ _ W hXSmtTyW hYSmtTyW
  unfold bvSremTerm
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; intro h; cases h)

private noncomputable def bvSremRemValue
    (n : native_Int) (x y : SmtValue) : SmtValue :=
  __smtx_model_eval_bvurem (bvSdivAbsValue n x) (bvSdivAbsValue n y)

private noncomputable def bvSremRhsValue
    (n : native_Int) (x y : SmtValue) : SmtValue :=
  let r := bvSremRemValue n x y
  __smtx_model_eval_ite (bvSdivSignValue n x)
    (__smtx_model_eval_bvneg r) r

private noncomputable def bvSremExpandedValue
    (sx sy x y : SmtValue) : SmtValue :=
  __smtx_model_eval_ite
    (__smtx_model_eval_and (__smtx_model_eval_not sx)
      (__smtx_model_eval_not sy))
    (__smtx_model_eval_bvurem x y)
    (__smtx_model_eval_ite
      (__smtx_model_eval_and sx (__smtx_model_eval_not sy))
      (__smtx_model_eval_bvneg
        (__smtx_model_eval_bvurem (__smtx_model_eval_bvneg x) y))
      (__smtx_model_eval_ite
        (__smtx_model_eval_and (__smtx_model_eval_not sx) sy)
        (__smtx_model_eval_bvurem x (__smtx_model_eval_bvneg y))
        (__smtx_model_eval_bvneg
          (__smtx_model_eval_bvurem
            (__smtx_model_eval_bvneg x) (__smtx_model_eval_bvneg y)))))

private theorem bv_srem_compact_value
    (x y : SmtValue) (bx bY : Bool) :
    (let sx := SmtValue.Boolean bx
     let sy := SmtValue.Boolean bY
     let r := __smtx_model_eval_bvurem
       (__smtx_model_eval_ite sx (__smtx_model_eval_bvneg x) x)
       (__smtx_model_eval_ite sy (__smtx_model_eval_bvneg y) y)
     __smtx_model_eval_ite sx (__smtx_model_eval_bvneg r) r) =
      bvSremExpandedValue
        (SmtValue.Boolean bx) (SmtValue.Boolean bY) x y := by
  cases bx <;> cases bY <;>
    simp [bvSremExpandedValue, __smtx_model_eval_and,
      __smtx_model_eval_not, __smtx_model_eval_eq,
      native_veq, __smtx_model_eval_ite,
      native_not, SmtEval.native_not, native_and, SmtEval.native_and]

private theorem bv_srem_rhs_value_eq_bvsrem
    (w px py : native_Int) :
    bvSremRhsValue (w - 1)
        (SmtValue.Binary w px) (SmtValue.Binary w py) =
      __smtx_model_eval_bvsrem
        (SmtValue.Binary w px) (SmtValue.Binary w py) := by
  rcases bv_sdiv_sign_value_binary_bool w px (w - 1) with ⟨bx, hx⟩
  rcases bv_sdiv_sign_value_binary_bool w py (w - 1) with ⟨bY, hy⟩
  rw [show bvSremRhsValue (w - 1)
      (SmtValue.Binary w px) (SmtValue.Binary w py) =
      (let sx := SmtValue.Boolean bx
       let sy := SmtValue.Boolean bY
       let r := __smtx_model_eval_bvurem
         (__smtx_model_eval_ite sx
           (__smtx_model_eval_bvneg (SmtValue.Binary w px))
           (SmtValue.Binary w px))
         (__smtx_model_eval_ite sy
           (__smtx_model_eval_bvneg (SmtValue.Binary w py))
           (SmtValue.Binary w py))
       __smtx_model_eval_ite sx (__smtx_model_eval_bvneg r) r) by
         simp [bvSremRhsValue, bvSremRemValue, bvSdivAbsValue, hx, hy]]
  rw [bv_srem_compact_value]
  rw [show __smtx_model_eval_bvsrem
      (SmtValue.Binary w px) (SmtValue.Binary w py) =
      bvSremExpandedValue
        (bvSdivSignValue (w + -1) (SmtValue.Binary w px))
        (bvSdivSignValue (w + -1) (SmtValue.Binary w py))
        (SmtValue.Binary w px) (SmtValue.Binary w py) from rfl]
  have hIdx : w + -1 = w - 1 :=
    (Int.sub_eq_add_neg (a := w) (b := 1)).symm
  rw [hIdx, hx, hy]

private theorem smtx_eval_bvurem_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvurem x y) =
      __smtx_model_eval_bvurem
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem smtx_eval_bvsrem_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bvsrem x y) =
      __smtx_model_eval_bvsrem
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_srem_rem
    (M : SmtModel) (x y : Term) (n : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSremRem x y (Term.Numeral n))) =
      bvSremRemValue n
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  unfold bvSremRem bvSremRemValue
  change __smtx_model_eval M
      (SmtTerm.bvurem
        (__eo_to_smt (bvSdivAbs (Term.Numeral n) x))
        (__eo_to_smt (bvSdivAbs (Term.Numeral n) y))) = _
  rw [smtx_eval_bvurem_term_eq, eval_bv_sdiv_abs, eval_bv_sdiv_abs]

private theorem eval_bv_srem_rhs
    (M : SmtModel) (x y : Term) (n : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSremRhs x y (Term.Numeral n))) =
      bvSremRhsValue n
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  unfold bvSremRhs bvSremRhsValue
  change __smtx_model_eval M
      (SmtTerm.ite
        (__eo_to_smt (bvSdivSign (Term.Numeral n) x))
        (SmtTerm.bvneg
          (__eo_to_smt (bvSremRem x y (Term.Numeral n))))
        (__eo_to_smt (bvSremRem x y (Term.Numeral n)))) = _
  rw [smtx_eval_ite_term_eq, eval_bv_sdiv_sign,
    smtx_eval_bvneg_term_eq, eval_bv_srem_rem]

private theorem facts_bv_srem_term
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSremTerm x y nm) = Term.Bool ->
    eo_interprets M (bvSremTerm x y nm) true := by
  intro hXTrans hYTrans hPrem hResultTy
  rcases bv_srem_context x y nm hXTrans hYTrans hResultTy with
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
  have hBool := typed_bv_srem_term x y (Term.Numeral n)
    hXTrans hYTrans hResultTy
  unfold bvSremTerm
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvSremTerm] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (SmtTerm.bvsrem (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M
        (__eo_to_smt (bvSremRhs x y (Term.Numeral n))))
    rw [smtx_eval_bvsrem_term_eq, eval_bv_srem_rhs, hXEval, hYEval,
      hIndex, bv_srem_rhs_value_eq_bvsrem]
    exact RuleProofs.smt_value_rel_refl _

def bvSremProgram (x y nm : Term) : Term :=
  __eo_prog_bv_srem_eliminate x y nm (Proof.pf (bvSdivPrem x nm))

theorem bv_srem_program_eq_term_of_ne_stuck (x y nm : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvSremProgram x y nm = bvSremTerm x y nm := by
  intro hXNe hYNe hNmNe
  unfold bvSremProgram bvSdivPrem
  rw [__eo_prog_bv_srem_eliminate.eq_4 x y nm nm x hXNe hYNe hNmNe]
  simp [bvSremTerm, bvSremLhs, bvSremRhs, bvSremRem,
    bvSdivAbs, bvSdivSign, bvSdivExtract, bvSdivBitOne,
    __eo_requires, __eo_and, __eo_eq,
    native_ite, native_teq, native_not, SmtEval.native_not,
    native_and, SmtEval.native_and, hXNe, hNmNe]

theorem bv_srem_eliminate_shape_of_ne_stuck
    (x y nm P : Term) :
    __eo_prog_bv_srem_eliminate x y nm (Proof.pf P) ≠ Term.Stuck ->
    x ≠ Term.Stuck ∧ y ≠ Term.Stuck ∧ nm ≠ Term.Stuck ∧
      ∃ pnm px, P = bvSdivPrem px pnm := by
  intro hProg
  have hXNe : x ≠ Term.Stuck := by
    intro hX
    subst x
    exact hProg (__eo_prog_bv_srem_eliminate.eq_1 y nm (Proof.pf P))
  have hYNe : y ≠ Term.Stuck := by
    intro hY
    subst y
    exact hProg
      (__eo_prog_bv_srem_eliminate.eq_2 x nm (Proof.pf P) hXNe)
  have hNmNe : nm ≠ Term.Stuck := by
    intro hNm
    subst nm
    exact hProg
      (__eo_prog_bv_srem_eliminate.eq_3 x y (Proof.pf P) hXNe hYNe)
  refine ⟨hXNe, hYNe, hNmNe, ?_⟩
  by_cases hShape : ∃ pnm px, P = bvSdivPrem px pnm
  · exact hShape
  · exact False.elim (hProg
      (__eo_prog_bv_srem_eliminate.eq_5 x y nm (Proof.pf P)
        hXNe hYNe hNmNe (by
          intro pnm px hP
          cases hP
          exact hShape ⟨pnm, px, rfl⟩)))

theorem typed_bv_srem_program (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvSremProgram x y nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvSremProgram x y nm) := by
  intro hXTrans hYTrans hNmTrans hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hEq := bv_srem_program_eq_term_of_ne_stuck x y nm hXNe hYNe hNmNe
  have hTermTy : __eo_typeof (bvSremTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact typed_bv_srem_term x y nm hXTrans hYTrans hTermTy

theorem facts_bv_srem_program
    (M : SmtModel) (hM : model_wf M) (x y nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    RuleProofs.eo_has_smt_translation nm ->
    eo_interprets M (bvSdivPrem x nm) true ->
    __eo_typeof (bvSremProgram x y nm) = Term.Bool ->
    eo_interprets M (bvSremProgram x y nm) true := by
  intro hXTrans hYTrans hNmTrans hPrem hResultTy
  have hXNe := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hYNe := RuleProofs.term_ne_stuck_of_has_smt_translation y hYTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hEq := bv_srem_program_eq_term_of_ne_stuck x y nm hXNe hYNe hNmNe
  have hTermTy : __eo_typeof (bvSremTerm x y nm) = Term.Bool := by
    rw [← hEq]
    exact hResultTy
  rw [hEq]
  exact facts_bv_srem_term M hM x y nm hXTrans hYTrans hPrem hTermTy
