module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtend2Support
import all Cpc.Proofs.RuleSupport.BvExtractSignExtend2Support

public section

/-! Support for the above-source `bv_extract_sign_extend_3` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvExtractSignExtend3Lhs (x low high k : Term) : Term :=
  bvExtractTerm (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) high low

def bvExtractSignExtend3Rhs (x rn nm : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.repeat rn)
    (bvExtractTerm x nm nm)

def bvExtractSignExtend3Term
    (x low high k rn nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractSignExtend3Lhs x low high k))
    (bvExtractSignExtend3Rhs x rn nm)

private theorem eo_typeof_repeat_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_repeat A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_repeat at h
  split at h <;> simp at h ⊢

private theorem repeat_amount_context
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

private theorem bv_extract_sign_extend_3_context
    (x low high k rn nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend3Term x low high k rn nm) = Term.Bool ->
    ∃ w h l a r n : native_Int,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      high = Term.Numeral h ∧ low = Term.Numeral l ∧
      k = Term.Numeral a ∧ rn = Term.Numeral r ∧
      nm = Term.Numeral n ∧
      native_zleq 0 w = true ∧ native_zleq 0 n = true ∧
      native_zlt n w = true ∧
      native_zlt 0
        (native_zplus (native_zplus n 1) (native_zneg n)) = true ∧
      native_zleq 0 l = true ∧ native_zleq 0 a = true ∧
      native_zlt 0 r = true ∧
      native_zleq 0 (native_zplus a w) = true ∧
      native_zlt h (native_zplus a w) = true ∧
      native_zlt 0
        (native_zplus (native_zplus h 1) (native_zneg l)) = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvExtractSignExtend3Lhs x low high k))
      (__eo_typeof (bvExtractSignExtend3Rhs x rn nm)) = Term.Bool
    at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hRhsNe' :
      __eo_typeof_repeat (__eo_typeof rn) rn
          (__eo_typeof (bvExtractTerm x nm nm)) ≠ Term.Stuck := by
    have hsimpa := hRhsNe
    try simp [bvExtractSignExtend3Rhs] at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_repeat_arg_bitvec_of_ne_stuck hRhsNe' with
    ⟨innerWidthTerm, hInnerEoTy⟩
  have hInnerNe : __eo_typeof (bvExtractTerm x nm nm) ≠ Term.Stuck := by
    rw [hInnerEoTy]
    intro hBad
    cases hBad
  rcases bv_extract_context_of_non_stuck x nm nm hXTrans hInnerNe with
    ⟨w, nHigh, nLow, hXTy, hNmHigh, hNmLow, hw0, hnLow0,
      hnHighW, hdInner0, hXSmtTy⟩
  have hnEq : nHigh = nLow := by
    have hEq := hNmHigh.symm.trans hNmLow
    injection hEq
  subst nLow
  rcases repeat_amount_context (bvExtractTerm x nm nm) rn innerWidthTerm
      hInnerEoTy hRhsNe with ⟨r, hRn, hr0⟩
  have hLhsNe' :
      __eo_typeof_extract (__eo_typeof high) high
          (__eo_typeof low) low
          (__eo_typeof
            (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x)) ≠
        Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvExtractSignExtend3Lhs, bvExtractTerm] at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hLhsNe' with
    ⟨signWidthTerm, hSignEoTy⟩
  rcases sign_extend_index_context x k signWidthTerm w hXTy hSignEoTy with
    ⟨a, hK, ha0, hSignWidth⟩
  rw [hSignWidth] at hSignEoTy
  let wa := native_zplus a w
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)) =
        SmtType.BitVec (native_int_to_nat wa) := by
    simpa [wa] using
      smt_typeof_sign_extend_of_context x w a hXSmtTy hw0 ha0
  have hSignTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) := by
    rw [hK]
    unfold RuleProofs.eo_has_smt_translation
    rw [hSignSmtTy]
    intro hBad
    cases hBad
  rcases bv_extract_context_of_non_stuck
      (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x)
      high low hSignTrans hLhsNe with
    ⟨wLhs, h, l, _hSignTy', hHigh, hLow, hwLhs0, hl0,
      hHighW, hdLhs0, hSignSmtTyLhs⟩
  have hwa0 : native_zleq 0 wa = true := by
    have hwInt : (0 : Int) ≤ w := by
      simpa [SmtEval.native_zleq] using hw0
    have haInt : (0 : Int) ≤ a := by
      simpa [SmtEval.native_zleq] using ha0
    simpa [wa, SmtEval.native_zleq, SmtEval.native_zplus]
      using Int.add_nonneg haInt hwInt
  have hWidthNat : native_int_to_nat wa = native_int_to_nat wLhs := by
    rw [hK, hSignSmtTy] at hSignSmtTyLhs
    simpa using hSignSmtTyLhs
  have hwLhsEq : wLhs = wa :=
    nonneg_int_eq_of_toNat_eq wLhs wa hwLhs0 hwa0 hWidthNat.symm
  rw [hwLhsEq] at hHighW
  exact ⟨w, h, l, a, r, nHigh, hXTy, hHigh, hLow, hK, hRn,
    hNmHigh, hw0, hnLow0, hnHighW, hdInner0, hl0, ha0, hr0,
    hwa0, hHighW, hdLhs0, hXSmtTy⟩

private theorem typed_bv_extract_sign_extend_3_term
    (x low high k rn nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend3Term x low high k rn nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractSignExtend3Term x low high k rn nm) := by
  intro hXTrans hResultTy
  rcases bv_extract_sign_extend_3_context x low high k rn nm
      hXTrans hResultTy with
    ⟨w, h, l, a, r, n, _hXTy, rfl, rfl, rfl, rfl, rfl,
      hw0, hn0, hnw, hdInner0, hl0, ha0, hr0, hwa0, hhwa,
      hdLhs0, hXSmtTy⟩
  let wa := native_zplus a w
  let dLhs := native_zplus (native_zplus h 1) (native_zneg l)
  have hSignTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)) =
        SmtType.BitVec (native_int_to_nat wa) := by
    simpa [wa] using smt_typeof_sign_extend_of_context
      x w a hXSmtTy hw0 ha0
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractSignExtend3Lhs x (Term.Numeral l)
              (Term.Numeral h) (Term.Numeral a))) =
        SmtType.BitVec (native_int_to_nat dLhs) := by
    exact smt_typeof_extract_of_context
      (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)
      wa h l hSignTy hwa0 hl0 hhwa hdLhs0
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral n) (Term.Numeral n))) =
        SmtType.BitVec 1 := by
    have hRaw := smt_typeof_extract_of_context x w n n
      hXSmtTy hw0 hn0 hnw hdInner0
    have hD : native_int_to_nat
        (native_zplus (native_zplus n 1) (native_zneg n)) = 1 := by
      change Int.toNat (n + 1 + -n) = 1
      have hOne : n + 1 + -n = (1 : Int) := by
        calc
          n + 1 + -n = 1 + n + -n := by ac_rfl
          _ = 1 := Int.add_neg_cancel_right 1 n
      rw [hOne]
      exact Int.toNat_one
    rw [hD] at hRaw
    exact hRaw
  have hr1 : native_zleq 1 r = true := by
    have hrInt : (0 : Int) < r := by
      simpa [SmtEval.native_zlt] using hr0
    have hsimpa := hrInt
    try simp [SmtEval.native_zleq] at hsimpa ⊢
    exact hsimpa
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractSignExtend3Rhs x (Term.Numeral r)
              (Term.Numeral n))) =
        SmtType.BitVec (native_int_to_nat r) := by
    unfold bvExtractSignExtend3Rhs
    change __smtx_typeof
      (SmtTerm.repeat (SmtTerm.Numeral r)
        (__eo_to_smt
          (bvExtractTerm x (Term.Numeral n) (Term.Numeral n)))) = _
    rw [typeof_repeat_eq, hInnerTy]
    simp [__smtx_typeof_repeat, native_ite, hr1,
      SmtEval.native_zmult, native_nat_to_int, SmtEval.native_nat_to_int]
  let lhs := bvExtractSignExtend3Lhs x (Term.Numeral l)
    (Term.Numeral h) (Term.Numeral a)
  let rhs := bvExtractSignExtend3Rhs x (Term.Numeral r)
    (Term.Numeral n)
  have hLhsTrans : RuleProofs.eo_has_smt_translation lhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt lhs) =
        SmtType.BitVec (native_int_to_nat dLhs) by
      simpa [lhs] using hLhsTy]
    intro hBad
    cases hBad
  have hRhsTrans : RuleProofs.eo_has_smt_translation rhs := by
    unfold RuleProofs.eo_has_smt_translation
    rw [show __smtx_typeof (__eo_to_smt rhs) =
        SmtType.BitVec (native_int_to_nat r) by
      simpa [rhs] using hRhsTy]
    intro hBad
    cases hBad
  have hEOTypeEq : __eo_typeof lhs = __eo_typeof rhs := by
    apply RuleProofs.eo_typeof_eq_bool_operands_eq
    have hsimpa := hResultTy
    try simp [bvExtractSignExtend3Term, lhs, rhs] at hsimpa ⊢
    exact hsimpa
  have hLhsBridge :
      __smtx_typeof (__eo_to_smt lhs) =
        __eo_to_smt_type (__eo_typeof lhs) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      lhs (__eo_typeof lhs) (__eo_to_smt lhs) rfl hLhsTrans rfl
  have hRhsBridge :
      __smtx_typeof (__eo_to_smt rhs) =
        __eo_to_smt_type (__eo_typeof rhs) :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      rhs (__eo_typeof rhs) (__eo_to_smt rhs) rfl hRhsTrans rfl
  have hLhsTy' :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.BitVec (native_int_to_nat dLhs) := by
    simpa [lhs] using hLhsTy
  unfold bvExtractSignExtend3Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
    (by rw [hLhsTy']; simp)

def bvExtractSignExtend3PremLow (x low : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) low)
        (bvExtractBvsizeTerm x)))
    (Term.Boolean true)

def bvExtractSignExtend3PremRn (high low rn : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) rn)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) high) low))
        (Term.Numeral 0)))

def bvExtractSignExtend3PremNm (x nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvExtractBvsizeTerm x)) (Term.Numeral 1))

private theorem eval_bv_extract_bvsize_3
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M (__eo_to_smt (bvExtractBvsizeTerm x)) =
      SmtValue.Numeral w := by
  have hRound := native_int_to_nat_roundtrip w hw0
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

private theorem model_eval_eq_true_of_eo_eq_true_3
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem eval_geq_bvsize_3
    (M : SmtModel) (x : Term) (l w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral l))
            (bvExtractBvsizeTerm x))) =
      SmtValue.Boolean (native_zleq w l) := by
  change __smtx_model_eval M
      (SmtTerm.geq (SmtTerm.Numeral l)
        (__eo_to_smt (bvExtractBvsizeTerm x))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bv_extract_bvsize_3 M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval_geq,
    __smtx_model_eval_leq]

private theorem eval_bvsize_minus_one_3
    (M : SmtModel) (x : Term) (w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (bvExtractBvsizeTerm x)) (Term.Numeral 1))) =
      SmtValue.Numeral (native_zplus w (native_zneg 1)) := by
  change __smtx_model_eval M
      (SmtTerm.neg (__eo_to_smt (bvExtractBvsizeTerm x))
        (SmtTerm.Numeral 1)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bv_extract_bvsize_3 M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval__,
    native_zplus, native_zneg]

private theorem eval_extract_repeat_count_3
    (M : SmtModel) (h l : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
                (Term.Numeral h)) (Term.Numeral l)))
              (Term.Numeral 0)))) =
      SmtValue.Numeral
        (native_zplus 1
          (native_zplus (native_zplus h (native_zneg l)) 0)) := by
  change __smtx_model_eval M
      (SmtTerm.plus (SmtTerm.Numeral 1)
        (SmtTerm.plus
          (SmtTerm.neg (SmtTerm.Numeral h) (SmtTerm.Numeral l))
          (SmtTerm.Numeral 0))) = _
  have hSub :
      __smtx_model_eval M
          (SmtTerm.neg (SmtTerm.Numeral h) (SmtTerm.Numeral l)) =
        SmtValue.Numeral (native_zplus h (native_zneg l)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [__smtx_model_eval, __smtx_model_eval__,
      native_zplus, native_zneg]
  have hInner :
      __smtx_model_eval M
          (SmtTerm.plus
            (SmtTerm.neg (SmtTerm.Numeral h) (SmtTerm.Numeral l))
            (SmtTerm.Numeral 0)) =
        SmtValue.Numeral
          (native_zplus (native_zplus h (native_zneg l)) 0) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hSub]
    simp [__smtx_model_eval, __smtx_model_eval_plus]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInner]
  simp [__smtx_model_eval, __smtx_model_eval_plus,
    __smtx_model_eval__, native_zplus, native_zneg]

private theorem bv_extract_sign_extend_3_premises_numeric
    (M : SmtModel) (x : Term) (w l h r n : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    eo_interprets M
      (bvExtractSignExtend3PremLow x (Term.Numeral l)) true ->
    eo_interprets M
      (bvExtractSignExtend3PremRn (Term.Numeral h) (Term.Numeral l)
        (Term.Numeral r)) true ->
    eo_interprets M
      (bvExtractSignExtend3PremNm x (Term.Numeral n)) true ->
    native_zleq w l = true ∧
      r = native_zplus 1
        (native_zplus (native_zplus h (native_zneg l)) 0) ∧
      n = native_zplus w (native_zneg 1) := by
  intro hw0 hXSmtTy hLowPrem hRnPrem hNmPrem
  have hLowEq := model_eval_eq_true_of_eo_eq_true_3 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral l))
      (bvExtractBvsizeTerm x)) (Term.Boolean true)
    (by simpa [bvExtractSignExtend3PremLow] using hLowPrem)
  have hRnEq := model_eval_eq_true_of_eo_eq_true_3 M
    (Term.Numeral r)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral h))
          (Term.Numeral l))) (Term.Numeral 0)))
    (by simpa [bvExtractSignExtend3PremRn] using hRnPrem)
  have hNmEq := model_eval_eq_true_of_eo_eq_true_3 M
    (Term.Numeral n)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvExtractBvsizeTerm x)) (Term.Numeral 1))
    (by simpa [bvExtractSignExtend3PremNm] using hNmPrem)
  rw [eval_geq_bvsize_3 M x l w hw0 hXSmtTy] at hLowEq
  rw [eval_extract_repeat_count_3 M h l] at hRnEq
  rw [eval_bvsize_minus_one_3 M x w hw0 hXSmtTy] at hNmEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral r))
      (SmtValue.Numeral
        (native_zplus 1
          (native_zplus (native_zplus h (native_zneg l)) 0))) =
    SmtValue.Boolean true at hRnEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral n))
      (SmtValue.Numeral (native_zplus w (native_zneg 1))) =
    SmtValue.Boolean true at hNmEq
  rw [__smtx_model_eval.eq_def] at hRnEq hNmEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hLowEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hLowEq hRnEq hNmEq
  exact ⟨hLowEq, hRnEq, hNmEq⟩

private theorem extractLsb'_signExtend_above
    {x : BitVec W} {K L R : Nat}
    (hLow : W ≤ L) (hFit : L + R ≤ K + W) :
    (x.signExtend (K + W)).extractLsb' L R =
      BitVec.fill R x.msb := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi]
  have hExt : L + i < K + W := by omega
  have hOrig : ¬ L + i < W := by omega
  rw [BitVec.getLsbD_eq_getElem hExt, BitVec.getElem_signExtend hExt,
    BitVec.getElem_fill hi]
  simp [hOrig]

private theorem extractLsb'_sign_bit
    {x : BitVec W} (hWPos : 0 < W) :
    x.extractLsb' (W - 1) 1 = BitVec.fill 1 x.msb := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  rw [BitVec.getElem_extractLsb', BitVec.getElem_fill]
  simp only [Nat.add_zero]
  exact (BitVec.msb_eq_getLsbD_last x).symm

private theorem native_int_pow2_add_of_nonneg_3
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

private theorem native_int_pow2_nat_succ_3 (n : Nat) :
    native_int_pow2 (Int.ofNat (Nat.succ n)) =
      2 * native_int_pow2 (Int.ofNat n) := by
  have h1 : (0 : Int) ≤ 1 := by decide
  have hn : (0 : Int) ≤ Int.ofNat n := Int.natCast_nonneg n
  have hAdd := native_int_pow2_add_of_nonneg_3
    (a := Int.ofNat n) (b := 1) hn h1
  have hSucc : (Int.ofNat (Nat.succ n) : Int) = Int.ofNat n + 1 := by
    simp
  have hPow1 : native_int_pow2 (1 : Int) = 2 := by native_decide
  rw [hSucc, hAdd, hPow1, Int.mul_comm]

private theorem native_pow2_minus_one_mod_self_3 (w : native_Int) :
    native_zleq 0 w = true ->
    native_mod_total (native_int_pow2 w - 1) (native_int_pow2 w) =
      native_int_pow2 w - 1 := by
  intro hW0
  have hw : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hW0
  have hPowPos : 0 < native_int_pow2 w := by
    have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
    simp [native_int_pow2, native_zexp_total, hnot]
    exact Int.pow_pos (by decide)
  have hLo : 0 ≤ native_int_pow2 w - 1 :=
    Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr hPowPos)
  have hHi : native_int_pow2 w - 1 < native_int_pow2 w :=
    Int.sub_lt_self _ (by decide : (0 : Int) < 1)
  simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hLo hHi

private theorem eval_repeat_rec_zero_bit_3 :
    ∀ n : native_Nat,
      __smtx_repeat_rec n (SmtValue.Binary 1 0) =
        SmtValue.Binary (native_nat_to_int n) 0
  | Nat.zero => by
      simp [__smtx_repeat_rec, native_nat_to_int,
        SmtEval.native_nat_to_int]
  | Nat.succ n => by
      rw [__smtx_repeat_rec, eval_repeat_rec_zero_bit_3 n]
      have hWidth :
          native_zplus (1 : native_Int) (native_nat_to_int n) =
            native_nat_to_int (Nat.succ n) := by
        simp [SmtEval.native_zplus, native_nat_to_int,
          SmtEval.native_nat_to_int]
        rw [Int.add_comm]
      have hWidthInt : (1 : Int) + ↑n = ↑n + 1 := by
        rw [Int.add_comm]
      simp [__smtx_model_eval_concat, native_binary_concat,
        SmtEval.native_zplus, SmtEval.native_zmult,
        native_nat_to_int, SmtEval.native_nat_to_int,
        native_mod_total, hWidth, hWidthInt]

private theorem eval_repeat_rec_one_bit_3 :
    ∀ n : native_Nat,
      __smtx_repeat_rec n (SmtValue.Binary 1 1) =
        SmtValue.Binary (native_nat_to_int n)
          (native_int_pow2 (native_nat_to_int n) - 1)
  | Nat.zero => by
      simp [__smtx_repeat_rec, native_nat_to_int,
        SmtEval.native_nat_to_int, native_int_pow2, native_zexp_total]
  | Nat.succ n => by
      rw [__smtx_repeat_rec, eval_repeat_rec_one_bit_3 n]
      have hPowSucc :
          native_int_pow2 (native_nat_to_int (Nat.succ n)) =
            2 * native_int_pow2 (native_nat_to_int n) := by
        simpa [native_nat_to_int, SmtEval.native_nat_to_int] using
          native_int_pow2_nat_succ_3 n
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
      have hMod := native_pow2_minus_one_mod_self_3
        (native_nat_to_int (Nat.succ n)) hSucc0
      have hWidth :
          native_zplus (1 : native_Int) (native_nat_to_int n) =
            native_nat_to_int (Nat.succ n) := by
        simp [SmtEval.native_zplus, native_nat_to_int,
          SmtEval.native_nat_to_int]
        rw [Int.add_comm]
      have hWidthInt : (1 : Int) + ↑n = ↑n + 1 := by
        rw [Int.add_comm]
      have hPayload :
          native_mod_total
              (native_int_pow2 (native_nat_to_int n) +
                (native_int_pow2 (native_nat_to_int n) - 1))
              (native_int_pow2 (↑n + 1)) =
            native_int_pow2 (↑n + 1) - 1 := by
        rw [hRaw]
        simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hMod
      simpa [__smtx_model_eval_concat, native_binary_concat,
        SmtEval.native_zplus, SmtEval.native_zmult,
        native_nat_to_int, SmtEval.native_nat_to_int, hWidthInt]
        using hPayload

private theorem eval_repeat_term_3
    (M : SmtModel) (x rn : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat rn) x)) =
      __smtx_model_eval_repeat
        (__smtx_model_eval M (__eo_to_smt rn))
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.repeat (__eo_to_smt rn) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem extract_sign_extend_above_val
    (W K L R : Nat) (p h l n r : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hl : l = ↑L) (hd : h + 1 + -l = ↑R)
    (hn : n = ↑(W - 1)) (hr : r = ↑R)
    (hWPos : 0 < W) (hLow : W ≤ L) (hFit : L + R ≤ K + W) :
    __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (__smtx_model_eval_sign_extend (SmtValue.Numeral (↑K : Int))
          (SmtValue.Binary (↑W : Int) p)) =
      __smtx_model_eval_repeat (SmtValue.Numeral r)
        (__smtx_model_eval_extract (SmtValue.Numeral n)
          (SmtValue.Numeral n) (SmtValue.Binary (↑W : Int) p)) := by
  let x := BitVec.ofInt W p
  let sx := x.signExtend (K + W)
  let bit := x.extractLsb' (W - 1) 1
  have hsx0 : (0 : Int) ≤ (↑sx.toNat : Int) := Int.natCast_nonneg _
  have hsx1 : (↑sx.toNat : Int) < (2 : Int) ^ (K + W) := by
    exact_mod_cast sx.isLt
  have hbit0 : (0 : Int) ≤ (↑bit.toNat : Int) := Int.natCast_nonneg _
  have hbit1 : (↑bit.toNat : Int) < (2 : Int) ^ 1 := by
    exact_mod_cast bit.isLt
  rw [sign_extend_val_bitvec W K p hp0 hp1]
  rw [extract_val_bitvec_start_len (K + W) L R (↑sx.toNat : Int)
    h l hsx0 hsx1 hl hd]
  have hnWidth : n + 1 + -n = (1 : Int) := by
    rw [hn]
    omega
  rw [extract_val_bitvec_start_len W (W - 1) 1 p n n
    hp0 hp1 hn hnWidth]
  rw [hr]
  have hsxOf : BitVec.ofInt (K + W) (↑sx.toNat : Int) = sx :=
    bitvec_ofInt_natCast_toNat sx
  rw [hsxOf]
  change SmtValue.Binary (↑R : Int)
      (↑((sx.extractLsb' L R).toNat) : Int) =
    __smtx_model_eval_repeat (SmtValue.Numeral (↑R : Int))
      (SmtValue.Binary 1 (↑bit.toNat : Int))
  have hBitFill : bit = BitVec.fill 1 x.msb := by
    exact extractLsb'_sign_bit hWPos
  rw [extractLsb'_signExtend_above hLow hFit, hBitFill]
  have hRToNat : native_int_to_nat (↑R : Int) = R := by
    simp [native_int_to_nat, SmtEval.native_int_to_nat]
  have hPowOne : 1 ≤ (2 : Nat) ^ R := by
    exact Nat.one_le_pow R 2 (by decide)
  have hOnesCast : Int.ofNat ((2 : Nat) ^ R - 1) =
      (2 : Int) ^ R - 1 := by
    simpa using (Int.ofNat_sub hPowOne)
  cases hMsb : x.msb with
  | false =>
      simp [BitVec.fill_toNat, hMsb, __smtx_model_eval_repeat,
        eval_repeat_rec_zero_bit_3, hRToNat, native_nat_to_int,
        SmtEval.native_nat_to_int]
  | true =>
      simp only [BitVec.fill_toNat, hMsb, ↓reduceIte]
      simp [__smtx_model_eval_repeat,
        eval_repeat_rec_one_bit_3, hRToNat,
        native_nat_to_int, SmtEval.native_nat_to_int, natpow2_eq]
      exact hOnesCast

private theorem eval_bv_extract_sign_extend_3
    (M : SmtModel) (hM : model_wf M)
    (x low high k rn nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend3Term x low high k rn nm) = Term.Bool ->
    eo_interprets M (bvExtractSignExtend3PremLow x low) true ->
    eo_interprets M (bvExtractSignExtend3PremRn high low rn) true ->
    eo_interprets M (bvExtractSignExtend3PremNm x nm) true ->
    __smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend3Lhs x low high k)) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend3Rhs x rn nm)) := by
  intro hXTrans hResultTy hLowPrem hRnPrem hNmPrem
  rcases bv_extract_sign_extend_3_context x low high k rn nm
      hXTrans hResultTy with
    ⟨w, h, l, a, r, n, _hXTy, rfl, rfl, rfl, rfl, rfl,
      hw0, hn0, hnw, _hdInner0, hl0, ha0, hr0, _hwa0,
      hhwa, _hdLhs0, hXSmtTy⟩
  rcases bv_extract_sign_extend_3_premises_numeric M x w l h r n
      hw0 hXSmtTy hLowPrem hRnPrem hNmPrem with
    ⟨hwl, hr, hn⟩
  let W := native_int_to_nat w
  let K := native_int_to_nat a
  let L := native_int_to_nat l
  let R := native_int_to_nat r
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hKRound : (↑K : Int) = a := by
    simpa [K, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip a ha0
  have hLRound : (↑L : Int) = l := by
    simpa [L, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip l hl0
  have hrNonneg : native_zleq 0 r = true :=
    native_zleq_of_zlt_true _ _ hr0
  have hRRound : (↑R : Int) = r := by
    simpa [R, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip r hrNonneg
  have hnInt : (0 : Int) ≤ n := by
    simpa [SmtEval.native_zleq] using hn0
  have hnwInt : n < w := by
    simpa [SmtEval.native_zlt] using hnw
  have hwPosInt : (0 : Int) < w :=
    Int.lt_of_le_of_lt hnInt hnwInt
  have hWPosInt : (0 : Int) < (↑W : Int) := by
    rw [hWRound]
    exact hwPosInt
  have hWPos : 0 < W := by exact_mod_cast hWPosInt
  have hWSubOneCast : (↑(W - 1) : Int) = (↑W : Int) - 1 := by
    simpa using (Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hWPos)))
  have hNmCast : n = (↑(W - 1) : Int) := by
    calc
      n = w + -1 := by
        simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hn
      _ = (↑W : Int) - 1 := by
        rw [hWRound, Int.sub_eq_add_neg]
      _ = (↑(W - 1) : Int) := hWSubOneCast.symm
  have hwlInt : w ≤ l := by
    simpa [SmtEval.native_zleq] using hwl
  have hLowInt : (↑W : Int) ≤ (↑L : Int) := by
    rw [hWRound, hLRound]
    exact hwlInt
  have hLow : W ≤ L := by exact_mod_cast hLowInt
  have hrEq : r = h + 1 + -l := by
    rw [hr]
    simp [SmtEval.native_zplus, SmtEval.native_zneg,
      Int.add_assoc, Int.add_comm, Int.add_left_comm]
  have hdCast : h + 1 + -l = (↑R : Int) := by
    rw [hRRound, hrEq]
  have hhwaInt : h < a + w := by
    have hsimpa := hhwa
    try simp [SmtEval.native_zlt, SmtEval.native_zplus] at hsimpa ⊢
    exact of_decide_eq_true hsimpa
  have hFitZ : l + r ≤ a + w := by
    rw [hrEq]
    have hLhs : l + (h + 1 + -l) = h + 1 := by
      calc
        l + (h + 1 + -l) = h + 1 + l + -l := by ac_rfl
        _ = h + 1 := Int.add_neg_cancel_right (h + 1) l
    rw [hLhs]
    exact Int.add_one_le_iff.mpr hhwaInt
  have hFitInt : (↑L : Int) + (↑R : Int) ≤
      (↑K : Int) + (↑W : Int) := by
    rw [hLRound, hRRound, hKRound, hWRound]
    exact hFitZ
  have hFit : L + R ≤ K + W := by exact_mod_cast hFitInt
  rcases _root_.smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) p := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hXEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int,
      SmtEval.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hRange.2
  unfold bvExtractSignExtend3Lhs bvExtractSignExtend3Rhs
  rw [eval_extract_term, eval_sign_extend_term, eval_repeat_term_3,
    eval_extract_term, hXEval']
  change __smtx_model_eval_extract (SmtValue.Numeral h)
      (SmtValue.Numeral l)
      (__smtx_model_eval_sign_extend (SmtValue.Numeral a)
        (SmtValue.Binary (↑W : Int) p)) =
    __smtx_model_eval_repeat (SmtValue.Numeral r)
      (__smtx_model_eval_extract (SmtValue.Numeral n)
        (SmtValue.Numeral n) (SmtValue.Binary (↑W : Int) p))
  simpa [hKRound] using
    extract_sign_extend_above_val W K L R p h l n r hp0 hp1
      hLRound.symm hdCast hNmCast hRRound.symm hWPos hLow hFit

private theorem facts_bv_extract_sign_extend_3_term
    (M : SmtModel) (hM : model_wf M)
    (x low high k rn nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend3Term x low high k rn nm) = Term.Bool ->
    eo_interprets M (bvExtractSignExtend3PremLow x low) true ->
    eo_interprets M (bvExtractSignExtend3PremRn high low rn) true ->
    eo_interprets M (bvExtractSignExtend3PremNm x nm) true ->
    eo_interprets M (bvExtractSignExtend3Term x low high k rn nm) true := by
  intro hXTrans hResultTy hLowPrem hRnPrem hNmPrem
  have hBool := typed_bv_extract_sign_extend_3_term
    x low high k rn nm hXTrans hResultTy
  unfold bvExtractSignExtend3Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractSignExtend3Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend3Lhs x low high k)))
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend3Rhs x rn nm)))
    rw [eval_bv_extract_sign_extend_3 M hM x low high k rn nm
      hXTrans hResultTy hLowPrem hRnPrem hNmPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvExtractSignExtend3Program
    (x low high k rn nm P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_extract_sign_extend_3 x low high k rn nm
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private theorem bv_extract_sign_extend_3_guard_refs
    {low x rn high nm lowRef xRef1 rnRef highRef lowRef2 nmRef xRef2
      body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and (__eo_eq low lowRef) (__eo_eq x xRef1))
                  (__eo_eq rn rnRef))
                (__eo_eq high highRef))
              (__eo_eq low lowRef2))
            (__eo_eq nm nmRef))
          (__eo_eq x xRef2))
        (Term.Boolean true) body ≠ Term.Stuck ->
    lowRef = low ∧ xRef1 = x ∧ rnRef = rn ∧ highRef = high ∧
      lowRef2 = low ∧ nmRef = nm ∧ xRef2 = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG6, hX2⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hNm⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hLow2⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hHigh⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hRn⟩
  rcases bv_extract_support_and_true hG2 with ⟨hLow, hX1⟩
  exact ⟨(bv_extract_support_eq_true hLow).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hRn).symm,
    (bv_extract_support_eq_true hHigh).symm,
    (bv_extract_support_eq_true hLow2).symm,
    (bv_extract_support_eq_true hNm).symm,
    (bv_extract_support_eq_true hX2).symm⟩

private theorem bv_extract_sign_extend_3_premise_shape
    (x low high k rn nm P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> low ≠ Term.Stuck -> high ≠ Term.Stuck ->
    k ≠ Term.Stuck -> rn ≠ Term.Stuck -> nm ≠ Term.Stuck ->
    bvExtractSignExtend3Program x low high k rn nm P1 P2 P3 ≠
      Term.Stuck ->
    ∃ lowRef xRef1 rnRef highRef lowRef2 nmRef xRef2,
      P1 = bvExtractSignExtend3PremLow xRef1 lowRef ∧
      P2 = bvExtractSignExtend3PremRn highRef lowRef2 rnRef ∧
      P3 = bvExtractSignExtend3PremNm xRef2 nmRef := by
  intro hX hLow hHigh hK hRn hNm hProg
  by_cases hShape :
      ∃ lowRef xRef1 rnRef highRef lowRef2 nmRef xRef2,
        P1 = bvExtractSignExtend3PremLow xRef1 lowRef ∧
        P2 = bvExtractSignExtend3PremRn highRef lowRef2 rnRef ∧
        P3 = bvExtractSignExtend3PremNm xRef2 nmRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_sign_extend_3.eq_8
      x low high k rn nm (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hLow hHigh hK hRn hNm (by
        intro lowRef xRef1 rnRef highRef lowRef2 nmRef xRef2
          hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨lowRef, xRef1, rnRef, highRef, lowRef2, nmRef, xRef2,
            rfl, rfl, rfl⟩)

private theorem bv_extract_sign_extend_3_program_canonical
    (x low high k rn nm : Term) :
    x ≠ Term.Stuck -> low ≠ Term.Stuck -> high ≠ Term.Stuck ->
    k ≠ Term.Stuck -> rn ≠ Term.Stuck -> nm ≠ Term.Stuck ->
    bvExtractSignExtend3Program x low high k rn nm
        (bvExtractSignExtend3PremLow x low)
        (bvExtractSignExtend3PremRn high low rn)
        (bvExtractSignExtend3PremNm x nm) =
      bvExtractSignExtend3Term x low high k rn nm := by
  intro hX hLow hHigh hK hRn hNm
  unfold bvExtractSignExtend3Program bvExtractSignExtend3PremLow
    bvExtractSignExtend3PremRn bvExtractSignExtend3PremNm
    bvExtractBvsizeTerm
  rw [__eo_prog_bv_extract_sign_extend_3.eq_7
    x low high k rn nm low x rn high low nm x
    hX hLow hHigh hK hRn hNm]
  simp [bvExtractSignExtend3Term, bvExtractSignExtend3Lhs,
    bvExtractSignExtend3Rhs, bvExtractTerm, __eo_requires, __eo_and,
    __eo_eq, native_ite, native_teq, native_not, native_and,
    hX, hLow, hHigh, hK, hRn, hNm]

private theorem bvExtractSignExtend3Program_normalize
    (x low high k rn nm P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation rn ->
    RuleProofs.eo_has_smt_translation nm ->
    bvExtractSignExtend3Program x low high k rn nm P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvExtractSignExtend3PremLow x low ∧
      P2 = bvExtractSignExtend3PremRn high low rn ∧
      P3 = bvExtractSignExtend3PremNm x nm ∧
      bvExtractSignExtend3Program x low high k rn nm P1 P2 P3 =
        bvExtractSignExtend3Term x low high k rn nm := by
  intro hXTrans hLowTrans hHighTrans hKTrans hRnTrans hNmTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hLow := RuleProofs.term_ne_stuck_of_has_smt_translation low hLowTrans
  have hHigh := RuleProofs.term_ne_stuck_of_has_smt_translation high hHighTrans
  have hK := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hRn := RuleProofs.term_ne_stuck_of_has_smt_translation rn hRnTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_extract_sign_extend_3_premise_shape
      x low high k rn nm P1 P2 P3 hX hLow hHigh hK hRn hNm hProg with
    ⟨lowRef, xRef1, rnRef, highRef, lowRef2, nmRef, xRef2,
      hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvExtractSignExtend3Program bvExtractSignExtend3PremLow
    bvExtractSignExtend3PremRn bvExtractSignExtend3PremNm
    bvExtractBvsizeTerm at hReq
  rw [__eo_prog_bv_extract_sign_extend_3.eq_7
    x low high k rn nm lowRef xRef1 rnRef highRef lowRef2 nmRef xRef2
    hX hLow hHigh hK hRn hNm] at hReq
  rcases bv_extract_sign_extend_3_guard_refs hReq with
    ⟨hLowRef, hXRef1, hRnRef, hHighRef, hLowRef2, hNmRef, hXRef2⟩
  subst lowRef
  subst xRef1
  subst rnRef
  subst highRef
  subst lowRef2
  subst nmRef
  subst xRef2
  have hP1Canon : P1 = bvExtractSignExtend3PremLow x low := hP1
  have hP2Canon : P2 = bvExtractSignExtend3PremRn high low rn := hP2
  have hP3Canon : P3 = bvExtractSignExtend3PremNm x nm := hP3
  refine ⟨hP1Canon, hP2Canon, hP3Canon, ?_⟩
  rw [hP1Canon, hP2Canon, hP3Canon]
  exact bv_extract_sign_extend_3_program_canonical
    x low high k rn nm hX hLow hHigh hK hRn hNm

theorem typed_bv_extract_sign_extend_3_program
    (x low high k rn nm P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation rn ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof
        (bvExtractSignExtend3Program x low high k rn nm P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractSignExtend3Program x low high k rn nm P1 P2 P3) := by
  intro hXTrans hLowTrans hHighTrans hKTrans hRnTrans hNmTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractSignExtend3Program_normalize
      x low high k rn nm P1 P2 P3 hXTrans hLowTrans hHighTrans
      hKTrans hRnTrans hNmTrans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvExtractSignExtend3Term x low high k rn nm) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_extract_sign_extend_3_term
    x low high k rn nm hXTrans hTermTy

theorem facts_bv_extract_sign_extend_3_program
    (M : SmtModel) (hM : model_wf M)
    (x low high k rn nm P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation rn ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof
        (bvExtractSignExtend3Program x low high k rn nm P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvExtractSignExtend3Program x low high k rn nm P1 P2 P3)
      true := by
  intro hXTrans hLowTrans hHighTrans hKTrans hRnTrans hNmTrans
    hResultTy hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractSignExtend3Program_normalize
      x low high k rn nm P1 P2 P3 hXTrans hLowTrans hHighTrans
      hKTrans hRnTrans hNmTrans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvExtractSignExtend3Term x low high k rn nm) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hPremLow :
      eo_interprets M (bvExtractSignExtend3PremLow x low) true := by
    simpa [hP1] using hP1True
  have hPremRn :
      eo_interprets M (bvExtractSignExtend3PremRn high low rn) true := by
    simpa [hP2] using hP2True
  have hPremNm :
      eo_interprets M (bvExtractSignExtend3PremNm x nm) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_extract_sign_extend_3_term M hM x low high k rn nm
    hXTrans hTermTy hPremLow hPremRn hPremNm
