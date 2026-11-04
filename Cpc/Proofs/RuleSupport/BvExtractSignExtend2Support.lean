module

public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport

public section

/-! Support for the straddling `bv_extract_sign_extend_2` rewrite. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem extractLsb'_signExtend_straddle
    {x : BitVec W} {K L D : Nat}
    (hLow : L < W) (hFit : L + D ≤ K + W)
    (hCross : W ≤ L + D) :
    (x.signExtend (K + W)).extractLsb' L D =
      (x.extractLsb' L (W - L)).signExtend D := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi]
  have hExt : L + i < K + W := by omega
  rw [BitVec.getLsbD_eq_getElem hExt, BitVec.getElem_signExtend hExt,
    BitVec.getElem_signExtend hi]
  by_cases hOrig : L + i < W
  · have hInner : i < W - L := by omega
    simp [hOrig, hInner, BitVec.getElem_extractLsb']
  · have hInner : ¬ i < W - L := by omega
    have hLen : 0 < W - L := by omega
    have hEnd : L + (W - L) ≤ W := by omega
    have hEndEq : L + (W - L) = W := by omega
    simp [hOrig, hInner, BitVec.msb_extractLsb', hLen, hEnd, hEndEq,
      BitVec.msb]

private theorem extract_sign_extend_straddle_val
    (W K L D S : Nat) (p h l nm sn : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hl : l = ↑L) (hd : h + 1 + -l = ↑D)
    (hnm : nm = ↑(W - 1))
    (hInnerWidth : nm + 1 + -l = ↑(W - L))
    (hsn : sn = ↑S) (hWidth : S + (W - L) = D)
    (hLow : L < W) (hFit : L + D ≤ K + W)
    (hCross : W ≤ L + D) :
    __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (__smtx_model_eval_sign_extend (SmtValue.Numeral (↑K : Int))
          (SmtValue.Binary (↑W : Int) p)) =
      __smtx_model_eval_sign_extend (SmtValue.Numeral sn)
        (__smtx_model_eval_extract (SmtValue.Numeral nm)
          (SmtValue.Numeral l) (SmtValue.Binary (↑W : Int) p)) := by
  let x := BitVec.ofInt W p
  let sx := x.signExtend (K + W)
  let inner := x.extractLsb' L (W - L)
  have hsx0 : (0 : Int) ≤ (↑sx.toNat : Int) := Int.natCast_nonneg _
  have hsx1 : (↑sx.toNat : Int) < (2 : Int) ^ (K + W) := by
    exact_mod_cast sx.isLt
  have hInner0 : (0 : Int) ≤ (↑inner.toNat : Int) :=
    Int.natCast_nonneg _
  have hInner1 : (↑inner.toNat : Int) < (2 : Int) ^ (W - L) := by
    exact_mod_cast inner.isLt
  rw [sign_extend_val_bitvec W K p hp0 hp1]
  rw [extract_val_bitvec_start_len (K + W) L D (↑sx.toNat : Int)
    h l hsx0 hsx1 hl hd]
  rw [extract_val_bitvec_start_len W L (W - L) p nm l
    hp0 hp1 hl hInnerWidth]
  rw [show sn = (↑S : Int) from hsn]
  rw [sign_extend_val_bitvec (W - L) S (↑inner.toNat : Int)
    hInner0 hInner1]
  have hsxOf : BitVec.ofInt (K + W) (↑sx.toNat : Int) = sx :=
    bitvec_ofInt_natCast_toNat sx
  have hInnerOf :
      BitVec.ofInt (W - L) (↑inner.toNat : Int) = inner :=
    bitvec_ofInt_natCast_toNat inner
  rw [hsxOf, hInnerOf]
  rw [hWidth]
  exact congrArg (fun z => SmtValue.Binary (↑D : Int) (↑z.toNat : Int))
    (extractLsb'_signExtend_straddle hLow hFit hCross)

def bvExtractSignExtend2Lhs (x low high k : Term) : Term :=
  bvExtractTerm (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) high low

def bvExtractSignExtend2Rhs (x low nm sn : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend sn)
    (bvExtractTerm x nm low)

def bvExtractSignExtend2Term
    (x low high k nm sn : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractSignExtend2Lhs x low high k))
    (bvExtractSignExtend2Rhs x low nm sn)

private theorem eo_typeof_sign_extend_arg_bitvec_of_ne_stuck
    {A idx C : Term}
    (h : __eo_typeof_zero_extend A idx C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_zero_extend at h
  split at h <;> simp at h ⊢

private theorem sign_extend_amount_context
    (x k widthTerm : Term) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) widthTerm ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) ≠
      Term.Stuck ->
    ∃ a : native_Int,
      k = Term.Numeral a ∧ native_zleq 0 a = true := by
  intro hXTy hSignNe
  change __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof x) ≠
      Term.Stuck at hSignNe
  rw [hXTy] at hSignNe
  have hParts :
      __eo_typeof k = Term.UOp UserOp.Int ∧
      __eo_requires (__eo_gt k (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec)
            (__eo_add widthTerm k)) ≠ Term.Stuck := by
    unfold __eo_typeof_zero_extend at hSignNe
    split at hSignNe <;> simp_all
  have hGuard :
      __eo_gt k (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hParts.2
  rcases sign_numeral_nonneg_of_gt_neg_one k hGuard with ⟨a, hK, ha0⟩
  exact ⟨a, hK, ha0⟩

private theorem bv_extract_sign_extend_2_context
    (x low high k nm sn : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend2Term x low high k nm sn) = Term.Bool ->
    ∃ w h l a n s : native_Int,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      high = Term.Numeral h ∧ low = Term.Numeral l ∧
      k = Term.Numeral a ∧ nm = Term.Numeral n ∧
      sn = Term.Numeral s ∧
      native_zleq 0 w = true ∧ native_zleq 0 l = true ∧
      native_zlt n w = true ∧
      native_zlt 0
        (native_zplus (native_zplus n 1) (native_zneg l)) = true ∧
      native_zleq 0 a = true ∧ native_zleq 0 s = true ∧
      native_zleq 0 (native_zplus a w) = true ∧
      native_zlt h (native_zplus a w) = true ∧
      native_zlt 0
        (native_zplus (native_zplus h 1) (native_zneg l)) = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvExtractSignExtend2Lhs x low high k))
      (__eo_typeof (bvExtractSignExtend2Rhs x low nm sn)) = Term.Bool
    at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hRhsNe' :
      __eo_typeof_zero_extend (__eo_typeof sn) sn
          (__eo_typeof (bvExtractTerm x nm low)) ≠ Term.Stuck := by
    have hsimpa := hRhsNe
    try simp [bvExtractSignExtend2Rhs] at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_sign_extend_arg_bitvec_of_ne_stuck hRhsNe' with
    ⟨innerWidthTerm, hInnerEoTy⟩
  have hInnerNe : __eo_typeof (bvExtractTerm x nm low) ≠ Term.Stuck := by
    intro hInner
    rw [hInner] at hInnerEoTy
    cases hInnerEoTy
  rcases bv_extract_context_of_non_stuck x nm low hXTrans hInnerNe with
    ⟨w, n, l, hXTy, hNm, hLow, hw0, hl0, hnw, hdInner0,
      hXSmtTy⟩
  rcases sign_extend_amount_context (bvExtractTerm x nm low) sn
      innerWidthTerm hInnerEoTy hRhsNe with ⟨s, hSn, hs0⟩
  have hLhsNe' :
      __eo_typeof_extract (__eo_typeof high) high
          (__eo_typeof low) low
          (__eo_typeof
            (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x)) ≠
        Term.Stuck := by
    have hsimpa := hLhsNe
    try simp [bvExtractSignExtend2Lhs, bvExtractTerm] at hsimpa ⊢
    exact hsimpa
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hLhsNe' with
    ⟨signWidthTerm, hSignEoTy⟩
  have hSignNe :
      __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) ≠
        Term.Stuck := by
    rw [hSignEoTy]
    intro hBad
    cases hBad
  rcases sign_extend_amount_context x k (Term.Numeral w) hXTy hSignNe with
    ⟨a, hK, ha0⟩
  let wa := native_zplus a w
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)) =
        SmtType.BitVec (native_int_to_nat wa) := by
    simpa [wa] using smt_typeof_sign_extend_of_context
      x w a hXSmtTy hw0 ha0
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
    ⟨wLhs, h, lLhs, _hSignEoTy', hHigh, hLowLhs, hwLhs0,
      hlLhs0, hhwLhs, hdLhs0, hSignSmtTyLhs⟩
  have hlEq : lLhs = l := by
    rw [hLow] at hLowLhs
    injection hLowLhs with hEq
    exact hEq.symm
  subst lLhs
  have hWidthNat : native_int_to_nat wa = native_int_to_nat wLhs := by
    rw [hK, hSignSmtTy] at hSignSmtTyLhs
    simpa using hSignSmtTyLhs
  have hwInt : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  have haInt : (0 : Int) ≤ a := by
    simpa [SmtEval.native_zleq] using ha0
  have hwa0 : native_zleq 0 wa = true := by
    have hwaInt : (0 : Int) ≤ a + w := Int.add_nonneg haInt hwInt
    simpa [wa, SmtEval.native_zleq, SmtEval.native_zplus] using hwaInt
  have hwLhsEq : wLhs = wa :=
    nonneg_int_eq_of_toNat_eq wLhs wa hwLhs0 hwa0 hWidthNat.symm
  rw [hwLhsEq] at hhwLhs
  exact ⟨w, h, l, a, n, s, hXTy, hHigh, hLow, hK, hNm, hSn,
    hw0, hl0, hnw, hdInner0, ha0, hs0, hwa0, hhwLhs, hdLhs0,
    hXSmtTy⟩

private theorem typed_bv_extract_sign_extend_2_term
    (x low high k nm sn : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend2Term x low high k nm sn) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractSignExtend2Term x low high k nm sn) := by
  intro hXTrans hResultTy
  rcases bv_extract_sign_extend_2_context x low high k nm sn
      hXTrans hResultTy with
    ⟨w, h, l, a, n, s, _hXTy, rfl, rfl, rfl, rfl, rfl,
      hw0, hl0, hnw, hdInner0, ha0, hs0, hwa0, hhwa, hdLhs0,
      hXSmtTy⟩
  let wa := native_zplus a w
  let dInner := native_zplus (native_zplus n 1) (native_zneg l)
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
            (bvExtractSignExtend2Lhs x (Term.Numeral l)
              (Term.Numeral h) (Term.Numeral a))) =
        SmtType.BitVec (native_int_to_nat dLhs) := by
    exact smt_typeof_extract_of_context
      (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)
      wa h l hSignTy hwa0 hl0 hhwa hdLhs0
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral n) (Term.Numeral l))) =
        SmtType.BitVec (native_int_to_nat dInner) := by
    exact smt_typeof_extract_of_context x w n l
      hXSmtTy hw0 hl0 hnw hdInner0
  have hdInnerNonneg : native_zleq 0 dInner = true :=
    native_zleq_of_zlt_true _ _ hdInner0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractSignExtend2Rhs x (Term.Numeral l)
              (Term.Numeral n) (Term.Numeral s))) =
        SmtType.BitVec
          (native_int_to_nat (native_zplus s dInner)) := by
    exact smt_typeof_sign_extend_of_context
      (bvExtractTerm x (Term.Numeral n) (Term.Numeral l))
      dInner s hInnerTy hdInnerNonneg hs0
  let lhs := bvExtractSignExtend2Lhs x (Term.Numeral l)
    (Term.Numeral h) (Term.Numeral a)
  let rhs := bvExtractSignExtend2Rhs x (Term.Numeral l)
    (Term.Numeral n) (Term.Numeral s)
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
        SmtType.BitVec (native_int_to_nat (native_zplus s dInner)) by
      simpa [rhs] using hRhsTy]
    intro hBad
    cases hBad
  have hEOTypeEq : __eo_typeof lhs = __eo_typeof rhs := by
    apply RuleProofs.eo_typeof_eq_bool_operands_eq
    have hsimpa := hResultTy
    try simp [bvExtractSignExtend2Term, lhs, rhs] at hsimpa ⊢
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
  unfold bvExtractSignExtend2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
    (by rw [hLhsBridge, hRhsBridge, hEOTypeEq])
    (by rw [hLhsTy']; simp)

def bvExtractBvsizeTerm (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_bvsize) x

def bvExtractSignExtend2PremLow (x low : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) low)
        (bvExtractBvsizeTerm x)))
    (Term.Boolean true)

def bvExtractSignExtend2PremHigh (x high : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) high)
        (bvExtractBvsizeTerm x)))
    (Term.Boolean true)

def bvExtractSignExtend2PremNm (x nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvExtractBvsizeTerm x)) (Term.Numeral 1))

def bvExtractSignExtend2PremSn (x high sn : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) sn)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) high)
          (bvExtractBvsizeTerm x))) (Term.Numeral 0)))

private theorem eval_bv_extract_bvsize
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
  simp [native_ite, hw0, __smtx_model_eval, __smtx_model_eval__at_purify]

private theorem model_eval_eq_true_of_eo_eq_true
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

private theorem eval_lt_bvsize
    (M : SmtModel) (x : Term) (l w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral l))
            (bvExtractBvsizeTerm x))) =
      SmtValue.Boolean (native_zlt l w) := by
  change __smtx_model_eval M
      (SmtTerm.lt (SmtTerm.Numeral l)
        (__eo_to_smt (bvExtractBvsizeTerm x))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bv_extract_bvsize M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval_lt]

private theorem eval_geq_bvsize
    (M : SmtModel) (x : Term) (h w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral h))
            (bvExtractBvsizeTerm x))) =
      SmtValue.Boolean (native_zleq w h) := by
  change __smtx_model_eval M
      (SmtTerm.geq (SmtTerm.Numeral h)
        (__eo_to_smt (bvExtractBvsizeTerm x))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bv_extract_bvsize M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval_geq,
    __smtx_model_eval_leq]

private theorem eval_bvsize_minus_one
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
  rw [eval_bv_extract_bvsize M x w hw0 hXSmtTy]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem eval_sign_extension_count
    (M : SmtModel) (x : Term) (h w : native_Int)
    (hw0 : native_zleq 0 w = true)
    (hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w)) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
                (Term.Numeral h)) (bvExtractBvsizeTerm x)))
              (Term.Numeral 0)))) =
      SmtValue.Numeral
        (native_zplus 1 (native_zplus
          (native_zplus h (native_zneg w)) 0)) := by
  change __smtx_model_eval M
      (SmtTerm.plus (SmtTerm.Numeral 1)
        (SmtTerm.plus
          (SmtTerm.neg (SmtTerm.Numeral h)
            (__eo_to_smt (bvExtractBvsizeTerm x)))
          (SmtTerm.Numeral 0))) = _
  have hSub :
      __smtx_model_eval M
          (SmtTerm.neg (SmtTerm.Numeral h)
            (__eo_to_smt (bvExtractBvsizeTerm x))) =
        SmtValue.Numeral (native_zplus h (native_zneg w)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [eval_bv_extract_bvsize M x w hw0 hXSmtTy]
    simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]
  have hInner :
      __smtx_model_eval M
          (SmtTerm.plus
            (SmtTerm.neg (SmtTerm.Numeral h)
              (__eo_to_smt (bvExtractBvsizeTerm x)))
            (SmtTerm.Numeral 0)) =
        SmtValue.Numeral
          (native_zplus (native_zplus h (native_zneg w)) 0) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hSub]
    simp [__smtx_model_eval, __smtx_model_eval_plus]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInner]
  simp [__smtx_model_eval, __smtx_model_eval_plus,
    __smtx_model_eval__, native_zplus, native_zneg]

private theorem bv_extract_sign_extend_2_premises_numeric
    (M : SmtModel) (x : Term) (w l h n s : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    eo_interprets M
      (bvExtractSignExtend2PremLow x (Term.Numeral l)) true ->
    eo_interprets M
      (bvExtractSignExtend2PremHigh x (Term.Numeral h)) true ->
    eo_interprets M
      (bvExtractSignExtend2PremNm x (Term.Numeral n)) true ->
    eo_interprets M
      (bvExtractSignExtend2PremSn x (Term.Numeral h)
        (Term.Numeral s)) true ->
    native_zlt l w = true ∧ native_zleq w h = true ∧
      n = native_zplus w (native_zneg 1) ∧
      s = native_zplus 1
        (native_zplus (native_zplus h (native_zneg w)) 0) := by
  intro hw0 hXSmtTy hLowPrem hHighPrem hNmPrem hSnPrem
  have hLowEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral l))
      (bvExtractBvsizeTerm x)) (Term.Boolean true)
    (by simpa [bvExtractSignExtend2PremLow] using hLowPrem)
  have hHighEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) (Term.Numeral h))
      (bvExtractBvsizeTerm x)) (Term.Boolean true)
    (by simpa [bvExtractSignExtend2PremHigh] using hHighPrem)
  have hNmEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral n)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvExtractBvsizeTerm x)) (Term.Numeral 1))
    (by simpa [bvExtractSignExtend2PremNm] using hNmPrem)
  have hSnEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Numeral s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) (Term.Numeral h))
          (bvExtractBvsizeTerm x))) (Term.Numeral 0)))
    (by simpa [bvExtractSignExtend2PremSn] using hSnPrem)
  rw [eval_lt_bvsize M x l w hw0 hXSmtTy] at hLowEq
  rw [eval_geq_bvsize M x h w hw0 hXSmtTy] at hHighEq
  rw [eval_bvsize_minus_one M x w hw0 hXSmtTy] at hNmEq
  rw [eval_sign_extension_count M x h w hw0 hXSmtTy] at hSnEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral n))
      (SmtValue.Numeral (native_zplus w (native_zneg 1))) =
    SmtValue.Boolean true at hNmEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral s))
      (SmtValue.Numeral
        (native_zplus 1
          (native_zplus (native_zplus h (native_zneg w)) 0))) =
    SmtValue.Boolean true at hSnEq
  rw [__smtx_model_eval.eq_def] at hNmEq hSnEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hLowEq hHighEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hLowEq hHighEq hNmEq hSnEq
  exact ⟨hLowEq, hHighEq, hNmEq, hSnEq⟩

private theorem eval_bv_extract_sign_extend_2
    (M : SmtModel) (hM : model_wf M)
    (x low high k nm sn : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend2Term x low high k nm sn) = Term.Bool ->
    eo_interprets M (bvExtractSignExtend2PremLow x low) true ->
    eo_interprets M (bvExtractSignExtend2PremHigh x high) true ->
    eo_interprets M (bvExtractSignExtend2PremNm x nm) true ->
    eo_interprets M (bvExtractSignExtend2PremSn x high sn) true ->
    __smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend2Lhs x low high k)) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend2Rhs x low nm sn)) := by
  intro hXTrans hResultTy hLowPrem hHighPrem hNmPrem hSnPrem
  rcases bv_extract_sign_extend_2_context x low high k nm sn
      hXTrans hResultTy with
    ⟨w, h, l, a, n, s, _hXTy, rfl, rfl, rfl, rfl, rfl,
      hw0, hl0, hnw, hdInner0, ha0, hs0, hwa0, hhwa, hdLhs0,
      hXSmtTy⟩
  rcases bv_extract_sign_extend_2_premises_numeric M x w l h n s
      hw0 hXSmtTy hLowPrem hHighPrem hNmPrem hSnPrem with
    ⟨hlw, hwh, hn, hs⟩
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  let W := native_int_to_nat w
  let K := native_int_to_nat a
  let L := native_int_to_nat l
  let D := native_int_to_nat d
  let S := native_int_to_nat s
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hKRound : (↑K : Int) = a := by
    simpa [K, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip a ha0
  have hLRound : (↑L : Int) = l := by
    simpa [L, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip l hl0
  have hdLhsNonneg : native_zleq 0 d = true :=
    native_zleq_of_zlt_true _ _ hdLhs0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip d hdLhsNonneg
  have hSRound : (↑S : Int) = s := by
    simpa [S, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip s hs0
  have hlwInt : l < w := by
    simpa [SmtEval.native_zlt] using hlw
  have hwhInt : w ≤ h := by
    simpa [SmtEval.native_zleq] using hwh
  have hhwaInt : h < a + w := by
    have hsimpa := hhwa
    try simp [SmtEval.native_zlt, SmtEval.native_zplus] at hsimpa ⊢
    exact of_decide_eq_true hsimpa
  have hLowInt : (↑L : Int) < (↑W : Int) := by
    rw [hLRound, hWRound]
    exact hlwInt
  have hLow : L < W := by exact_mod_cast hLowInt
  have hWPos : 0 < W := Nat.zero_lt_of_lt hLow
  have hOneW : 1 ≤ W := hWPos
  have hLLe : L ≤ W := Nat.le_of_lt hLow
  have hWSubOneCast :
      (↑(W - 1) : Int) = (↑W : Int) - 1 := by
    simpa using (Int.ofNat_sub hOneW)
  have hWSubLCast :
      (↑(W - L) : Int) = (↑W : Int) - (↑L : Int) := by
    simpa using (Int.ofNat_sub hLLe)
  have hNmCast : n = (↑(W - 1) : Int) := by
    calc
      n = w + -1 := by
        simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hn
      _ = (↑W : Int) - 1 := by
        rw [hWRound, Int.sub_eq_add_neg]
      _ = (↑(W - 1) : Int) := hWSubOneCast.symm
  have hInnerWidthCast : n + 1 + -l = (↑(W - L) : Int) := by
    calc
      n + 1 + -l = (↑(W - 1) : Int) + 1 + -(↑L : Int) := by
        rw [hNmCast, hLRound]
      _ = ((↑W : Int) - 1) + 1 + -(↑L : Int) := by
        rw [hWSubOneCast]
      _ = (↑W : Int) - (↑L : Int) := by omega
      _ = (↑(W - L) : Int) := hWSubLCast.symm
  have hFitEq : l + d = h + 1 := by
    simp [d, SmtEval.native_zplus, SmtEval.native_zneg, Int.add_assoc,
      Int.add_comm, Int.add_left_comm]
    omega
  have hFitZ : l + d ≤ a + w := by
    rw [hFitEq]
    exact Int.add_one_le_iff.mpr hhwaInt
  have hFitInt : (↑L : Int) + (↑D : Int) ≤
      (↑K : Int) + (↑W : Int) := by
    rw [hLRound, hDRound, hKRound, hWRound]
    exact hFitZ
  have hFit : L + D ≤ K + W := by exact_mod_cast hFitInt
  have hCrossZ : w ≤ l + d := by
    rw [hFitEq]
    have hh1 : h ≤ h + 1 :=
      Int.le_add_of_nonneg_right (by decide : (0 : Int) ≤ 1)
    exact Int.le_trans hwhInt hh1
  have hCrossInt : (↑W : Int) ≤ (↑L : Int) + (↑D : Int) := by
    rw [hWRound, hLRound, hDRound]
    exact hCrossZ
  have hCross : W ≤ L + D := by exact_mod_cast hCrossInt
  have hWidthZ : s + (w - l) = d := by
    rw [hs]
    simp [d, SmtEval.native_zplus, SmtEval.native_zneg,
      Int.add_assoc, Int.add_comm, Int.add_left_comm]
    omega
  have hWidthInt : (↑S : Int) + (↑(W - L) : Int) = (↑D : Int) := by
    rw [hSRound, hDRound]
    have hSubCast : (↑(W - L) : Int) = w - l := by
      rw [← hWRound, ← hLRound]
      omega
    rw [hSubCast]
    exact hWidthZ
  have hWidth : S + (W - L) = D := by exact_mod_cast hWidthInt
  have hdCast : h + 1 + -l = (↑D : Int) := by
    rw [hDRound]
    rfl
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) W
      (by simpa [W] using hXSmtTy) with ⟨p, hXEval, hCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑W : Int) p := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hXEval
  have hWidth0 : native_zleq 0 (native_nat_to_int W) = true := by
    simp [SmtEval.native_zleq, native_nat_to_int, SmtEval.native_nat_to_int]
  have hRange := bitvec_payload_range_of_canonical hWidth0 hCan
  have hp0 : (0 : Int) ≤ p := hRange.1
  have hp1 : p < (2 : Int) ^ W := by
    simpa [natpow2_eq, native_nat_to_int, SmtEval.native_nat_to_int] using
      hRange.2
  unfold bvExtractSignExtend2Lhs bvExtractSignExtend2Rhs
  rw [eval_extract_term, eval_sign_extend_term, eval_sign_extend_term,
    eval_extract_term, hXEval']
  simpa [hKRound, hSRound] using
    extract_sign_extend_straddle_val W K L D S p h l n s
      hp0 hp1 hLRound.symm hdCast hNmCast hInnerWidthCast
      hSRound.symm hWidth hLow hFit hCross

private theorem facts_bv_extract_sign_extend_2_term
    (M : SmtModel) (hM : model_wf M)
    (x low high k nm sn : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend2Term x low high k nm sn) = Term.Bool ->
    eo_interprets M (bvExtractSignExtend2PremLow x low) true ->
    eo_interprets M (bvExtractSignExtend2PremHigh x high) true ->
    eo_interprets M (bvExtractSignExtend2PremNm x nm) true ->
    eo_interprets M (bvExtractSignExtend2PremSn x high sn) true ->
    eo_interprets M (bvExtractSignExtend2Term x low high k nm sn) true := by
  intro hXTrans hResultTy hLowPrem hHighPrem hNmPrem hSnPrem
  have hBool := typed_bv_extract_sign_extend_2_term
    x low high k nm sn hXTrans hResultTy
  unfold bvExtractSignExtend2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractSignExtend2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend2Lhs x low high k)))
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend2Rhs x low nm sn)))
    rw [eval_bv_extract_sign_extend_2 M hM x low high k nm sn
      hXTrans hResultTy hLowPrem hHighPrem hNmPrem hSnPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvExtractSignExtend2Program
    (x low high k nm sn P1 P2 P3 P4 : Term) : Term :=
  __eo_prog_bv_extract_sign_extend_2 x low high k nm sn
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3) (Proof.pf P4)

private theorem bv_extract_sign_extend_2_guard_refs
    {low x high nm sn lowRef xRef1 highRef1 xRef2 nmRef xRef3
      snRef highRef2 xRef4 body : Term} :
    __eo_requires
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and
                (__eo_and
                  (__eo_and
                    (__eo_and
                      (__eo_and (__eo_eq low lowRef) (__eo_eq x xRef1))
                      (__eo_eq high highRef1))
                    (__eo_eq x xRef2))
                  (__eo_eq nm nmRef))
                (__eo_eq x xRef3))
              (__eo_eq sn snRef))
            (__eo_eq high highRef2))
          (__eo_eq x xRef4))
        (Term.Boolean true) body ≠ Term.Stuck ->
    lowRef = low ∧ xRef1 = x ∧ highRef1 = high ∧ xRef2 = x ∧
      nmRef = nm ∧ xRef3 = x ∧ snRef = sn ∧
      highRef2 = high ∧ xRef4 = x := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  rcases bv_extract_support_and_true hGuard with ⟨hG8, hX4⟩
  rcases bv_extract_support_and_true hG8 with ⟨hG7, hHigh2⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hSn⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hX3⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hNm⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hX2⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hHigh1⟩
  rcases bv_extract_support_and_true hG2 with ⟨hLow, hX1⟩
  exact ⟨(bv_extract_support_eq_true hLow).symm,
    (bv_extract_support_eq_true hX1).symm,
    (bv_extract_support_eq_true hHigh1).symm,
    (bv_extract_support_eq_true hX2).symm,
    (bv_extract_support_eq_true hNm).symm,
    (bv_extract_support_eq_true hX3).symm,
    (bv_extract_support_eq_true hSn).symm,
    (bv_extract_support_eq_true hHigh2).symm,
    (bv_extract_support_eq_true hX4).symm⟩

private theorem bv_extract_sign_extend_2_premise_shape
    (x low high k nm sn P1 P2 P3 P4 : Term) :
    x ≠ Term.Stuck -> low ≠ Term.Stuck -> high ≠ Term.Stuck ->
    k ≠ Term.Stuck -> nm ≠ Term.Stuck -> sn ≠ Term.Stuck ->
    bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4 ≠
      Term.Stuck ->
    ∃ lowRef xRef1 highRef1 xRef2 nmRef xRef3 snRef highRef2 xRef4,
      P1 = bvExtractSignExtend2PremLow xRef1 lowRef ∧
      P2 = bvExtractSignExtend2PremHigh xRef2 highRef1 ∧
      P3 = bvExtractSignExtend2PremNm xRef3 nmRef ∧
      P4 = bvExtractSignExtend2PremSn xRef4 highRef2 snRef := by
  intro hX hLow hHigh hK hNm hSn hProg
  by_cases hShape :
      ∃ lowRef xRef1 highRef1 xRef2 nmRef xRef3 snRef highRef2 xRef4,
        P1 = bvExtractSignExtend2PremLow xRef1 lowRef ∧
        P2 = bvExtractSignExtend2PremHigh xRef2 highRef1 ∧
        P3 = bvExtractSignExtend2PremNm xRef3 nmRef ∧
        P4 = bvExtractSignExtend2PremSn xRef4 highRef2 snRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_sign_extend_2.eq_8
      x low high k nm sn (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      (Proof.pf P4) hX hLow hHigh hK hNm hSn (by
        intro lowRef xRef1 highRef1 xRef2 nmRef xRef3 snRef highRef2
          xRef4 hP1 hP2 hP3 hP4
        cases hP1
        cases hP2
        cases hP3
        cases hP4
        exact hShape
          ⟨lowRef, xRef1, highRef1, xRef2, nmRef, xRef3, snRef,
            highRef2, xRef4, rfl, rfl, rfl, rfl⟩)

private theorem bv_extract_sign_extend_2_program_canonical
    (x low high k nm sn : Term) :
    x ≠ Term.Stuck -> low ≠ Term.Stuck -> high ≠ Term.Stuck ->
    k ≠ Term.Stuck -> nm ≠ Term.Stuck -> sn ≠ Term.Stuck ->
    bvExtractSignExtend2Program x low high k nm sn
        (bvExtractSignExtend2PremLow x low)
        (bvExtractSignExtend2PremHigh x high)
        (bvExtractSignExtend2PremNm x nm)
        (bvExtractSignExtend2PremSn x high sn) =
      bvExtractSignExtend2Term x low high k nm sn := by
  intro hX hLow hHigh hK hNm hSn
  unfold bvExtractSignExtend2Program bvExtractSignExtend2PremLow
    bvExtractSignExtend2PremHigh bvExtractSignExtend2PremNm
    bvExtractSignExtend2PremSn bvExtractBvsizeTerm
  rw [__eo_prog_bv_extract_sign_extend_2.eq_7
    x low high k nm sn low x high x nm x sn high x
    hX hLow hHigh hK hNm hSn]
  simp [bvExtractSignExtend2Term, bvExtractSignExtend2Lhs,
    bvExtractSignExtend2Rhs, bvExtractTerm, __eo_requires, __eo_and,
    __eo_eq, native_ite, native_teq, native_not, native_and,
    hX, hLow, hHigh, hK, hNm, hSn]

private theorem bvExtractSignExtend2Program_normalize
    (x low high k nm sn P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation sn ->
    bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4 ≠
      Term.Stuck ->
    P1 = bvExtractSignExtend2PremLow x low ∧
      P2 = bvExtractSignExtend2PremHigh x high ∧
      P3 = bvExtractSignExtend2PremNm x nm ∧
      P4 = bvExtractSignExtend2PremSn x high sn ∧
      bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4 =
        bvExtractSignExtend2Term x low high k nm sn := by
  intro hXTrans hLowTrans hHighTrans hKTrans hNmTrans hSnTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hLow := RuleProofs.term_ne_stuck_of_has_smt_translation low hLowTrans
  have hHigh := RuleProofs.term_ne_stuck_of_has_smt_translation high hHighTrans
  have hK := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hSn := RuleProofs.term_ne_stuck_of_has_smt_translation sn hSnTrans
  rcases bv_extract_sign_extend_2_premise_shape
      x low high k nm sn P1 P2 P3 P4 hX hLow hHigh hK hNm hSn hProg with
    ⟨lowRef, xRef1, highRef1, xRef2, nmRef, xRef3, snRef,
      highRef2, xRef4, hP1, hP2, hP3, hP4⟩
  have hReq := hProg
  rw [hP1, hP2, hP3, hP4] at hReq
  unfold bvExtractSignExtend2Program bvExtractSignExtend2PremLow
    bvExtractSignExtend2PremHigh bvExtractSignExtend2PremNm
    bvExtractSignExtend2PremSn bvExtractBvsizeTerm at hReq
  rw [__eo_prog_bv_extract_sign_extend_2.eq_7
    x low high k nm sn lowRef xRef1 highRef1 xRef2 nmRef xRef3
    snRef highRef2 xRef4 hX hLow hHigh hK hNm hSn] at hReq
  rcases bv_extract_sign_extend_2_guard_refs hReq with
    ⟨hLowRef, hXRef1, hHighRef1, hXRef2, hNmRef, hXRef3,
      hSnRef, hHighRef2, hXRef4⟩
  subst lowRef
  subst xRef1
  subst highRef1
  subst xRef2
  subst nmRef
  subst xRef3
  subst snRef
  subst highRef2
  subst xRef4
  have hP1Canon : P1 = bvExtractSignExtend2PremLow x low := hP1
  have hP2Canon : P2 = bvExtractSignExtend2PremHigh x high := hP2
  have hP3Canon : P3 = bvExtractSignExtend2PremNm x nm := hP3
  have hP4Canon : P4 = bvExtractSignExtend2PremSn x high sn := hP4
  refine ⟨hP1Canon, hP2Canon, hP3Canon, hP4Canon, ?_⟩
  rw [hP1Canon, hP2Canon, hP3Canon, hP4Canon]
  exact bv_extract_sign_extend_2_program_canonical
    x low high k nm sn hX hLow hHigh hK hNm hSn

theorem typed_bv_extract_sign_extend_2_program
    (x low high k nm sn P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation sn ->
    __eo_typeof
        (bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4) := by
  intro hXTrans hLowTrans hHighTrans hKTrans hNmTrans hSnTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractSignExtend2Program_normalize
      x low high k nm sn P1 P2 P3 P4 hXTrans hLowTrans hHighTrans
      hKTrans hNmTrans hSnTrans hProg with
    ⟨_hP1, _hP2, _hP3, _hP4, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvExtractSignExtend2Term x low high k nm sn) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_extract_sign_extend_2_term
    x low high k nm sn hXTrans hTermTy

theorem facts_bv_extract_sign_extend_2_program
    (M : SmtModel) (hM : model_wf M)
    (x low high k nm sn P1 P2 P3 P4 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation sn ->
    __eo_typeof
        (bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true -> eo_interprets M P4 true ->
    eo_interprets M
      (bvExtractSignExtend2Program x low high k nm sn P1 P2 P3 P4)
      true := by
  intro hXTrans hLowTrans hHighTrans hKTrans hNmTrans hSnTrans
    hResultTy hP1True hP2True hP3True hP4True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractSignExtend2Program_normalize
      x low high k nm sn P1 P2 P3 P4 hXTrans hLowTrans hHighTrans
      hKTrans hNmTrans hSnTrans hProg with
    ⟨hP1, hP2, hP3, hP4, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvExtractSignExtend2Term x low high k nm sn) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hPremLow : eo_interprets M (bvExtractSignExtend2PremLow x low) true := by
    simpa [hP1] using hP1True
  have hPremHigh :
      eo_interprets M (bvExtractSignExtend2PremHigh x high) true := by
    simpa [hP2] using hP2True
  have hPremNm : eo_interprets M (bvExtractSignExtend2PremNm x nm) true := by
    simpa [hP3] using hP3True
  have hPremSn :
      eo_interprets M (bvExtractSignExtend2PremSn x high sn) true := by
    simpa [hP4] using hP4True
  rw [hProgramEq]
  exact facts_bv_extract_sign_extend_2_term M hM x low high k nm sn
    hXTrans hTermTy hPremLow hPremHigh hPremNm hPremSn
