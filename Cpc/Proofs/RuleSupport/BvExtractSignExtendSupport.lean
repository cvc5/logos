module

public import Cpc.Proofs.RuleSupport.BvExtractRewriteSupport
import all Cpc.Proofs.RuleSupport.BvExtractRewriteSupport

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

theorem native_binary_uts_eq_bitvec_toInt
    (W : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    native_binary_uts (↑W : Int) p = (BitVec.ofInt W p).toInt := by
  cases W with
  | zero =>
      have hp : p = 0 := by simp at hp1; omega
      subst p
      native_decide
  | succ w =>
      let x := BitVec.ofInt (w + 1) p
      have hToNat : x.toNat = p.toNat := by
        exact ofInt_toNat_canonical (w + 1) p hp0 hp1
      have hpCast : (↑p.toNat : Int) = p := Int.toNat_of_nonneg hp0
      have hHalfPos : (0 : Int) < (2 : Int) ^ w := by
        exact_mod_cast Nat.two_pow_pos w
      have hPow : (2 : Int) ^ (w + 1) = 2 * (2 : Int) ^ w := by
        rw [Int.pow_succ]
        omega
      have hPred : (↑(w + 1) : Int) + -1 = ↑w := by omega
      cases hMsb : x.msb with
      | false =>
          have hLowNat : 2 * x.toNat < 2 ^ (w + 1) :=
            BitVec.msb_eq_false_iff_two_mul_lt.mp hMsb
          have hLow : p < (2 : Int) ^ w := by
            have hLowInt : 2 * p < (2 : Int) ^ (w + 1) := by
              rw [← hpCast, ← hToNat]
              exact_mod_cast hLowNat
            rw [hPow] at hLowInt
            omega
          have hMod : native_mod_total p (native_int_pow2 (↑w : Int)) = p := by
            rw [natpow2_eq]
            exact Int.emod_eq_of_lt hp0 hLow
          rw [BitVec.toInt_eq_msb_cond, hMsb]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hToNat, Int.toNat_of_nonneg hp0]
          unfold native_binary_uts
          simp only [native_zplus, native_zmult, native_zneg]
          rw [hPred, hMod]
          rw [Int.two_mul]
          exact Int.add_neg_cancel_right p p
      | true =>
          have hHighNat : 2 ^ (w + 1) ≤ 2 * x.toNat :=
            BitVec.msb_eq_true_iff_two_mul_ge.mp hMsb
          have hHigh : (2 : Int) ^ w ≤ p := by
            have hHighInt : (2 : Int) ^ (w + 1) ≤ 2 * p := by
              rw [← hpCast, ← hToNat]
              exact_mod_cast hHighNat
            rw [hPow] at hHighInt
            omega
          have hRem0 : (0 : Int) ≤ p - (2 : Int) ^ w := by omega
          have hRem1 : p - (2 : Int) ^ w < (2 : Int) ^ w := by
            rw [hPow] at hp1
            omega
          have hMod :
              native_mod_total p (native_int_pow2 (↑w : Int)) =
                p - (2 : Int) ^ w := by
            rw [natpow2_eq]
            change p % (2 : Int) ^ w = p - (2 : Int) ^ w
            rw [← Int.sub_emod_right p ((2 : Int) ^ w)]
            exact Int.emod_eq_of_lt hRem0 hRem1
          rw [BitVec.toInt_eq_msb_cond, hMsb]
          simp only [↓reduceIte]
          rw [hToNat, Int.toNat_of_nonneg hp0]
          rw [show (↑(2 ^ (w + 1) : Nat) : Int) = (2 : Int) ^ (w + 1) by
            norm_cast]
          unfold native_binary_uts
          simp only [native_zplus, native_zmult, native_zneg]
          rw [hPred, hMod, hPow]
          rw [Int.two_mul, Int.sub_eq_add_neg]
          have hCancel : p + -p = 0 := by
            simpa using (Int.add_neg_cancel_right (0 : Int) p)
          calc
            (p + -((2 : Int) ^ w)) + (p + -((2 : Int) ^ w)) + -p =
                (p + -p) + (p + (-((2 : Int) ^ w) + -((2 : Int) ^ w))) := by
              ac_rfl
            _ = p + (-((2 : Int) ^ w) + -((2 : Int) ^ w)) := by
              rw [hCancel, Int.zero_add]
            _ = p + -((2 : Int) ^ w + (2 : Int) ^ w) := by
              rw [Int.neg_add]
            _ = p - 2 * (2 : Int) ^ w := by
              rw [Int.sub_eq_add_neg, Int.two_mul]

theorem sign_extend_val_bitvec
    (W K : Nat) (p : Int) (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W) :
    __smtx_model_eval_sign_extend (SmtValue.Numeral (↑K : Int))
        (SmtValue.Binary (↑W : Int) p) =
      SmtValue.Binary (↑(K + W) : Int)
        (↑((BitVec.ofInt W p).signExtend (K + W)).toNat : Int) := by
  let x := BitVec.ofInt W p
  have hWidth : (↑K : Int) + ↑W = ↑(K + W) := by norm_cast
  have hUts : native_binary_uts (↑W : Int) p = x.toInt :=
    native_binary_uts_eq_bitvec_toInt W p hp0 hp1
  simp only [__smtx_model_eval_sign_extend, native_zplus, native_mod_total]
  rw [hWidth, hUts, natpow2_eq]
  congr 2
  rw [show x.signExtend (K + W) = BitVec.ofInt (K + W) x.toInt by rfl]
  rw [BitVec.toNat_ofInt]
  have hPowCast : (↑(2 ^ (K + W) : Nat) : Int) =
      (2 : Int) ^ (K + W) := by norm_cast
  rw [hPowCast]
  have hPowPos : (0 : Int) < (2 : Int) ^ (K + W) := by
    exact_mod_cast Nat.two_pow_pos (K + W)
  have hModNonneg : 0 ≤ x.toInt % (2 : Int) ^ (K + W) :=
    Int.emod_nonneg _ (Int.ne_of_gt hPowPos)
  exact (Int.toNat_of_nonneg hModNonneg).symm

private theorem extractLsb'_signExtend_of_le
    {x : BitVec W} {K start len : Nat} (hFit : start + len ≤ W) :
    (x.signExtend (K + W)).extractLsb' start len =
      x.extractLsb' start len := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_extractLsb' hi, BitVec.getElem_extractLsb' hi]
  have hOrig : start + i < W := by omega
  have hExt : start + i < K + W := by omega
  rw [BitVec.getLsbD_eq_getElem hExt, BitVec.getElem_signExtend hExt]
  simp [hOrig, BitVec.getLsbD_eq_getElem hOrig]

private theorem extract_sign_extend_low_val
    (W K L D : Nat) (p h l : Int)
    (hp0 : 0 ≤ p) (hp1 : p < (2 : Int) ^ W)
    (hl : l = ↑L) (hd : h + 1 + -l = ↑D)
    (hFit : L + D ≤ W) :
    __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (__smtx_model_eval_sign_extend (SmtValue.Numeral (↑K : Int))
          (SmtValue.Binary (↑W : Int) p)) =
      __smtx_model_eval_extract (SmtValue.Numeral h) (SmtValue.Numeral l)
        (SmtValue.Binary (↑W : Int) p) := by
  let x := BitVec.ofInt W p
  let sx := x.signExtend (K + W)
  have hsx0 : (0 : Int) ≤ (↑sx.toNat : Int) := Int.natCast_nonneg _
  have hsx1 : (↑sx.toNat : Int) < (2 : Int) ^ (K + W) := by
    exact_mod_cast sx.isLt
  rw [sign_extend_val_bitvec W K p hp0 hp1]
  rw [extract_val_bitvec_start_len (K + W) L D (↑sx.toNat : Int)
    h l hsx0 hsx1 hl hd]
  rw [extract_val_bitvec_start_len W L D p h l hp0 hp1 hl hd]
  congr 2
  have hsxOf : BitVec.ofInt (K + W) (↑sx.toNat : Int) = sx :=
    bitvec_ofInt_natCast_toNat sx
  rw [hsxOf]
  exact congrArg BitVec.toNat (extractLsb'_signExtend_of_le hFit)

def bvExtractSignExtend1Lhs (x low high k : Term) : Term :=
  bvExtractTerm (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) high low

def bvExtractSignExtend1Rhs (x low high : Term) : Term :=
  bvExtractTerm x high low

def bvExtractSignExtend1Term (x low high k : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvExtractSignExtend1Lhs x low high k))
    (bvExtractSignExtend1Rhs x low high)

theorem sign_numeral_nonneg_of_gt_neg_one
    (t : Term)
    (h : __eo_gt t (Term.Numeral (-1 : native_Int)) = Term.Boolean true) :
    ∃ n : native_Int, t = Term.Numeral n ∧ native_zleq 0 n = true := by
  cases t <;> simp [__eo_gt] at h
  case Numeral n =>
    have hn : (-1 : Int) < n := by simpa [SmtEval.native_zlt] using h
    have hn0 : (0 : Int) ≤ n := by omega
    exact ⟨n, rfl, by simpa [SmtEval.native_zleq] using hn0⟩

theorem sign_extend_index_context
    (x k widthTerm : Term) (w : native_Int) :
    __eo_typeof x =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    __eo_typeof (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x) =
      Term.Apply (Term.UOp UserOp.BitVec) widthTerm ->
    ∃ a : native_Int,
      k = Term.Numeral a ∧ native_zleq 0 a = true ∧
      widthTerm = Term.Numeral (native_zplus w a) := by
  intro hXTy hSignTy
  change __eo_typeof_zero_extend (__eo_typeof k) k (__eo_typeof x) =
      Term.Apply (Term.UOp UserOp.BitVec) widthTerm at hSignTy
  rw [hXTy] at hSignTy
  have hSignNe :
      __eo_typeof_zero_extend (__eo_typeof k) k
          (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) ≠
        Term.Stuck := by
    rw [hSignTy]
    intro h
    cases h
  have hParts :
      __eo_typeof k = Term.UOp UserOp.Int ∧
      __eo_requires (__eo_gt k (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true)
          (__eo_mk_apply (Term.UOp UserOp.BitVec)
            (__eo_add (Term.Numeral w) k)) ≠ Term.Stuck := by
    unfold __eo_typeof_zero_extend at hSignNe
    split at hSignNe <;> simp_all
  have hGuard :
      __eo_gt k (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hParts.2
  rcases sign_numeral_nonneg_of_gt_neg_one k hGuard with ⟨a, hK, ha0⟩
  subst k
  have hNumeralTy :
      __eo_typeof (Term.Numeral a) = Term.UOp UserOp.Int := rfl
  rw [hNumeralTy] at hSignTy
  have hLt : native_zlt (-1 : native_Int) a = true := by
    simpa [__eo_gt] using hGuard
  have hGuardNe :
      __eo_gt (Term.Numeral a) (Term.Numeral (-1 : native_Int)) ≠
        Term.Stuck := by simp [__eo_gt]
  have hWidthEq :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_zplus w a)) =
        Term.Apply (Term.UOp UserOp.BitVec) widthTerm := by
    simpa [hXTy, __eo_typeof_zero_extend, __eo_requires, __eo_gt,
      __eo_mk_apply, __eo_add, hLt, hGuard, hGuardNe, native_ite, native_teq,
      native_not] using hSignTy
  have hWidth : Term.Numeral (native_zplus w a) = widthTerm := by
    simpa using hWidthEq
  exact ⟨a, rfl, ha0, hWidth.symm⟩

private theorem bv_extract_sign_extend_1_context
    (x low high k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend1Term x low high k) = Term.Bool ->
    ∃ w h l a : native_Int,
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ∧
      high = Term.Numeral h ∧ low = Term.Numeral l ∧
      k = Term.Numeral a ∧
      native_zleq 0 w = true ∧ native_zleq 0 l = true ∧
      native_zlt h w = true ∧
      native_zlt 0
        (native_zplus (native_zplus h 1) (native_zneg l)) = true ∧
      native_zleq 0 a = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) := by
  intro hXTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvExtractSignExtend1Lhs x low high k))
      (__eo_typeof (bvExtractSignExtend1Rhs x low high)) = Term.Bool
    at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases bv_extract_context_of_non_stuck x high low hXTrans hRhsNe with
    ⟨w, h, l, hXTy, hHigh, hLow, hw0, hl0, hhw, hd0, hXSmtTy⟩
  have hLhsNe' :
      __eo_typeof_extract (__eo_typeof high) high
          (__eo_typeof low) low
          (__eo_typeof
            (Term.Apply (Term.UOp1 UserOp1.sign_extend k) x)) ≠
        Term.Stuck := by
    simpa [bvExtractSignExtend1Lhs, bvExtractTerm, __eo_typeof, __eo_typeof_extract] using hLhsNe
  rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hLhsNe' with
    ⟨widthTerm, hSignTy⟩
  rcases sign_extend_index_context x k widthTerm w hXTy hSignTy with
    ⟨a, hK, ha0, _hWidth⟩
  exact ⟨w, h, l, a, hXTy, hHigh, hLow, hK, hw0, hl0, hhw, hd0,
    ha0, hXSmtTy⟩

theorem smt_typeof_sign_extend_of_context
    (x : Term) (w a : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ->
    native_zleq 0 w = true ->
    native_zleq 0 a = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus a w)) := by
  intro hXTy hw0 ha0
  have hRound := native_int_to_nat_roundtrip w hw0
  change __smtx_typeof
      (SmtTerm.sign_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [typeof_sign_extend_eq, hXTy]
  simp [__smtx_typeof_sign_extend, native_ite, ha0, hRound]

private theorem typed_bv_extract_sign_extend_1_term
    (x low high k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend1Term x low high k) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractSignExtend1Term x low high k) := by
  intro hXTrans hResultTy
  rcases bv_extract_sign_extend_1_context x low high k hXTrans hResultTy with
    ⟨w, h, l, a, _hXTy, rfl, rfl, rfl, hw0, hl0, hhw, hd0, ha0,
      hXSmtTy⟩
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  let wa := native_zplus a w
  have hSignTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)) =
        SmtType.BitVec (native_int_to_nat wa) := by
    simpa [wa] using smt_typeof_sign_extend_of_context x w a hXSmtTy hw0 ha0
  have hwInt : (0 : Int) ≤ w := by
    simpa [SmtEval.native_zleq] using hw0
  have haInt : (0 : Int) ≤ a := by
    simpa [SmtEval.native_zleq] using ha0
  have hhwInt : h < w := by
    simpa [SmtEval.native_zlt] using hhw
  have hwa0 : native_zleq 0 wa = true := by
    have hSum : (0 : Int) ≤ a + w := Int.add_nonneg haInt hwInt
    simpa [wa, SmtEval.native_zleq, SmtEval.native_zplus] using hSum
  have hhwa : native_zlt h wa = true := by
    have hWLe : w ≤ a + w := Int.le_add_of_nonneg_left haInt
    have hlt : h < a + w := Int.lt_of_lt_of_le hhwInt hWLe
    simpa [wa, SmtEval.native_zlt, SmtEval.native_zplus] using hlt
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractSignExtend1Lhs x (Term.Numeral l)
              (Term.Numeral h) (Term.Numeral a))) =
        SmtType.BitVec (native_int_to_nat d) := by
    exact smt_typeof_extract_of_context
      (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)
      wa h l hSignTy hwa0 hl0 hhwa hd0
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (bvExtractSignExtend1Rhs x (Term.Numeral l)
              (Term.Numeral h))) =
        SmtType.BitVec (native_int_to_nat d) := by
    exact smt_typeof_extract_of_context x w h l
      hXSmtTy hw0 hl0 hhw hd0
  unfold bvExtractSignExtend1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hRhsTy.symm) (by rw [hLhsTy]; simp)

theorem eval_sign_extend_term
    (M : SmtModel) (x : Term) (a : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.sign_extend (Term.Numeral a)) x)) =
      __smtx_model_eval_sign_extend (SmtValue.Numeral a)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.sign_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval]

private theorem eval_bv_extract_sign_extend_1
    (M : SmtModel) (hM : model_wf M)
    (x low high k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend1Term x low high k) = Term.Bool ->
    __smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend1Lhs x low high k)) =
      __smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend1Rhs x low high)) := by
  intro hXTrans hResultTy
  rcases bv_extract_sign_extend_1_context x low high k hXTrans hResultTy with
    ⟨w, h, l, a, _hXTy, rfl, rfl, rfl, hw0, hl0, hhw, hd0, ha0,
      hXSmtTy⟩
  let d := native_zplus (native_zplus h 1) (native_zneg l)
  let W := native_int_to_nat w
  let K := native_int_to_nat a
  let L := native_int_to_nat l
  let D := native_int_to_nat d
  have hWRound : (↑W : Int) = w := by
    simpa [W, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip w hw0
  have hKRound : (↑K : Int) = a := by
    simpa [K, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip a ha0
  have hLRound : (↑L : Int) = l := by
    simpa [L, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip l hl0
  have hd0Nonneg : native_zleq 0 d = true :=
    native_zleq_of_zlt_true _ _ hd0
  have hDRound : (↑D : Int) = d := by
    simpa [D, native_nat_to_int, SmtEval.native_nat_to_int] using
      native_int_to_nat_roundtrip d hd0Nonneg
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
  have hhwInt : h < w := by
    simpa [SmtEval.native_zlt] using hhw
  have hFitEq : l + d = h + 1 := by
    simp [d, SmtEval.native_zplus, SmtEval.native_zneg, Int.add_assoc,
      Int.add_comm, Int.add_left_comm]
    omega
  have hFitZ : l + d ≤ w := by
    rw [hFitEq]
    exact Int.add_one_le_iff.mpr hhwInt
  have hFitInt : (↑L : Int) + (↑D : Int) ≤ (↑W : Int) := by
    rw [hLRound, hDRound, hWRound]
    exact hFitZ
  have hFit : L + D ≤ W := by
    exact_mod_cast hFitInt
  have hdCast : h + 1 + -l = (↑D : Int) := by
    rw [hDRound]
    rfl
  unfold bvExtractSignExtend1Lhs bvExtractSignExtend1Rhs
  rw [eval_extract_term, eval_sign_extend_term, eval_extract_term, hXEval']
  simpa [hKRound] using
    extract_sign_extend_low_val W K L D p h l hp0 hp1
      hLRound.symm hdCast hFit

private theorem facts_bv_extract_sign_extend_1_term
    (M : SmtModel) (hM : model_wf M)
    (x low high k : Term) :
    RuleProofs.eo_has_smt_translation x ->
    __eo_typeof (bvExtractSignExtend1Term x low high k) = Term.Bool ->
    eo_interprets M (bvExtractSignExtend1Term x low high k) true := by
  intro hXTrans hResultTy
  have hBool := typed_bv_extract_sign_extend_1_term
    x low high k hXTrans hResultTy
  unfold bvExtractSignExtend1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvExtractSignExtend1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend1Lhs x low high k)))
      (__smtx_model_eval M
        (__eo_to_smt (bvExtractSignExtend1Rhs x low high)))
    rw [eval_bv_extract_sign_extend_1 M hM x low high k
      hXTrans hResultTy]
    exact RuleProofs.smt_value_rel_refl _

def bvExtractSignExtend1Prem (x high : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) high)
        (Term.Apply (Term.UOp UserOp._at_bvsize) x)))
    (Term.Boolean true)

def bvExtractSignExtend1Program
    (x low high k P : Term) : Term :=
  __eo_prog_bv_extract_sign_extend_1 x low high k (Proof.pf P)

private theorem bv_extract_sign_extend_1_premise_shape
    (x low high k P : Term) :
    x ≠ Term.Stuck -> low ≠ Term.Stuck -> high ≠ Term.Stuck ->
    k ≠ Term.Stuck ->
    bvExtractSignExtend1Program x low high k P ≠ Term.Stuck ->
    ∃ highRef xRef,
      P = bvExtractSignExtend1Prem xRef highRef := by
  intro hX hLow hHigh hK hProg
  by_cases hShape :
      ∃ highRef xRef,
        P = bvExtractSignExtend1Prem xRef highRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_extract_sign_extend_1.eq_6
      x low high k (Proof.pf P) hX hLow hHigh hK (by
        intro highRef xRef hP
        cases hP
        exact hShape ⟨highRef, xRef, rfl⟩)

private theorem bv_extract_sign_extend_1_program_canonical
    (x low high k : Term) :
    x ≠ Term.Stuck -> low ≠ Term.Stuck -> high ≠ Term.Stuck ->
    k ≠ Term.Stuck ->
    bvExtractSignExtend1Program x low high k
        (bvExtractSignExtend1Prem x high) =
      bvExtractSignExtend1Term x low high k := by
  intro hX hLow hHigh hK
  unfold bvExtractSignExtend1Program bvExtractSignExtend1Prem
  rw [__eo_prog_bv_extract_sign_extend_1.eq_5
    x low high k high x hX hLow hHigh hK]
  simp [bvExtractSignExtend1Term, bvExtractSignExtend1Lhs,
    bvExtractSignExtend1Rhs, bvExtractTerm, __eo_requires, __eo_and,
    __eo_eq, native_ite, native_teq, native_not, native_and,
    hX, hLow, hHigh, hK]

private theorem bvExtractSignExtend1Program_normalize
    (x low high k P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    bvExtractSignExtend1Program x low high k P ≠ Term.Stuck ->
    P = bvExtractSignExtend1Prem x high ∧
      bvExtractSignExtend1Program x low high k P =
        bvExtractSignExtend1Term x low high k := by
  intro hXTrans hLowTrans hHighTrans hKTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hLow := RuleProofs.term_ne_stuck_of_has_smt_translation low hLowTrans
  have hHigh := RuleProofs.term_ne_stuck_of_has_smt_translation high hHighTrans
  have hK := RuleProofs.term_ne_stuck_of_has_smt_translation k hKTrans
  rcases bv_extract_sign_extend_1_premise_shape x low high k P
      hX hLow hHigh hK hProg with ⟨highRef, xRef, hP⟩
  have hReq := hProg
  rw [hP] at hReq
  unfold bvExtractSignExtend1Program bvExtractSignExtend1Prem at hReq
  rw [__eo_prog_bv_extract_sign_extend_1.eq_5
    x low high k highRef xRef hX hLow hHigh hK] at hReq
  rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
      high x highRef xRef
      (bvExtractSignExtend1Term x low high k) (by
        simpa [bvExtractSignExtend1Term, bvExtractSignExtend1Lhs,
          bvExtractSignExtend1Rhs, bvExtractTerm] using hReq) with
    ⟨hHighRef, hXRef⟩
  subst highRef
  subst xRef
  have hPCanon : P = bvExtractSignExtend1Prem x high := hP
  refine ⟨hPCanon, ?_⟩
  rw [hPCanon]
  exact bv_extract_sign_extend_1_program_canonical
    x low high k hX hLow hHigh hK

theorem typed_bv_extract_sign_extend_1_program
    (x low high k P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    __eo_typeof (bvExtractSignExtend1Program x low high k P) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvExtractSignExtend1Program x low high k P) := by
  intro hXTrans hLowTrans hHighTrans hKTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractSignExtend1Program_normalize x low high k P
      hXTrans hLowTrans hHighTrans hKTrans hProg with
    ⟨_hP, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvExtractSignExtend1Term x low high k) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_extract_sign_extend_1_term
    x low high k hXTrans hTermTy

theorem facts_bv_extract_sign_extend_1_program
    (M : SmtModel) (hM : model_wf M)
    (x low high k P : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation low ->
    RuleProofs.eo_has_smt_translation high ->
    RuleProofs.eo_has_smt_translation k ->
    __eo_typeof (bvExtractSignExtend1Program x low high k P) = Term.Bool ->
    eo_interprets M P true ->
    eo_interprets M (bvExtractSignExtend1Program x low high k P) true := by
  intro hXTrans hLowTrans hHighTrans hKTrans hResultTy _hPTrue
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvExtractSignExtend1Program_normalize x low high k P
      hXTrans hLowTrans hHighTrans hKTrans hProg with
    ⟨_hP, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvExtractSignExtend1Term x low high k) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact facts_bv_extract_sign_extend_1_term
    M hM x low high k hXTrans hTermTy
