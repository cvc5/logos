module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport
public import Cpc.Proofs.RuleSupport.RegexValueSupport
import all Cpc.Proofs.RuleSupport.RegexValueSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrInReRangeElimProof

private abbrev mkLenOne (s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_len) s))
    (Term.Numeral 1)

private abbrev lhs (s c1 c2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) c1) c2)

private abbrev rhs (s c1 c2 : Term) : Term :=
  let codeS := Term.Apply (Term.UOp UserOp.str_to_code) s
  Term.Apply
    (Term.Apply (Term.UOp UserOp.and)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.leq)
          (Term.Apply (Term.UOp UserOp.str_to_code) c1))
        codeS))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.leq) codeS)
          (Term.Apply (Term.UOp UserOp.str_to_code) c2)))
      (Term.Boolean true))

private abbrev concl (s c1 c2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs s c1 c2)) (rhs s c1 c2)

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not, SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

private theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

private theorem eo_typeof_eq_bool_operands_not_stuck (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · exact ⟨hA, hB⟩

private theorem eo_and_eq_true {x y : Term}
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  unfold __eo_and at h
  split at h
  · rename_i b1 b2
    simp only [Term.Boolean.injEq, SmtEval.native_and, Bool.and_eq_true] at h
    exact ⟨by rw [h.1], by rw [h.2]⟩
  · rename_i w1 n1 w2 n2
    simp only [__eo_requires, native_ite] at h
    split at h
    · split at h <;> exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

private theorem eqs_of_eo_and2_eq_true
    (x1 y1 x2 y2 : Term)
    (h : __eo_and (__eo_eq x1 y1) (__eo_eq x2 y2) = Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 := by
  rcases eo_and_eq_true h with ⟨h1, h2⟩
  exact ⟨eo_eq_eq_true h1, eo_eq_eq_true h2⟩

private theorem eo_typeof_str_in_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char ∧ B = Term.RegLan := by
  cases A with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_in_re] at h ⊢
                cases B with
                | UOp opb =>
                    cases opb <;> simp [__eo_typeof_str_in_re] at h ⊢
                | _ => simp [__eo_typeof_str_in_re] at h
            | _ => simp [__eo_typeof_str_in_re] at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

private theorem eo_typeof_re_range_eq_reglan_args_seq_char (A B : Term)
    (h : __eo_typeof_re_range A B = Term.UOp UserOp.RegLan) :
    A = Term.Apply Term.Seq Term.Char ∧
      B = Term.Apply Term.Seq Term.Char := by
  unfold __eo_typeof_re_range at h
  split at h
  · exact ⟨rfl, rfl⟩
  · cases h

private theorem prog_form (s c1 c2 P1 P2 : Term)
    (hNe : __eo_prog_str_in_re_range_elim s c1 c2 (Proof.pf P1)
        (Proof.pf P2) ≠ Term.Stuck) :
    P1 = mkLenOne c1 ∧ P2 = mkLenOne c2 ∧
      __eo_prog_str_in_re_range_elim s c1 c2 (Proof.pf P1)
        (Proof.pf P2) = concl s c1 c2 := by
  unfold __eo_prog_str_in_re_range_elim at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i heqP1 heqP2
    injection heqP1 with hP1
    injection heqP2 with hP2
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rcases eqs_of_eo_and2_eq_true _ _ _ _ hReqArg with ⟨hc1, hc2⟩
    rw [hc1] at hP1
    rw [hc2] at hP2
    exact ⟨hP1, hP2, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem native_unpack_string_singleton_of_seq_len_one (ss : SmtSeq)
    (hLen : native_seq_len (native_unpack_seq ss) = 1) :
    ∃ c : native_Char, native_unpack_string ss = [c] := by
  cases hUnpack : native_unpack_seq ss with
  | nil =>
      simp [native_seq_len, hUnpack] at hLen
  | cons v vs =>
      cases vs with
      | nil =>
          exact ⟨impl_native_ssm_char_of_value v, by simp [native_unpack_string, hUnpack]⟩
      | cons w ws =>
          have hLen' : (Int.ofNat (List.length (v :: w :: ws))) = 1 := by
            simpa [native_seq_len, hUnpack] using hLen
          have hLen'' : (Int.ofNat ws.length) + 1 + 1 = 1 := by
            simpa using hLen'
          have hNonneg : (0 : Int) ≤ Int.ofNat ws.length := Int.natCast_nonneg _
          omega

private theorem native_string_valid_cons_parts
    {c : native_Char} {cs : native_String}
    (h : native_string_valid (c :: cs) = true) :
    native_char_valid c = true ∧ native_string_valid cs = true := by
  simp [native_string_valid] at h
  constructor
  · exact h.1
  · rw [native_string_valid, List.all_eq_true]
    intro x hx
    exact h.2 x hx

private theorem native_zleq_nat_neg_one_false (n : Nat) :
    native_zleq (Int.ofNat n) (-1) = false := by
  have hgt : (-1 : Int) < Int.ofNat n :=
    Int.lt_of_lt_of_le (by decide) (Int.natCast_nonneg n)
  have hn : ¬ (Int.ofNat n ≤ (-1 : Int)) := Int.not_le_of_gt hgt
  simpa [native_zleq, SmtEval.native_zleq] using decide_eq_false hn

private theorem decide_natCast_le_neg_one_false (n : Nat) :
    decide (Int.ofNat n ≤ (-1 : Int)) = false := by
  have hgt : (-1 : Int) < Int.ofNat n :=
    Int.lt_of_lt_of_le (by decide) (Int.natCast_nonneg n)
  exact decide_eq_false (Int.not_le_of_gt hgt)

private theorem native_str_in_re_range_iff_code_bounds
    (str : native_String) (lo hi : native_Char)
    (hLo : native_char_valid lo = true)
    (hHi : native_char_valid hi = true)
    (hValid : native_string_valid str = true) :
    RuleProofs.native_str_in_re str (native_re_range [lo] [hi]) =
      native_and
        (native_zleq (native_str_to_code [lo]) (native_str_to_code str))
        (native_and
          (native_zleq (native_str_to_code str) (native_str_to_code [hi]))
          true) := by
  cases str with
  | nil =>
      simp [native_re_range, RuleProofs.native_str_in_re, hValid,
        RuleProofs.nativeListInRe, native_re_nullable, native_str_to_code,
        hLo, hHi, native_and, native_zleq, SmtEval.native_zleq,
        decide_natCast_le_neg_one_false lo]
      exact Int.lt_of_lt_of_le (by decide) (Int.natCast_nonneg lo)
  | cons c rest =>
      rcases native_string_valid_cons_parts hValid with ⟨hc, hRestValid⟩
      cases rest with
      | nil =>
          by_cases hLoC : lo ≤ c <;> by_cases hCHi : c ≤ hi <;>
            simp [native_re_range, RuleProofs.native_str_in_re, hValid,
              RuleProofs.nativeListInRe, native_re_deriv, native_re_nullable,
              native_re_elem_valid, impl_native_re_elem_le, native_str_to_code, hLo,
              hHi, hc, hLoC, hCHi, native_and, native_zleq,
              SmtEval.native_zleq]
      | cons d ds =>
          by_cases hBounds : lo ≤ c ∧ c ≤ hi <;>
            simp [native_re_range, RuleProofs.native_str_in_re, hValid,
              RuleProofs.nativeListInRe, RuleProofs.nativeListInRe_empty,
              native_re_deriv, native_re_nullable, native_re_elem_valid,
              impl_native_re_elem_le, native_str_to_code, hLo, hHi, hc, hBounds,
              native_and, native_zleq_nat_neg_one_false lo,
              decide_natCast_le_neg_one_false lo, SmtEval.native_zleq]
          all_goals
            exact Int.lt_of_lt_of_le (by decide) (Int.natCast_nonneg lo)

private theorem smtx_typeof_of_eo_seq_char
    (a : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq Term.Char) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq SmtType.Char := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  rw [hTy] at hTyRaw
  simp only [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hTyRaw
  exact hTyRaw

private theorem typed_concl
    (s c1 c2 : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hC1Ty : __smtx_typeof (__eo_to_smt c1) = SmtType.Seq SmtType.Char)
    (hC2Ty : __smtx_typeof (__eo_to_smt c2) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (concl s c1 c2) := by
  let codeS := Term.Apply (Term.UOp UserOp.str_to_code) s
  let codeC1 := Term.Apply (Term.UOp UserOp.str_to_code) c1
  let codeC2 := Term.Apply (Term.UOp UserOp.str_to_code) c2
  have hRangeTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) c1) c2)) =
        SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_range (__eo_to_smt c1) (__eo_to_smt c2)) =
      SmtType.RegLan
    rw [typeof_re_range_eq]
    simp [hC1Ty, hC2Ty, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs s c1 c2)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s)
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) c1) c2))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hSTy, hRangeTy, native_ite, native_Teq]
  have hCodeSTy : __smtx_typeof (__eo_to_smt codeS) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt s)) = SmtType.Int
    rw [typeof_str_to_code_eq]
    simp [hSTy, native_ite, native_Teq]
  have hCodeC1Ty : __smtx_typeof (__eo_to_smt codeC1) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt c1)) = SmtType.Int
    rw [typeof_str_to_code_eq]
    simp [hC1Ty, native_ite, native_Teq]
  have hCodeC2Ty : __smtx_typeof (__eo_to_smt codeC2) = SmtType.Int := by
    change __smtx_typeof (SmtTerm.str_to_code (__eo_to_smt c2)) = SmtType.Int
    rw [typeof_str_to_code_eq]
    simp [hC2Ty, native_ite, native_Teq]
  have hLe1Ty :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.leq) codeC1) codeS)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.leq (__eo_to_smt codeC1) (__eo_to_smt codeS)) =
      SmtType.Bool
    rw [typeof_leq_eq]
    simp [hCodeC1Ty, hCodeSTy, native_ite, native_Teq,
      __smtx_typeof_arith_overload_op_2_ret]
  have hLe2Ty :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.leq) codeS) codeC2)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.leq (__eo_to_smt codeS) (__eo_to_smt codeC2)) =
      SmtType.Bool
    rw [typeof_leq_eq]
    simp [hCodeSTy, hCodeC2Ty, native_ite, native_Teq,
      __smtx_typeof_arith_overload_op_2_ret]
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.Apply (Term.UOp UserOp.leq) codeS) codeC2))
              (Term.Boolean true))) =
        SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.and
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) codeS) codeC2))
          (SmtTerm.Boolean true)) = SmtType.Bool
    rw [typeof_and_eq]
    simp [hLe2Ty, __smtx_typeof.eq_1, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhs s c1 c2)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.and
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) codeC1) codeS))
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.and)
                (Term.Apply (Term.Apply (Term.UOp UserOp.leq) codeS) codeC2))
              (Term.Boolean true)))) = SmtType.Bool
    -- rewrite the component types before `simp` normalises
    -- `__eo_to_smt (Apply ..)` past their left-hand sides
    rw [typeof_and_eq, hLe1Ty, hInnerTy]
    simp [native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs s c1 c2) (rhs s c1 c2)
    (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; decide)

private theorem seq_len_one_of_prem
    (M : SmtModel) (s : Term) (ss : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hPrem : eo_interprets M (mkLenOne s) true) :
    native_seq_len (native_unpack_seq ss) = 1 := by
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.UOp UserOp.str_len) s) (Term.Numeral 1) hPrem
  have hLenEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
        SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
    change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss))
    simp [__smtx_model_eval, __smtx_model_eval_str_len, hSEval]
  have hOneEval :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 1)) =
        SmtValue.Numeral 1 := by
    change __smtx_model_eval M (SmtTerm.Numeral 1) = SmtValue.Numeral 1
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hLenEval, hOneEval] at hPremRel
  have hLenValueEq :
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) =
        SmtValue.Numeral 1 :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  injection hLenValueEq

private theorem facts
    (M : SmtModel) (hM : model_wf M) (s c1 c2 : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hC1Ty : __smtx_typeof (__eo_to_smt c1) = SmtType.Seq SmtType.Char)
    (hC2Ty : __smtx_typeof (__eo_to_smt c2) = SmtType.Seq SmtType.Char)
    (hPremC1 : eo_interprets M (mkLenOne c1) true)
    (hPremC2 : eo_interprets M (mkLenOne c2) true) :
    eo_interprets M (concl s c1 c2) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl s c1 c2) :=
    typed_concl s c1 c2 hSTy hC1Ty hC2Ty
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hC1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hC1Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c1) (by
        unfold term_has_non_none_type
        rw [hC1Ty]
        simp)
  have hC2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt c2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hC2Ty] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt c2) (by
        unfold term_has_non_none_type
        rw [hC2Ty]
        simp)
  rcases RuleProofs.seq_value_canonical_with_char_type hSEvalTy with
    ⟨ss, hSEval, hSsTy⟩
  rcases RuleProofs.seq_value_canonical_with_char_type hC1EvalTy with
    ⟨sc1, hC1Eval, hSc1Ty⟩
  rcases RuleProofs.seq_value_canonical_with_char_type hC2EvalTy with
    ⟨sc2, hC2Eval, hSc2Ty⟩
  have hSValid : native_string_valid (native_unpack_string ss) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simp only [hSEval] at hSEvalTy
    exact hSEvalTy
  have hC1Valid : native_string_valid (native_unpack_string sc1) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simp only [hC1Eval] at hC1EvalTy
    exact hC1EvalTy
  have hC2Valid : native_string_valid (native_unpack_string sc2) = true := by
    apply native_unpack_string_valid_of_typeof_seq_char
    simp only [hC2Eval] at hC2EvalTy
    exact hC2EvalTy
  have hC1Len : native_seq_len (native_unpack_seq sc1) = 1 :=
    seq_len_one_of_prem M c1 sc1 hC1Eval hPremC1
  have hC2Len : native_seq_len (native_unpack_seq sc2) = 1 :=
    seq_len_one_of_prem M c2 sc2 hC2Eval hPremC2
  rcases native_unpack_string_singleton_of_seq_len_one sc1 hC1Len with
    ⟨lo, hC1String⟩
  rcases native_unpack_string_singleton_of_seq_len_one sc2 hC2Len with
    ⟨hi, hC2String⟩
  have hLoValid : native_char_valid lo = true := by
    simpa [hC1String, native_string_valid] using hC1Valid
  have hHiValid : native_char_valid hi = true := by
    simpa [hC2String, native_string_valid] using hC2Valid
  have hSc1Unpack :
      native_unpack_seq sc1 =
        impl_native_string_to_values (native_unpack_string sc1) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char (by
      exact hSc1Ty)
  have hSc2Unpack :
      native_unpack_seq sc2 =
        impl_native_string_to_values (native_unpack_string sc2) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char (by
      exact hSc2Ty)
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs s c1 c2)) =
        __smtx_model_eval M (__eo_to_smt (rhs s c1 c2)) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s)
          (SmtTerm.re_range (__eo_to_smt c1) (__eo_to_smt c2))) =
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt c1))
            (SmtTerm.str_to_code (__eo_to_smt s)))
          (SmtTerm.and
            (SmtTerm.leq (SmtTerm.str_to_code (__eo_to_smt s))
              (SmtTerm.str_to_code (__eo_to_smt c2)))
            (SmtTerm.Boolean true)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
      __smtx_model_eval_re_range, __smtx_model_eval_str_to_code,
      __smtx_model_eval_leq, __smtx_model_eval_and,
      hSEval, hC1Eval, hC2Eval]
    rw [hSc1Unpack, hSc2Unpack]
    rw [hC1String, hC2String]
    rw [RuleProofs.model_str_in_re_unpack_eq_string_of_value_type ss _ hSsTy]
    exact native_str_in_re_range_iff_code_bounds
      (native_unpack_string ss) lo hi hLoValid hHiValid hSValid
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs s c1 c2) (rhs s c1 c2) hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt (rhs s c1 c2)))

end StrInReRangeElimProof

public theorem cmd_step_str_in_re_range_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_range_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_range_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_range_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_range_elim args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  cases premises with
                  | nil =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | cons n1 premises =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n2 premises =>
                          cases premises with
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                          | nil =>
                              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk]
                                  using hCmdTrans.1
                              have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk]
                                  using hCmdTrans.2.1
                              have hA3Trans : RuleProofs.eo_has_smt_translation a3 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk]
                                  using hCmdTrans.2.2.1
                              show StepRuleProperties M
                                [__eo_state_proven_nth s n1,
                                  __eo_state_proven_nth s n2]
                                (__eo_prog_str_in_re_range_elim a1 a2 a3
                                  (Proof.pf (__eo_state_proven_nth s n1))
                                  (Proof.pf (__eo_state_proven_nth s n2)))
                              generalize hP1 : __eo_state_proven_nth s n1 = P1
                              generalize hP2 : __eo_state_proven_nth s n2 = P2
                              have hProgNe :
                                  __eo_prog_str_in_re_range_elim a1 a2 a3
                                      (Proof.pf P1) (Proof.pf P2) ≠ Term.Stuck := by
                                rw [← hP1, ← hP2]
                                change __eo_cmd_step_proven s CRule.str_in_re_range_elim
                                    (CArgList.cons a1
                                      (CArgList.cons a2
                                        (CArgList.cons a3 CArgList.nil)))
                                    (CIndexList.cons n1
                                      (CIndexList.cons n2 CIndexList.nil)) ≠
                                  Term.Stuck
                                exact hProg
                              obtain ⟨hP1Shape, hP2Shape, hProgEq⟩ :=
                                StrInReRangeElimProof.prog_form a1 a2 a3 P1 P2 hProgNe
                              have hResultTyProg :
                                  __eo_typeof
                                      (__eo_prog_str_in_re_range_elim a1 a2 a3
                                        (Proof.pf P1) (Proof.pf P2)) =
                                    Term.Bool := by
                                rw [← hP1, ← hP2]
                                change __eo_typeof
                                    (__eo_cmd_step_proven s CRule.str_in_re_range_elim
                                      (CArgList.cons a1
                                        (CArgList.cons a2
                                          (CArgList.cons a3 CArgList.nil)))
                                      (CIndexList.cons n1
                                        (CIndexList.cons n2 CIndexList.nil))) =
                                  Term.Bool
                                exact hResultTy
                              have hConclTy :
                                  __eo_typeof
                                      (StrInReRangeElimProof.concl a1 a2 a3) =
                                    Term.Bool := by
                                rw [hProgEq] at hResultTyProg
                                exact hResultTyProg
                              change __eo_typeof_eq
                                  (__eo_typeof
                                    (StrInReRangeElimProof.lhs a1 a2 a3))
                                  (__eo_typeof
                                    (StrInReRangeElimProof.rhs a1 a2 a3)) =
                                Term.Bool at hConclTy
                              have hLhsNotStuck :
                                  __eo_typeof
                                      (StrInReRangeElimProof.lhs a1 a2 a3) ≠
                                    Term.Stuck :=
                                (StrInReRangeElimProof.eo_typeof_eq_bool_operands_not_stuck
                                  (__eo_typeof
                                    (StrInReRangeElimProof.lhs a1 a2 a3))
                                  (__eo_typeof
                                    (StrInReRangeElimProof.rhs a1 a2 a3))
                                  hConclTy).1
                              have hA1Ty :
                                  __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                                change __eo_typeof_str_in_re (__eo_typeof a1)
                                    (__eo_typeof
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.re_range) a2)
                                        a3)) ≠ Term.Stuck at hLhsNotStuck
                                exact
                                  (StrInReRangeElimProof.eo_typeof_str_in_re_args_of_ne_stuck
                                    (__eo_typeof a1)
                                    (__eo_typeof
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.re_range) a2)
                                        a3))
                                    hLhsNotStuck).1
                              have hRangeTy :
                                  __eo_typeof
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.re_range) a2)
                                        a3) = Term.UOp UserOp.RegLan := by
                                change __eo_typeof_str_in_re (__eo_typeof a1)
                                    (__eo_typeof
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.re_range) a2)
                                        a3)) ≠ Term.Stuck at hLhsNotStuck
                                exact
                                  (StrInReRangeElimProof.eo_typeof_str_in_re_args_of_ne_stuck
                                    (__eo_typeof a1)
                                    (__eo_typeof
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.re_range) a2)
                                        a3))
                                    hLhsNotStuck).2
                              have hArgTypes :
                                  __eo_typeof a2 = Term.Apply Term.Seq Term.Char ∧
                                    __eo_typeof a3 =
                                      Term.Apply Term.Seq Term.Char := by
                                change __eo_typeof_re_range (__eo_typeof a2)
                                    (__eo_typeof a3) =
                                  Term.UOp UserOp.RegLan at hRangeTy
                                exact
                                  StrInReRangeElimProof.eo_typeof_re_range_eq_reglan_args_seq_char
                                    (__eo_typeof a2) (__eo_typeof a3) hRangeTy
                              have hA1SmtTy :=
                                StrInReRangeElimProof.smtx_typeof_of_eo_seq_char
                                  a1 hA1Trans hA1Ty
                              have hA2SmtTy :=
                                StrInReRangeElimProof.smtx_typeof_of_eo_seq_char
                                  a2 hA2Trans hArgTypes.1
                              have hA3SmtTy :=
                                StrInReRangeElimProof.smtx_typeof_of_eo_seq_char
                                  a3 hA3Trans hArgTypes.2
                              have hBool :=
                                StrInReRangeElimProof.typed_concl a1 a2 a3
                                  hA1SmtTy hA2SmtTy hA3SmtTy
                              rw [hProgEq]
                              refine ⟨?_,
                                RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hBool⟩
                              intro hEv
                              have hPremC1 :
                                  eo_interprets M
                                    (StrInReRangeElimProof.mkLenOne a2) true := by
                                have h := hEv.true_here P1 (by simp)
                                rwa [hP1Shape] at h
                              have hPremC2 :
                                  eo_interprets M
                                    (StrInReRangeElimProof.mkLenOne a3) true := by
                                have h := hEv.true_here P2 (by simp)
                                rwa [hP2Shape] at h
                              exact StrInReRangeElimProof.facts M hM a1 a2 a3
                                hA1SmtTy hA2SmtTy hA3SmtTy hPremC1 hPremC2
