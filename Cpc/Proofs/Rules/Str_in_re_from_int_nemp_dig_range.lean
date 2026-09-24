module

public import Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Cpc.Proofs.RuleSupport.StrInReFromIntDigRangeSupport
import all Init.Data.Repr

open Eo
open SmtEval
open Smtm
open RuleProofs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace StrInReFromIntNempDigRangeProof

abbrev digitRange : SmtRegLan :=
  StrInReFromIntDigRangeProof.digitRange

abbrev rangeTerm : Term :=
  StrInReFromIntDigRangeProof.rangeTerm

abbrev tailRangeTerm : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_concat)
      (Term.Apply (Term.UOp UserOp.re_mult) rangeTerm))
    (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))

abbrev concatRangeTerm : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_concat) rangeTerm)
    tailRangeTerm

abbrev lhs (n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.str_in_re)
      (Term.Apply (Term.UOp UserOp.str_from_int) n))
    concatRangeTerm

abbrev concl (n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs n)) (Term.Boolean true)

abbrev prem (n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
    (Term.Boolean true)

theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · simp [__eo_requires, hx, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · simp [__eo_requires, hxy, native_ite, native_teq] at h

theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · have hStuck : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, native_ite, hxy]
    exact False.elim (hReq hStuck)

theorem eo_eq_eq_true {t s : Term} (h : __eo_eq t s = Term.Boolean true) :
    s = t := by
  unfold __eo_eq at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [Term.Boolean.injEq, native_teq] at h
    exact of_decide_eq_true h

theorem prog_form (n P : Term)
    (hNe : __eo_prog_str_in_re_from_int_nemp_dig_range n (Proof.pf P) ≠
      Term.Stuck) :
    P = prem n ∧
      __eo_prog_str_in_re_from_int_nemp_dig_range n (Proof.pf P) =
        concl n := by
  unfold __eo_prog_str_in_re_from_int_nemp_dig_range at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · rename_i heqP
    injection heqP with hP
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    have hnEq := eo_eq_eq_true hReqArg
    rw [hnEq] at hP
    exact ⟨hP, hReqEq⟩
  · exact False.elim (hNe rfl)

theorem eo_typeof_concat_range_term :
    __eo_typeof concatRangeTerm = Term.UOp UserOp.RegLan := by
  native_decide

theorem typeof_arg_of_concl_bool (n : Term) :
    __eo_typeof (concl n) = Term.Bool ->
    __eo_typeof n = Term.UOp UserOp.Int := by
  intro hTy
  change __eo_typeof_eq (__eo_typeof (lhs n))
    (__eo_typeof (Term.Boolean true)) = Term.Bool at hTy
  have hLhsNotStuck : __eo_typeof (lhs n) ≠ Term.Stuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
      (__eo_typeof (lhs n)) (__eo_typeof (Term.Boolean true)) hTy).1
  have hFromTy :
      __eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) n) =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
    have hTypeNotStuck :
        __eo_typeof_str_in_re
            (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) n))
            (Term.UOp UserOp.RegLan) ≠ Term.Stuck := by
      change __eo_typeof_str_in_re
          (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) n))
          (__eo_typeof concatRangeTerm) ≠ Term.Stuck at hLhsNotStuck
      rw [eo_typeof_concat_range_term] at hLhsNotStuck
      exact hLhsNotStuck
    exact StrInReFromIntDigRangeProof.eo_typeof_str_in_re_reglan_eq_seq_char_of_ne_stuck
      (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) n))
      hTypeNotStuck
  change __eo_typeof_str_from_code (__eo_typeof n) =
    Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at hFromTy
  exact StrInReFromIntDigRangeProof.eo_typeof_str_from_code_eq_seq_char_arg_int
    (__eo_typeof n) hFromTy

theorem native_toDigitsCore_nonempty_of_acc :
    ∀ fuel n ds,
      ds ≠ [] -> Nat.toDigitsCore 10 fuel n ds ≠ []
  | 0, _n, ds, hds => by
      simpa [Nat.toDigitsCore.eq_1] using hds
  | fuel + 1, n, ds, hds => by
      rw [Nat.toDigitsCore.eq_2]
      by_cases hDiv : n / 10 = 0
      · rw [if_pos hDiv]
        simp
      · rw [if_neg hDiv]
        exact native_toDigitsCore_nonempty_of_acc fuel (n / 10)
          ((Nat.digitChar (n % 10)) :: ds) (by simp)

theorem native_toDigitsCore_empty_nonempty
    (fuel n : Nat) :
    Nat.toDigitsCore 10 (fuel + 1) n [] ≠ [] := by
  rw [Nat.toDigitsCore.eq_2]
  by_cases hDiv : n / 10 = 0
  · rw [if_pos hDiv]
    simp
  · rw [if_neg hDiv]
    exact native_toDigitsCore_nonempty_of_acc fuel (n / 10)
      [Nat.digitChar (n % 10)] (by simp)

theorem native_string_lit_nat_toString_nonempty
    (n : Nat) :
    native_string_lit (toString n) ≠ ([] : native_String) := by
  unfold native_string_lit
  rw [show (toString n).toList = Nat.toDigits 10 n by
    rw [show (toString n) = n.repr by rfl]
    unfold Nat.repr
    rw [String.toList_ofList]]
  rw [Nat.toDigits.eq_1]
  intro hNil
  apply native_toDigitsCore_empty_nonempty n n
  cases hDigits : Nat.toDigitsCore 10 (n + 1) n [] with
  | nil => rfl
  | cons d ds => simp [hDigits] at hNil

theorem native_str_from_int_exists_cons_of_nonneg
    (z : native_Int) (hz : 0 ≤ z) :
    ∃ c cs, native_str_from_int z = c :: cs := by
  cases z with
  | ofNat n =>
      unfold native_str_from_int
      have hNot : ¬ ((Int.ofNat n) < 0) := by
        exact Int.not_lt_of_ge (Int.natCast_nonneg n)
      rw [if_neg hNot]
      exact List.ne_nil_iff_exists_cons.mp
        (native_string_lit_nat_toString_nonempty n)
  | negSucc n =>
      have hBad : ¬ (0 ≤ Int.negSucc n) := by
        omega
      exact False.elim (hBad hz)

theorem native_string_valid_of_all_digits :
    ∀ xs : native_String,
      xs.all impl_native_char_is_digit = true -> native_string_valid xs = true
  | [], _ => by
      simp [native_string_valid]
  | c :: cs, hDigits => by
      have hParts :
          impl_native_char_is_digit c = true ∧
            cs.all impl_native_char_is_digit = true := by
        simpa [Bool.and_eq_true] using hDigits
      have hCsValid := native_string_valid_of_all_digits cs hParts.2
      rw [native_string_valid, List.all_eq_true]
      intro x hx
      cases hx with
      | head =>
          exact StrInReFromIntDigRangeProof.native_char_valid_of_digit c
            hParts.1
      | tail _ hxTail =>
          have hTailAll :
              ∀ x, x ∈ cs -> native_char_valid x = true := by
            simpa [native_string_valid, List.all_eq_true] using hCsValid
          exact hTailAll x hxTail

theorem native_str_in_re_str_to_re_empty :
    RuleProofs.native_str_in_re ([] : native_String) (native_str_to_re []) =
      true := by
  simp [RuleProofs.native_str_in_re, native_string_valid, native_str_to_re,
    impl_native_re_of_list, RuleProofs.nativeListInRe, native_re_nullable]

theorem native_str_in_re_from_int_nonempty_digit_range_star
    (z : native_Int) (hz : 0 ≤ z) :
    RuleProofs.native_str_in_re (native_str_from_int z)
      (native_re_concat digitRange
        (native_re_concat (native_re_mult digitRange) (native_str_to_re []))) =
      true := by
  rcases native_str_from_int_exists_cons_of_nonneg z hz with ⟨c, cs, hStr⟩
  have hDigitsAll :
      (c :: cs).all impl_native_char_is_digit = true := by
    have hAll :=
      StrInReFromIntDigRangeProof.native_str_from_int_all_digits z
    rwa [hStr] at hAll
  have hParts :
      impl_native_char_is_digit c = true ∧
        cs.all impl_native_char_is_digit = true := by
    simpa [Bool.and_eq_true] using hDigitsAll
  have hC :
      RuleProofs.native_str_in_re [c] digitRange = true :=
    StrInReFromIntDigRangeProof.native_str_in_re_digit_range_singleton c
      hParts.1
  have hCsList :
      RuleProofs.nativeListInRe cs (native_re_mult digitRange) = true :=
    StrInReFromIntDigRangeProof.nativeListInRe_digit_star_of_all_digits cs
      hParts.2
  have hCsValid : native_string_valid cs = true :=
    native_string_valid_of_all_digits cs hParts.2
  have hCs :
      RuleProofs.native_str_in_re cs (native_re_mult digitRange) = true := by
    simpa [RuleProofs.native_str_in_re, hCsValid] using hCsList
  have hTail :
      RuleProofs.native_str_in_re cs
        (native_re_concat (native_re_mult digitRange) (native_str_to_re [])) =
        true := by
    simpa using
      (RuleProofs.native_str_in_re_re_concat_intro cs []
        (native_re_mult digitRange) (native_str_to_re []) hCs
        native_str_in_re_str_to_re_empty)
  have hCons :
      RuleProofs.native_str_in_re (c :: cs)
        (native_re_concat digitRange
          (native_re_concat (native_re_mult digitRange) (native_str_to_re []))) =
        true := by
    simpa using
      (RuleProofs.native_str_in_re_re_concat_intro [c] cs digitRange
        (native_re_concat (native_re_mult digitRange) (native_str_to_re []))
        hC hTail)
  simpa [hStr] using hCons

theorem smtx_typeof_empty_string :
    __smtx_typeof (SmtTerm.String []) = SmtType.Seq SmtType.Char := by
  rw [__smtx_typeof.eq_4]
  simp [native_string_valid, native_ite]

theorem smtx_typeof_empty_str_to_re :
    __smtx_typeof (SmtTerm.str_to_re (SmtTerm.String [])) =
      SmtType.RegLan := by
  rw [typeof_str_to_re_eq]
  simp [smtx_typeof_empty_string, native_ite, native_Teq]

theorem smtx_typeof_star_range :
    __smtx_typeof
        (SmtTerm.re_mult
          (SmtTerm.re_range (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
            (SmtTerm.String StrInReFromIntDigRangeProof.nineStr))) =
      SmtType.RegLan := by
  rw [typeof_re_mult_eq]
  simp [StrInReFromIntDigRangeProof.smtx_typeof_digit_range, native_ite,
    native_Teq]

theorem smtx_typeof_tail_range :
    __smtx_typeof
        (SmtTerm.re_concat
          (SmtTerm.re_mult
            (SmtTerm.re_range
              (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
              (SmtTerm.String StrInReFromIntDigRangeProof.nineStr)))
          (SmtTerm.str_to_re (SmtTerm.String []))) =
      SmtType.RegLan := by
  rw [typeof_re_concat_eq]
  simp [smtx_typeof_star_range, smtx_typeof_empty_str_to_re, native_ite,
    native_Teq]

theorem smtx_typeof_concat_range :
    __smtx_typeof
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
            (SmtTerm.String StrInReFromIntDigRangeProof.nineStr))
          (SmtTerm.re_concat
            (SmtTerm.re_mult
              (SmtTerm.re_range
                (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
                (SmtTerm.String StrInReFromIntDigRangeProof.nineStr)))
            (SmtTerm.str_to_re (SmtTerm.String [])))) =
      SmtType.RegLan := by
  rw [typeof_re_concat_eq]
  simp [StrInReFromIntDigRangeProof.smtx_typeof_digit_range,
    smtx_typeof_tail_range, native_ite, native_Teq]

theorem typed_concl
    (n : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int) :
    RuleProofs.eo_has_bool_type (concl n) := by
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNTy
  have hFromTy :
      __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) =
        SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_from_int_eq, hNSmtTy]
    simp [native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs n)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re
          (SmtTerm.str_from_int (__eo_to_smt n))
          (SmtTerm.re_concat
            (SmtTerm.re_range
              (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
              (SmtTerm.String StrInReFromIntDigRangeProof.nineStr))
            (SmtTerm.re_concat
              (SmtTerm.re_mult
                (SmtTerm.re_range
                  (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
                  (SmtTerm.String StrInReFromIntDigRangeProof.nineStr)))
              (SmtTerm.str_to_re (SmtTerm.String []))))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hFromTy, smtx_typeof_concat_range, native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def] <;> simp only
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs n)
    (Term.Boolean true) (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; simp)

theorem eval_smt_numeral (M : SmtModel) (n : Int) :
    __smtx_model_eval M (SmtTerm.Numeral n) = SmtValue.Numeral n := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_re_concat_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.re_concat x y) =
      __smtx_model_eval_re_concat
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_empty_str_to_re
    (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.str_to_re (SmtTerm.String [])) =
      SmtValue.RegLan (native_str_to_re []) := by
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
    RuleProofs.native_unpack_string_pack_string]

theorem smtx_eval_star_range
    (M : SmtModel) :
    __smtx_model_eval M
        (SmtTerm.re_mult
          (SmtTerm.re_range (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
            (SmtTerm.String StrInReFromIntDigRangeProof.nineStr))) =
      SmtValue.RegLan (native_re_mult digitRange) := by
  rw [StrInReFromIntDigRangeProof.smtx_eval_re_mult_term_eq]
  rw [StrInReFromIntDigRangeProof.smtx_eval_digit_range]
  rfl

theorem smtx_eval_concat_range
    (M : SmtModel) :
    __smtx_model_eval M
        (SmtTerm.re_concat
          (SmtTerm.re_range (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
            (SmtTerm.String StrInReFromIntDigRangeProof.nineStr))
          (SmtTerm.re_concat
            (SmtTerm.re_mult
              (SmtTerm.re_range
                (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
                (SmtTerm.String StrInReFromIntDigRangeProof.nineStr)))
            (SmtTerm.str_to_re (SmtTerm.String [])))) =
      SmtValue.RegLan
        (native_re_concat digitRange
          (native_re_concat (native_re_mult digitRange) (native_str_to_re []))) := by
  rw [smtx_eval_re_concat_term_eq]
  rw [StrInReFromIntDigRangeProof.smtx_eval_digit_range]
  rw [smtx_eval_re_concat_term_eq]
  rw [smtx_eval_star_range, smtx_eval_empty_str_to_re]
  rfl

theorem nonneg_of_premise
    (M : SmtModel) (hM : model_wf M) (n : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hPrem : eo_interprets M (prem n) true) :
    ∃ z, __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral z ∧
      0 ≤ z := by
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    StrInReFromIntDigRangeProof.smtx_typeof_of_eo_int n hNTrans hNTy
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases int_value_canonical hNEvalTy with ⟨z, hNEval⟩
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))
      (Term.Boolean true) hPrem
  have hGeqEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n)
              (Term.Numeral 0))) =
        SmtValue.Boolean (native_zleq 0 z) := by
    change __smtx_model_eval M
        (SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0)) =
      SmtValue.Boolean (native_zleq 0 z)
    simp only [__smtx_model_eval, hNEval, eval_smt_numeral,
      __smtx_model_eval_geq, __smtx_model_eval_leq]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) =
      SmtValue.Boolean true
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hGeqEval, hTrueEval] at hPremRel
  have hBoolEq :
      SmtValue.Boolean (native_zleq 0 z) = SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  have hzBool : native_zleq 0 z = true := by
    injection hBoolEq
  exact ⟨z, hNEval, by simpa [native_zleq] using hzBool⟩

theorem facts
    (M : SmtModel) (hM : model_wf M) (n : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hPrem : eo_interprets M (prem n) true) :
    eo_interprets M (concl n) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl n) :=
    typed_concl n hNTrans hNTy
  rcases nonneg_of_premise M hM n hNTrans hNTy hPrem with
    ⟨z, hNEval, hz⟩
  have hFromEval :
      __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n)) =
        SmtValue.Seq (native_pack_string (native_str_from_int z)) := by
    rw [StrInReFromIntDigRangeProof.smtx_eval_str_from_int_term_eq, hNEval]
    rfl
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs n)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_from_int (__eo_to_smt n))
          (SmtTerm.re_concat
            (SmtTerm.re_range
              (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
              (SmtTerm.String StrInReFromIntDigRangeProof.nineStr))
            (SmtTerm.re_concat
              (SmtTerm.re_mult
                (SmtTerm.re_range
                  (SmtTerm.String StrInReFromIntDigRangeProof.zeroStr)
                  (SmtTerm.String StrInReFromIntDigRangeProof.nineStr)))
              (SmtTerm.str_to_re (SmtTerm.String []))))) =
      SmtValue.Boolean true
    rw [StrInReFromIntDigRangeProof.smtx_eval_str_in_re_term_eq]
    rw [hFromEval, smtx_eval_concat_range]
    simp only [__smtx_model_eval_str_in_re,
      RuleProofs.native_unpack_seq_pack_string]
    rw [← RuleProofs.native_str_in_re_eq_model]
    exact congrArg SmtValue.Boolean
      (native_str_in_re_from_int_nonempty_digit_range_star z hz)
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs n) (Term.Boolean true)
    hBool <| by
      have hTrueEval :
          __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
            SmtValue.Boolean true := by
        change __smtx_model_eval M (SmtTerm.Boolean true) =
          SmtValue.Boolean true
        rw [__smtx_model_eval.eq_def] <;> simp only
      rw [hLhsEval, hTrueEval]
      exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

end StrInReFromIntNempDigRangeProof

public theorem cmd_step_str_in_re_from_int_nemp_dig_range_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_from_int_nemp_dig_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_from_int_nemp_dig_range args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_from_int_nemp_dig_range args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s
      CRule.str_in_re_from_int_nemp_dig_range args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk]
                      using hCmdTrans.1
                  show StepRuleProperties M [__eo_state_proven_nth s n1]
                    (__eo_prog_str_in_re_from_int_nemp_dig_range a1
                      (Proof.pf (__eo_state_proven_nth s n1)))
                  generalize hP : __eo_state_proven_nth s n1 = P
                  have hProgNe :
                      __eo_prog_str_in_re_from_int_nemp_dig_range a1
                          (Proof.pf P) ≠ Term.Stuck := by
                    rw [← hP]
                    change __eo_cmd_step_proven s
                        CRule.str_in_re_from_int_nemp_dig_range
                        (CArgList.cons a1 CArgList.nil)
                        (CIndexList.cons n1 CIndexList.nil) ≠ Term.Stuck
                    exact hProg
                  obtain ⟨hPremShape, hProgEq⟩ :=
                    StrInReFromIntNempDigRangeProof.prog_form a1 P hProgNe
                  have hResultTyProg :
                      __eo_typeof
                          (__eo_prog_str_in_re_from_int_nemp_dig_range a1
                            (Proof.pf P)) =
                        Term.Bool := by
                    rw [← hP]
                    change __eo_typeof
                        (__eo_cmd_step_proven s
                          CRule.str_in_re_from_int_nemp_dig_range
                          (CArgList.cons a1 CArgList.nil)
                          (CIndexList.cons n1 CIndexList.nil)) = Term.Bool
                    exact hResultTy
                  have hConclTy :
                      __eo_typeof
                          (StrInReFromIntNempDigRangeProof.concl a1) =
                        Term.Bool := by
                    rw [hProgEq] at hResultTyProg
                    exact hResultTyProg
                  have hA1Ty : __eo_typeof a1 = Term.UOp UserOp.Int :=
                    StrInReFromIntNempDigRangeProof.typeof_arg_of_concl_bool
                      a1 hConclTy
                  have hBool :=
                    StrInReFromIntNempDigRangeProof.typed_concl a1
                      hA1Trans hA1Ty
                  rw [hProgEq]
                  refine ⟨?_,
                    RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      hBool⟩
                  intro hEv
                  have hPrem :
                      eo_interprets M
                        (StrInReFromIntNempDigRangeProof.prem a1) true := by
                    have h := hEv.true_here P (by simp)
                    rwa [hPremShape] at h
                  exact StrInReFromIntNempDigRangeProof.facts M hM a1
                    hA1Trans hA1Ty hPrem
