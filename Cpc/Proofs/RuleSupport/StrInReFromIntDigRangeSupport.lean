module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Init.Data.Repr

open Eo
open SmtEval
open Smtm
open RuleProofs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace StrInReFromIntDigRangeProof

abbrev zeroStr : native_String := native_string_lit "0"
abbrev nineStr : native_String := native_string_lit "9"

abbrev digitRange : SmtRegLan :=
  native_re_range zeroStr nineStr

abbrev rangeTerm : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_range) (Term.String zeroStr))
    (Term.String nineStr)

private abbrev starRangeTerm : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) rangeTerm

private abbrev lhs (n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.str_in_re)
      (Term.Apply (Term.UOp UserOp.str_from_int) n))
    starRangeTerm

abbrev concl (n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs n)) (Term.Boolean true)

theorem prog_eq_of_ne_stuck (n : Term) :
    n ≠ Term.Stuck ->
    __eo_prog_str_in_re_from_int_dig_range n = concl n := by
  intro hN
  cases n <;> simp [__eo_prog_str_in_re_from_int_dig_range, concl, lhs,
    starRangeTerm, rangeTerm] at hN ⊢

private theorem native_char_is_digit_digitChar_lt10
    (n : Nat) (hn : n < 10) :
    impl_native_char_is_digit (Char.toNat (Nat.digitChar n)) = true := by
  by_cases h0 : n = 0
  · subst n; native_decide
  by_cases h1 : n = 1
  · subst n; native_decide
  by_cases h2 : n = 2
  · subst n; native_decide
  by_cases h3 : n = 3
  · subst n; native_decide
  by_cases h4 : n = 4
  · subst n; native_decide
  by_cases h5 : n = 5
  · subst n; native_decide
  by_cases h6 : n = 6
  · subst n; native_decide
  by_cases h7 : n = 7
  · subst n; native_decide
  by_cases h8 : n = 8
  · subst n; native_decide
  by_cases h9 : n = 9
  · subst n; native_decide
  · have : False := by omega
    exact False.elim this

private theorem native_toDigitsCore_all_digits :
    ∀ fuel n ds,
      (ds.map Char.toNat).all impl_native_char_is_digit = true ->
        ((Nat.toDigitsCore 10 fuel n ds).map Char.toNat).all
          impl_native_char_is_digit = true
  | 0, _n, _ds, hds => by
      simpa [Nat.toDigitsCore.eq_1] using hds
  | fuel + 1, n, ds, hds => by
      rw [Nat.toDigitsCore.eq_2]
      by_cases hDiv : n / 10 = 0
      · rw [if_pos hDiv]
        have hDigit :=
          native_char_is_digit_digitChar_lt10 (n % 10) (Nat.mod_lt n (by decide))
        simpa [hDigit, hds]
      · rw [if_neg hDiv]
        have hDigit :=
          native_char_is_digit_digitChar_lt10 (n % 10) (Nat.mod_lt n (by decide))
        exact native_toDigitsCore_all_digits fuel (n / 10)
          ((Nat.digitChar (n % 10)) :: ds) (by
            simpa [hDigit, hds])

private theorem native_string_lit_nat_toString_all_digits
    (n : Nat) :
    (native_string_lit (toString n)).all impl_native_char_is_digit = true := by
  unfold native_string_lit
  rw [show (toString n).toList = Nat.toDigits 10 n by
    rw [show (toString n) = n.repr by rfl]
    unfold Nat.repr
    rw [String.toList_ofList]]
  rw [Nat.toDigits.eq_1]
  exact native_toDigitsCore_all_digits (n + 1) n [] (by simp)

theorem native_str_from_int_all_digits
    (i : native_Int) :
    (native_str_from_int i).all impl_native_char_is_digit = true := by
  cases i with
  | ofNat n =>
      unfold native_str_from_int
      have hNot : ¬ ((Int.ofNat n) < 0) := by
        exact Int.not_lt_of_ge (Int.natCast_nonneg n)
      rw [if_neg hNot]
      exact native_string_lit_nat_toString_all_digits n
  | negSucc n =>
      unfold native_str_from_int
      have hNeg : (Int.negSucc n) < 0 := by
        exact Int.negSucc_lt_zero n
      rw [if_pos hNeg]
      simp [native_string_lit]

theorem native_char_valid_of_digit
    (c : native_Char)
    (hDigit : impl_native_char_is_digit c = true) :
    native_char_valid c = true := by
  have hBounds : 48 ≤ c ∧ c ≤ 57 := by
    unfold impl_native_char_is_digit at hDigit
    simpa [Bool.and_eq_true] using hDigit
  unfold native_char_valid
  have h57 : 57 < 196608 := by native_decide
  exact decide_eq_true (Nat.lt_of_le_of_lt hBounds.2 h57)

theorem native_digit_bounds
    (c : native_Char)
    (hDigit : impl_native_char_is_digit c = true) :
    48 ≤ c ∧ c ≤ 57 := by
  unfold impl_native_char_is_digit at hDigit
  simpa [Bool.and_eq_true] using hDigit

theorem nativeListInRe_digit_range_singleton
    (c : native_Char)
    (hDigit : impl_native_char_is_digit c = true) :
    RuleProofs.nativeListInRe [c] digitRange = true := by
  have hValid : native_char_valid c = true :=
    native_char_valid_of_digit c hDigit
  have hBounds := native_digit_bounds c hDigit
  have hLoValid : native_char_valid 48 = true := by native_decide
  have hHiValid : native_char_valid 57 = true := by native_decide
  simp [digitRange, zeroStr, nineStr, native_re_range, native_string_lit,
    RuleProofs.nativeListInRe, native_re_deriv, native_re_nullable,
    native_re_elem_valid, impl_native_re_elem_le, hValid, hLoValid, hHiValid,
    hBounds.1, hBounds.2]

theorem native_str_in_re_digit_range_singleton
    (c : native_Char)
    (hDigit : impl_native_char_is_digit c = true) :
    RuleProofs.native_str_in_re [c] digitRange = true := by
  have hValidChar : native_char_valid c = true :=
    native_char_valid_of_digit c hDigit
  have hValidString : native_string_valid [c] = true := by
    simpa [native_string_valid, hValidChar]
  have hList := nativeListInRe_digit_range_singleton c hDigit
  simpa [RuleProofs.native_str_in_re, hValidString] using hList

theorem nativeListInRe_digit_star_of_all_digits
    (xs : native_String)
    (hDigits : xs.all impl_native_char_is_digit = true) :
    RuleProofs.nativeListInRe xs (native_re_mult digitRange) = true := by
  induction xs with
  | nil =>
      have hsimpa :=
        RuleProofs.nativeListInRe_nil_mk_star digitRange
      try simp [native_re_mult] at hsimpa ⊢
      exact hsimpa
  | cons c cs ih =>
      have hParts :
          impl_native_char_is_digit c = true ∧
            cs.all impl_native_char_is_digit = true := by
        simpa [Bool.and_eq_true] using hDigits
      have hCValid : native_string_valid [c] = true := by
        have hValidChar := native_char_valid_of_digit c hParts.1
        simpa [native_string_valid, hValidChar]
      have hCBase : RuleProofs.native_str_in_re [c] digitRange = true :=
        native_str_in_re_digit_range_singleton c hParts.1
      have hCStarStr :
          RuleProofs.native_str_in_re [c] (native_re_mult digitRange) = true :=
        RuleProofs.native_includes_star_self digitRange [c] hCValid hCBase
      have hCStar :
          RuleProofs.nativeListInRe [c]
            (native_re_mk_star digitRange) = true := by
        have hsimpa := hCStarStr
        try simp [RuleProofs.native_str_in_re, hCValid, native_re_mult] at hsimpa ⊢
        exact hsimpa
      have hCsStar :
          RuleProofs.nativeListInRe cs
            (native_re_mk_star digitRange) = true := by
        have hsimpa := ih hParts.2
        try simp [native_re_mult] at hsimpa ⊢
        exact hsimpa
      have hAppend :=
        RuleProofs.nativeListInRe_mk_star_append [c] cs digitRange
          hCStar hCsStar
      have hsimpa := hAppend
      try simp [native_re_mult] at hsimpa ⊢
      exact hsimpa

private theorem native_str_in_re_from_int_digit_range_star
    (i : native_Int) :
    RuleProofs.native_str_in_re (native_str_from_int i)
      (native_re_mult digitRange) = true := by
  have hValid : native_string_valid (native_str_from_int i) = true :=
    native_str_from_int_valid i
  have hDigits : (native_str_from_int i).all impl_native_char_is_digit = true :=
    native_str_from_int_all_digits i
  have hList :=
    nativeListInRe_digit_star_of_all_digits (native_str_from_int i) hDigits
  simpa [RuleProofs.native_str_in_re, hValid] using hList

private theorem eo_typeof_star_range_term :
    __eo_typeof starRangeTerm = Term.UOp UserOp.RegLan := by
  native_decide

theorem eo_typeof_str_in_re_reglan_eq_seq_char_of_ne_stuck (T : Term)
    (h : __eo_typeof_str_in_re T (Term.UOp UserOp.RegLan) ≠ Term.Stuck) :
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_in_re] at h ⊢
            | _ => simp [__eo_typeof_str_in_re] at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

theorem eo_typeof_str_from_code_eq_seq_char_arg_int
    (T : Term)
    (h : __eo_typeof_str_from_code T =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    T = Term.UOp UserOp.Int := by
  have hNe : __eo_typeof_str_from_code T ≠ Term.Stuck := by
    rw [h]
    native_decide
  cases T <;> simp [__eo_typeof_str_from_code] at hNe ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_str_from_code] at hNe ⊢

theorem typeof_arg_of_prog_bool (n : Term) :
    __eo_typeof (__eo_prog_str_in_re_from_int_dig_range n) = Term.Bool ->
    __eo_typeof n = Term.UOp UserOp.Int := by
  intro hTy
  by_cases hN : n = Term.Stuck
  · subst n
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hBad : __eo_typeof Term.Stuck ≠ Term.Bool := by native_decide
    exact False.elim (hBad hTy)
  · rw [prog_eq_of_ne_stuck n hN] at hTy
    change __eo_typeof_eq (__eo_typeof (lhs n)) (__eo_typeof (Term.Boolean true)) =
      Term.Bool at hTy
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
            (__eo_typeof starRangeTerm) ≠ Term.Stuck at hLhsNotStuck
        rw [eo_typeof_star_range_term] at hLhsNotStuck
        exact hLhsNotStuck
      exact eo_typeof_str_in_re_reglan_eq_seq_char_of_ne_stuck
        (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) n))
        hTypeNotStuck
    change __eo_typeof_str_from_code (__eo_typeof n) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) at hFromTy
    exact eo_typeof_str_from_code_eq_seq_char_arg_int (__eo_typeof n) hFromTy

theorem smtx_typeof_of_eo_int
    (n : Term)
    (hTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : __eo_typeof n = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt n) = __eo_to_smt_type (__eo_typeof n) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation n hTrans
  rw [hTy] at hTyRaw
  simpa using hTyRaw

private theorem smtx_typeof_zero_string :
    __smtx_typeof (SmtTerm.String zeroStr) = SmtType.Seq SmtType.Char := by
  native_decide

private theorem smtx_typeof_nine_string :
    __smtx_typeof (SmtTerm.String nineStr) = SmtType.Seq SmtType.Char := by
  native_decide

theorem smtx_typeof_digit_range :
    __smtx_typeof
        (SmtTerm.re_range (SmtTerm.String zeroStr) (SmtTerm.String nineStr)) =
      SmtType.RegLan := by
  rw [typeof_re_range_eq]
  simp [smtx_typeof_zero_string, smtx_typeof_nine_string, native_ite,
    native_Teq]

private theorem smtx_typeof_star_range :
    __smtx_typeof
        (SmtTerm.re_mult
          (SmtTerm.re_range (SmtTerm.String zeroStr) (SmtTerm.String nineStr))) =
      SmtType.RegLan := by
  rw [typeof_re_mult_eq]
  simp [smtx_typeof_digit_range, native_ite, native_Teq]

theorem typed_concl
    (n : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int) :
    RuleProofs.eo_has_bool_type (concl n) := by
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    smtx_typeof_of_eo_int n hNTrans hNTy
  have hFromTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) n)) =
        SmtType.Seq SmtType.Char := by
    change __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) =
      SmtType.Seq SmtType.Char
    rw [typeof_str_from_int_eq, hNSmtTy]
    simp [native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs n)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re
          (SmtTerm.str_from_int (__eo_to_smt n))
          (SmtTerm.re_mult
            (SmtTerm.re_range (SmtTerm.String zeroStr)
              (SmtTerm.String nineStr)))) =
      SmtType.Bool
    have hFromTy' :
        __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) =
          SmtType.Seq SmtType.Char := by
      have hsimpa := hFromTy
      try simp at hsimpa ⊢
      exact hsimpa
    rw [typeof_str_in_re_eq]
    simp [hFromTy', smtx_typeof_star_range, native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    rw [__smtx_typeof.eq_def] <;> simp only
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs n)
    (Term.Boolean true) (by rw [hLhsTy, hRhsTy])
    (by rw [hLhsTy]; simp)

theorem smtx_eval_str_from_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_from_int x) =
      __smtx_model_eval_str_from_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_re_mult_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.re_mult x) =
      __smtx_model_eval_re_mult (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_str_in_re_term_eq
    (M : SmtModel) (x r : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_in_re x r) =
      __smtx_model_eval_str_in_re
        (__smtx_model_eval M x) (__smtx_model_eval M r) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_digit_range
    (M : SmtModel) :
    __smtx_model_eval M
        (SmtTerm.re_range (SmtTerm.String zeroStr) (SmtTerm.String nineStr)) =
      SmtValue.RegLan digitRange := by
  simp [__smtx_model_eval, __smtx_model_eval_re_range,
    RuleProofs.native_unpack_string_pack_string, digitRange, zeroStr, nineStr]

private theorem smtx_eval_star_range
    (M : SmtModel) :
    __smtx_model_eval M
        (SmtTerm.re_mult
          (SmtTerm.re_range (SmtTerm.String zeroStr) (SmtTerm.String nineStr))) =
      SmtValue.RegLan (native_re_mult digitRange) := by
  rw [smtx_eval_re_mult_term_eq]
  rw [smtx_eval_digit_range]
  rfl

theorem facts
    (M : SmtModel) (hM : model_wf M) (n : Term)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int) :
    eo_interprets M (concl n) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl n) :=
    typed_concl n hNTrans hNTy
  have hNSmtTy : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    smtx_typeof_of_eo_int n hNTrans hNTy
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases int_value_canonical hNEvalTy with ⟨z, hNEval⟩
  have hFromEval :
      __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt n)) =
        SmtValue.Seq (native_pack_string (native_str_from_int z)) := by
    rw [smtx_eval_str_from_int_term_eq, hNEval]
    rfl
  have hFromIntMem :
      Smtm.native_str_in_re
          (impl_native_string_to_values (native_str_from_int z))
          (native_re_mult digitRange) = true := by
    rw [← RuleProofs.native_str_in_re_eq_model]
    exact native_str_in_re_from_int_digit_range_star z
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs n)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re
          (SmtTerm.str_from_int (__eo_to_smt n))
          (SmtTerm.re_mult
            (SmtTerm.re_range (SmtTerm.String zeroStr)
              (SmtTerm.String nineStr)))) =
      SmtValue.Boolean true
    rw [smtx_eval_str_in_re_term_eq]
    rw [hFromEval, smtx_eval_star_range]
    simp [__smtx_model_eval_str_in_re,
      RuleProofs.native_unpack_string_pack_string,
      hFromIntMem]
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

end StrInReFromIntDigRangeProof
