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

namespace ReRangeEmpProof

private abbrev mkLenOne (s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_len) s))
    (Term.Numeral 1)

private abbrev mkCodeLt (t s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.UOp UserOp.str_to_code) t))
        (Term.Apply (Term.UOp UserOp.str_to_code) s)))
    (Term.Boolean true)

private abbrev lhs (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s) t

private abbrev rhs : Term :=
  Term.UOp UserOp.re_none

private abbrev concl (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs s t)) rhs

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

private theorem eqs_of_eo_and4_eq_true
    (x1 y1 x2 y2 x3 y3 x4 y4 : Term)
    (h : __eo_and
        (__eo_and (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
          (__eo_eq x3 y3))
        (__eo_eq x4 y4) = Term.Boolean true) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  rcases eo_and_eq_true h with ⟨h123, h4⟩
  rcases eo_and_eq_true h123 with ⟨h12, h3⟩
  rcases eo_and_eq_true h12 with ⟨h1, h2⟩
  exact ⟨eo_eq_eq_true h1, eo_eq_eq_true h2,
    eo_eq_eq_true h3, eo_eq_eq_true h4⟩

private theorem eo_typeof_re_range_eq_reglan_args_seq_char (A B : Term)
    (h : __eo_typeof_re_range A B = Term.UOp UserOp.RegLan) :
    A = Term.Apply Term.Seq Term.Char ∧
      B = Term.Apply Term.Seq Term.Char := by
  unfold __eo_typeof_re_range at h
  split at h
  · exact ⟨rfl, rfl⟩
  · cases h

private theorem prog_form (s t P1 P2 P3 : Term)
    (hNe : __eo_prog_re_range_emp s t (Proof.pf P1) (Proof.pf P2)
        (Proof.pf P3) ≠ Term.Stuck) :
    P1 = mkLenOne s ∧ P2 = mkLenOne t ∧ P3 = mkCodeLt t s ∧
      __eo_prog_re_range_emp s t (Proof.pf P1) (Proof.pf P2)
        (Proof.pf P3) = concl s t := by
  unfold __eo_prog_re_range_emp at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i heqP1 heqP2 heqP3
    injection heqP1 with hP1
    injection heqP2 with hP2
    injection heqP3 with hP3
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rcases eqs_of_eo_and4_eq_true _ _ _ _ _ _ _ _ hReqArg with
      ⟨hs2, ht2, ht3, hs3⟩
    rw [hs2] at hP1
    rw [ht2] at hP2
    rw [ht3, hs3] at hP3
    exact ⟨hP1, hP2, hP3, hReqEq⟩
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

private theorem native_str_in_re_range_empty_of_hi_lt_lo
    (lo hi : native_Char)
    (hLo : native_char_valid lo = true)
    (hHi : native_char_valid hi = true)
    (hHiLtLo : hi < lo)
    (str : native_String) (hValid : native_string_valid str = true) :
    native_str_in_re str (native_re_range [lo] [hi]) = false := by
  cases str with
  | nil =>
      simp [native_re_range, native_str_in_re, impl_native_string_to_values,
            native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_nullable]
  | cons c rest =>
      rcases native_string_valid_cons_parts hValid with ⟨hc, hRestValid⟩
      have hBounds : ¬ (lo ≤ c ∧ c ≤ hi) := by
        intro h
        have hLoLeHi : lo ≤ hi := Nat.le_trans h.1 h.2
        exact (Nat.not_lt_of_ge hLoLeHi) hHiLtLo
      cases rest with
      | nil =>
          simp [native_re_range, native_str_in_re, impl_native_string_to_values,
            native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_deriv,
            native_re_nullable, hLo, hHi, hc, hBounds]
      | cons d ds =>
          simp [native_re_range, native_str_in_re, impl_native_string_to_values,
            native_re_str_valid, native_re_elem_valid, impl_native_re_elem_le, hValid, native_re_deriv,
            native_re_nullable, hLo, hHi, hc, hBounds,
            RuleProofs.native_re_nullable_foldl_empty]

private theorem typed_concl
    (s t : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hTTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (concl s t) := by
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs s t)) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_range (__eo_to_smt s) (__eo_to_smt t)) =
      SmtType.RegLan
    rw [typeof_re_range_eq]
    simp [hSTy, hTTy, native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
    rw [__smtx_typeof.eq_def] <;> simp only
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs s t) rhs
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

private theorem code_lt_of_prem
    (M : SmtModel) (s t : Term) (ss tt : SmtSeq)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hTEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt)
    (hPrem : eo_interprets M (mkCodeLt t s) true) :
    native_zlt (native_str_to_code (native_unpack_string tt))
      (native_str_to_code (native_unpack_string ss)) = true := by
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.lt)
          (Term.Apply (Term.UOp UserOp.str_to_code) t))
        (Term.Apply (Term.UOp UserOp.str_to_code) s))
      (Term.Boolean true) hPrem
  have hLtEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.lt)
                (Term.Apply (Term.UOp UserOp.str_to_code) t))
              (Term.Apply (Term.UOp UserOp.str_to_code) s))) =
        SmtValue.Boolean
          (native_zlt (native_str_to_code (native_unpack_string tt))
            (native_str_to_code (native_unpack_string ss))) := by
    change __smtx_model_eval M
        (SmtTerm.lt (SmtTerm.str_to_code (__eo_to_smt t))
          (SmtTerm.str_to_code (__eo_to_smt s))) =
      SmtValue.Boolean
        (native_zlt (native_str_to_code (native_unpack_string tt))
          (native_str_to_code (native_unpack_string ss)))
    simp [__smtx_model_eval, __smtx_model_eval_lt,
      __smtx_model_eval_str_to_code, hSEval, hTEval]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hLtEval, hTrueEval] at hPremRel
  have hValueEq :
      SmtValue.Boolean
          (native_zlt (native_str_to_code (native_unpack_string tt))
            (native_str_to_code (native_unpack_string ss))) =
        SmtValue.Boolean true :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  injection hValueEq

private theorem facts
    (M : SmtModel) (hM : model_wf M) (s t : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hTTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hPremS : eo_interprets M (mkLenOne s) true)
    (hPremT : eo_interprets M (mkLenOne t) true)
    (hPremLt : eo_interprets M (mkCodeLt t s) true) :
    eo_interprets M (concl s t) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl s t) :=
    typed_concl s t hSTy hTTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨tt, hTEval⟩
  have hSSTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simp only [hSEval] at hSEvalTy
    exact hSEvalTy
  have hTTTy : __smtx_typeof_seq_value tt = SmtType.Seq SmtType.Char := by
    simp only [hTEval] at hTEvalTy
    exact hTEvalTy
  have hSSValid : native_string_valid (native_unpack_string ss) = true :=
    native_unpack_string_valid_of_typeof_seq_char hSSTy
  have hTTValid : native_string_valid (native_unpack_string tt) = true :=
    native_unpack_string_valid_of_typeof_seq_char hTTTy
  have hSUnpack :
      native_unpack_seq ss = impl_native_string_to_values (native_unpack_string ss) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSSTy
  have hTUnpack :
      native_unpack_seq tt = impl_native_string_to_values (native_unpack_string tt) :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hTTTy
  have hSLen : native_seq_len (native_unpack_seq ss) = 1 :=
    seq_len_one_of_prem M s ss hSEval hPremS
  have hTLen : native_seq_len (native_unpack_seq tt) = 1 :=
    seq_len_one_of_prem M t tt hTEval hPremT
  rcases native_unpack_string_singleton_of_seq_len_one ss hSLen with
    ⟨lo, hSString⟩
  rcases native_unpack_string_singleton_of_seq_len_one tt hTLen with
    ⟨hi, hTString⟩
  have hLoValid : native_char_valid lo = true := by
    simpa [hSString, native_string_valid] using hSSValid
  have hHiValid : native_char_valid hi = true := by
    simpa [hTString, native_string_valid] using hTTValid
  have hCodeLt :
      native_zlt (native_str_to_code (native_unpack_string tt))
        (native_str_to_code (native_unpack_string ss)) = true :=
    code_lt_of_prem M s t ss tt hSEval hTEval hPremLt
  have hHiLtLo : hi < lo := by
    have hInt : (hi : Int) < (lo : Int) := by
      simpa [hSString, hTString, native_str_to_code, hLoValid, hHiValid,
        native_zlt] using hCodeLt
    exact Int.ofNat_lt.mp hInt
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs s t)) =
        SmtValue.RegLan
          (native_re_range (native_unpack_string ss) (native_unpack_string tt)) := by
    change __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt s) (__eo_to_smt t)) =
      SmtValue.RegLan
        (native_re_range (native_unpack_string ss) (native_unpack_string tt))
    simp [__smtx_model_eval, __smtx_model_eval_re_range, hSEval, hTEval,
      hSUnpack, hTUnpack]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_def] <;> simp only
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs s t) rhs hBool <| by
    rw [hLhsEval, hRhsEval, hSString, hTString]
    change SmtValue.Boolean
        (native_re_ext_eq (native_re_range [lo] [hi]) native_re_none) =
      SmtValue.Boolean true
    congr
    simp
    intro str hValid
    rw [native_str_in_re_range_empty_of_hi_lt_lo lo hi hLoValid hHiValid
      hHiLtLo str hValid]
    symm
    exact RuleProofs.model_str_in_re_re_none _

end ReRangeEmpProof

public theorem cmd_step_re_range_emp_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_range_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_emp args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_range_emp args premises ≠ Term.Stuck :=
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
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n3 premises =>
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
                              show StepRuleProperties M
                                [__eo_state_proven_nth s n1,
                                  __eo_state_proven_nth s n2,
                                  __eo_state_proven_nth s n3]
                                (__eo_prog_re_range_emp a1 a2
                                  (Proof.pf (__eo_state_proven_nth s n1))
                                  (Proof.pf (__eo_state_proven_nth s n2))
                                  (Proof.pf (__eo_state_proven_nth s n3)))
                              generalize hP1 : __eo_state_proven_nth s n1 = P1
                              generalize hP2 : __eo_state_proven_nth s n2 = P2
                              generalize hP3 : __eo_state_proven_nth s n3 = P3
                              have hProgNe :
                                  __eo_prog_re_range_emp a1 a2 (Proof.pf P1)
                                      (Proof.pf P2) (Proof.pf P3) ≠ Term.Stuck := by
                                rw [← hP1, ← hP2, ← hP3]
                                change __eo_cmd_step_proven s CRule.re_range_emp
                                    (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                                    (CIndexList.cons n1
                                      (CIndexList.cons n2
                                        (CIndexList.cons n3 CIndexList.nil))) ≠
                                  Term.Stuck
                                exact hProg
                              obtain ⟨hP1Shape, hP2Shape, hP3Shape, hProgEq⟩ :=
                                ReRangeEmpProof.prog_form a1 a2 P1 P2 P3 hProgNe
                              have hResultTyProg :
                                  __eo_typeof
                                      (__eo_prog_re_range_emp a1 a2 (Proof.pf P1)
                                        (Proof.pf P2) (Proof.pf P3)) =
                                    Term.Bool := by
                                rw [← hP1, ← hP2, ← hP3]
                                change __eo_typeof
                                    (__eo_cmd_step_proven s CRule.re_range_emp
                                      (CArgList.cons a1
                                        (CArgList.cons a2 CArgList.nil))
                                      (CIndexList.cons n1
                                        (CIndexList.cons n2
                                          (CIndexList.cons n3 CIndexList.nil)))) =
                                  Term.Bool
                                exact hResultTy
                              have hConclTy :
                                  __eo_typeof (ReRangeEmpProof.concl a1 a2) =
                                    Term.Bool := by
                                rw [hProgEq] at hResultTyProg
                                exact hResultTyProg
                              have hLhsTy :
                                  __eo_typeof (ReRangeEmpProof.lhs a1 a2) =
                                    Term.UOp UserOp.RegLan := by
                                change __eo_typeof_eq
                                    (__eo_typeof (ReRangeEmpProof.lhs a1 a2))
                                    (__eo_typeof ReRangeEmpProof.rhs) =
                                  Term.Bool at hConclTy
                                have hTyEq :=
                                  support_eo_typeof_eq_bool_operands_eq
                                    (__eo_typeof (ReRangeEmpProof.lhs a1 a2))
                                    (__eo_typeof ReRangeEmpProof.rhs) hConclTy
                                simpa [ReRangeEmpProof.rhs] using hTyEq
                              have hArgTypes :
                                  __eo_typeof a1 = Term.Apply Term.Seq Term.Char ∧
                                    __eo_typeof a2 =
                                      Term.Apply Term.Seq Term.Char := by
                                change __eo_typeof_re_range (__eo_typeof a1)
                                    (__eo_typeof a2) =
                                  Term.UOp UserOp.RegLan at hLhsTy
                                exact
                                  ReRangeEmpProof.eo_typeof_re_range_eq_reglan_args_seq_char
                                    (__eo_typeof a1) (__eo_typeof a2) hLhsTy
                              have hA1SmtTy :
                                  __smtx_typeof (__eo_to_smt a1) =
                                    SmtType.Seq SmtType.Char := by
                                have hTyRaw :
                                    __smtx_typeof (__eo_to_smt a1) =
                                      __eo_to_smt_type (__eo_typeof a1) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    a1 hA1Trans
                                rw [hArgTypes.1] at hTyRaw
                                simp only [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hTyRaw
                                exact hTyRaw
                              have hA2SmtTy :
                                  __smtx_typeof (__eo_to_smt a2) =
                                    SmtType.Seq SmtType.Char := by
                                have hTyRaw :
                                    __smtx_typeof (__eo_to_smt a2) =
                                      __eo_to_smt_type (__eo_typeof a2) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    a2 hA2Trans
                                rw [hArgTypes.2] at hTyRaw
                                simp only [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hTyRaw
                                exact hTyRaw
                              have hBool :=
                                ReRangeEmpProof.typed_concl a1 a2 hA1SmtTy hA2SmtTy
                              rw [hProgEq]
                              refine ⟨?_,
                                RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                  hBool⟩
                              intro hEv
                              have hPremS :
                                  eo_interprets M (ReRangeEmpProof.mkLenOne a1)
                                    true := by
                                have h := hEv.true_here P1 (by simp)
                                rwa [hP1Shape] at h
                              have hPremT :
                                  eo_interprets M (ReRangeEmpProof.mkLenOne a2)
                                    true := by
                                have h := hEv.true_here P2 (by simp)
                                rwa [hP2Shape] at h
                              have hPremLt :
                                  eo_interprets M
                                    (ReRangeEmpProof.mkCodeLt a2 a1) true := by
                                have h := hEv.true_here P3 (by simp)
                                rwa [hP3Shape] at h
                              exact ReRangeEmpProof.facts M hM a1 a2
                                hA1SmtTy hA2SmtTy hPremS hPremT hPremLt
