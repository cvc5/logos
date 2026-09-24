module

public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReRangeNonSingleton1Proof

private abbrev innerLenOne (s : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.UOp UserOp.str_len) s))
    (Term.Numeral 1)

private abbrev mkNotLenOne (s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (innerLenOne s))
    (Term.Boolean false)

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

private theorem eo_typeof_re_range_eq_reglan_args_seq_char (A B : Term)
    (h : __eo_typeof_re_range A B = Term.UOp UserOp.RegLan) :
    A = Term.Apply Term.Seq Term.Char ∧
      B = Term.Apply Term.Seq Term.Char := by
  unfold __eo_typeof_re_range at h
  split at h
  · exact ⟨rfl, rfl⟩
  · cases h

private theorem prog_form (s t P : Term)
    (hNe : __eo_prog_re_range_non_singleton_1 s t (Proof.pf P) ≠ Term.Stuck) :
    P = mkNotLenOne s ∧
      __eo_prog_re_range_non_singleton_1 s t (Proof.pf P) = concl s t := by
  unfold __eo_prog_re_range_non_singleton_1 at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i heqP
    injection heqP with hP
    have hReqArg := eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq := eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    have hsEq := eo_eq_eq_true hReqArg
    rw [hsEq] at hP
    exact ⟨hP, hReqEq⟩
  · exact False.elim (hNe rfl)

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

private theorem native_re_range_empty_of_first_len_ne_one
    (ss tt : SmtSeq)
    (hLenNe : native_seq_len (native_unpack_seq ss) ≠ 1) :
    native_re_range (native_unpack_seq ss) (native_unpack_seq tt) =
      native_re_none := by
  cases hUnpack : native_unpack_seq ss with
  | nil =>
      simp [hUnpack, native_re_range, native_re_none]
  | cons v vs =>
      cases vs with
      | nil =>
          have hLen : native_seq_len (native_unpack_seq ss) = 1 := by
            simp [native_seq_len, hUnpack]
          exact False.elim (hLenNe hLen)
      | cons w ws =>
          simp [hUnpack, native_re_range, native_re_none]

private theorem facts
    (M : SmtModel) (hM : model_wf M) (s t : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hTTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (mkNotLenOne s) true) :
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
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M (innerLenOne s) (Term.Boolean false) hPrem
  have hLenEval :
      __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
        SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
    simp [__smtx_model_eval, __smtx_model_eval_str_len, hSEval]
  have hOneEval :
      __smtx_model_eval M (SmtTerm.Numeral 1) =
        SmtValue.Numeral 1 := by
    rw [__smtx_model_eval.eq_def] <;> simp only
  have hInnerEval :
      __smtx_model_eval M (__eo_to_smt (innerLenOne s)) =
        SmtValue.Boolean
          (native_veq
            (SmtValue.Numeral (native_seq_len (native_unpack_seq ss)))
            (SmtValue.Numeral 1)) := by
    change __smtx_model_eval M
        (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt s)) (SmtTerm.Numeral 1)) =
      SmtValue.Boolean
        (native_veq
          (SmtValue.Numeral (native_seq_len (native_unpack_seq ss)))
          (SmtValue.Numeral 1))
    rw [smtx_eval_eq_term_eq, hLenEval, hOneEval]
    rfl
  have hFalseEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by
    change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInnerEval, hFalseEval] at hPremRel
  have hPremValueEq :
      SmtValue.Boolean
          (native_veq
            (SmtValue.Numeral (native_seq_len (native_unpack_seq ss)))
            (SmtValue.Numeral 1)) =
        SmtValue.Boolean false :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  have hNativeEqFalse :
      native_veq
          (SmtValue.Numeral (native_seq_len (native_unpack_seq ss)))
          (SmtValue.Numeral 1) =
        false := by
    injection hPremValueEq
  have hLenNe : native_seq_len (native_unpack_seq ss) ≠ 1 := by
    intro hLen
    rw [hLen] at hNativeEqFalse
    simp [native_veq] at hNativeEqFalse
  have hRangeNone :
      native_re_range (native_unpack_seq ss) (native_unpack_seq tt) =
        native_re_none :=
    native_re_range_empty_of_first_len_ne_one ss tt hLenNe
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs s t)) =
        SmtValue.RegLan
          (native_re_range (native_unpack_seq ss) (native_unpack_seq tt)) := by
    change __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt s) (__eo_to_smt t)) =
      SmtValue.RegLan
        (native_re_range (native_unpack_seq ss) (native_unpack_seq tt))
    simp [__smtx_model_eval, __smtx_model_eval_re_range, hSEval, hTEval]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none =
      SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_def] <;> simp only
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs s t) rhs hBool <| by
    rw [hLhsEval, hRhsEval, hRangeNone]
    change SmtValue.Boolean (native_re_ext_eq native_re_none native_re_none) =
      SmtValue.Boolean true
    congr
    simp

end ReRangeNonSingleton1Proof

public theorem cmd_step_re_range_non_singleton_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_non_singleton_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_range_non_singleton_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_non_singleton_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_range_non_singleton_1 args premises ≠
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
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                      have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                      show StepRuleProperties M [__eo_state_proven_nth s n1]
                        (__eo_prog_re_range_non_singleton_1 a1 a2
                          (Proof.pf (__eo_state_proven_nth s n1)))
                      generalize hP : __eo_state_proven_nth s n1 = P
                      have hProgNe :
                          __eo_prog_re_range_non_singleton_1 a1 a2 (Proof.pf P) ≠
                            Term.Stuck := by
                        rw [← hP]
                        change __eo_cmd_step_proven s CRule.re_range_non_singleton_1
                            (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                            (CIndexList.cons n1 CIndexList.nil) ≠ Term.Stuck
                        exact hProg
                      obtain ⟨hPremShape, hProgEq⟩ :=
                        ReRangeNonSingleton1Proof.prog_form a1 a2 P hProgNe
                      have hResultTyProg :
                          __eo_typeof
                              (__eo_prog_re_range_non_singleton_1 a1 a2 (Proof.pf P)) =
                            Term.Bool := by
                        rw [← hP]
                        change __eo_typeof
                            (__eo_cmd_step_proven s CRule.re_range_non_singleton_1
                              (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                              (CIndexList.cons n1 CIndexList.nil)) = Term.Bool
                        exact hResultTy
                      have hConclTy :
                          __eo_typeof (ReRangeNonSingleton1Proof.concl a1 a2) =
                            Term.Bool := by
                        rw [hProgEq] at hResultTyProg
                        exact hResultTyProg
                      have hLhsTy :
                          __eo_typeof (ReRangeNonSingleton1Proof.lhs a1 a2) =
                            Term.UOp UserOp.RegLan := by
                        change __eo_typeof_eq
                            (__eo_typeof (ReRangeNonSingleton1Proof.lhs a1 a2))
                            (__eo_typeof ReRangeNonSingleton1Proof.rhs) =
                          Term.Bool at hConclTy
                        have hTyEq :=
                          support_eo_typeof_eq_bool_operands_eq
                            (__eo_typeof (ReRangeNonSingleton1Proof.lhs a1 a2))
                            (__eo_typeof ReRangeNonSingleton1Proof.rhs) hConclTy
                        simpa [ReRangeNonSingleton1Proof.rhs] using hTyEq
                      have hArgTypes :
                          __eo_typeof a1 = Term.Apply Term.Seq Term.Char ∧
                            __eo_typeof a2 = Term.Apply Term.Seq Term.Char := by
                        change __eo_typeof_re_range (__eo_typeof a1) (__eo_typeof a2) =
                          Term.UOp UserOp.RegLan at hLhsTy
                        exact
                          ReRangeNonSingleton1Proof.eo_typeof_re_range_eq_reglan_args_seq_char
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
                        exact hTyRaw
                      have hBool :=
                        ReRangeNonSingleton1Proof.typed_concl a1 a2 hA1SmtTy hA2SmtTy
                      rw [hProgEq]
                      refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                        hBool⟩
                      intro hEv
                      have hPrem :
                          eo_interprets M
                            (ReRangeNonSingleton1Proof.mkNotLenOne a1) true := by
                        have h := hEv.true_here P (by simp)
                        rwa [hPremShape] at h
                      exact ReRangeNonSingleton1Proof.facts M hM a1 a2
                        hA1SmtTy hA2SmtTy hPrem
