module

public import Cpc.Proofs.RuleSupport.ReInterCstringSupport
import all Cpc.Proofs.RuleSupport.ReInterCstringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInterCstringNegProof

private abbrev reInter (x ys : Term) : Term :=
  ReInterCstringProof.reInter x ys

private abbrev lhs (x ys s : Term) : Term :=
  ReInterCstringProof.lhs x ys s

private abbrev rhs : Term :=
  Term.UOp UserOp.re_none

private abbrev prem (s x ys : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
        (lhs x ys s)))
    (Term.Boolean false)

private abbrev concl (x ys s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs x ys s)) rhs

private theorem prog_form (x ys s P : Term)
    (hNe : __eo_prog_re_inter_cstring_neg x ys s (Proof.pf P) ≠ Term.Stuck) :
    P = prem s x ys ∧
      __eo_prog_re_inter_cstring_neg x ys s (Proof.pf P) = concl x ys s := by
  unfold __eo_prog_re_inter_cstring_neg at hNe ⊢
  split at hNe
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · exact False.elim (hNe rfl)
  · rename_i hPrem
    injection hPrem with hPremEq
    have hReqArg := ReInterCstringProof.eo_requires_arg_eq_of_ne_stuck hNe
    have hReqEq :=
      ReInterCstringProof.eo_requires_eq_result_of_ne_stuck _ _ _ hNe
    rcases ReInterCstringProof.eqs_of_eo_and4_eq_true _ _ _ _ _ _ _ _
        hReqArg with
      ⟨hs2, hs3, hx, hys⟩
    rw [hs2, hs3, hx, hys] at hPremEq
    exact ⟨hPremEq, hReqEq⟩
  · exact False.elim (hNe rfl)

private theorem smtx_typeof_str_to_re_of_seq_char
    (s : Term)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
      SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hSTy, native_ite, native_Teq]

private theorem typed_concl
    (x ys s : Term)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    RuleProofs.eo_has_bool_type (concl x ys s) := by
  have hStrToReTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
        SmtType.RegLan :=
    smtx_typeof_str_to_re_of_seq_char s hSTy
  have hStrToReSmtTy :
      __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) = SmtType.RegLan := by
    have hsimpa := hStrToReTy
    try simp at hsimpa ⊢
    exact hsimpa
  have hInnerTy :
      __smtx_typeof (__eo_to_smt (reInter x ys)) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys)) =
      SmtType.RegLan
    rw [typeof_re_inter_eq]
    simp [hXTy, hYsTy, native_ite, native_Teq]
  have hInnerSmtTy :
      __smtx_typeof (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys)) =
        SmtType.RegLan := by
    simpa using hInnerTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt (lhs x ys s)) = SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_inter
          (SmtTerm.str_to_re (__eo_to_smt s))
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys))) =
      SmtType.RegLan
    rw [typeof_re_inter_eq]
    simp [hStrToReSmtTy, hInnerSmtTy, native_ite, native_Teq]
  have hNoneTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    change __smtx_typeof SmtTerm.re_none = SmtType.RegLan
    rw [__smtx_typeof.eq_def] <;> simp only
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs x ys s) rhs
    (by rw [hLhsTy, hNoneTy]) (by rw [hLhsTy]; simp)

private theorem str_in_lhs_false_of_prem
    (M : SmtModel) (s x ys : Term) (ss : SmtSeq)
    (xv ysv : SmtRegLan)
    (hSEval : __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss)
    (hXEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.RegLan xv)
    (hYsEval : __smtx_model_eval M (__eo_to_smt ys) = SmtValue.RegLan ysv)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (prem s x ys) true) :
    native_str_in_re (native_unpack_string ss)
        (native_re_inter (native_str_to_re (native_unpack_string ss))
          (native_re_inter xv ysv)) =
      false := by
  have hUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hPremRel :=
    RuleProofs.eo_interprets_eq_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) (lhs x ys s))
      (Term.Boolean false) hPrem
  have hInEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s)
              (lhs x ys s))) =
        SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter (native_str_to_re (native_unpack_string ss))
              (native_re_inter xv ysv))) := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (__eo_to_smt s)
          (SmtTerm.re_inter
            (SmtTerm.str_to_re (__eo_to_smt s))
            (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys)))) =
      SmtValue.Boolean
        (native_str_in_re (native_unpack_string ss)
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter xv ysv)))
    simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
      __smtx_model_eval_str_to_re, __smtx_model_eval_re_inter, hSEval,
      hXEval, hYsEval, hUnpack]
  have hFalseEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
        SmtValue.Boolean false := by
    change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
    rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hInEval, hFalseEval] at hPremRel
  have hValueEq :
      SmtValue.Boolean
          (native_str_in_re (native_unpack_string ss)
            (native_re_inter (native_str_to_re (native_unpack_string ss))
              (native_re_inter xv ysv))) =
        SmtValue.Boolean false :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, hBad, _⟩
      cases hBad)).1 hPremRel
  injection hValueEq

private theorem smt_value_rel_inter_cstring_neg
    (pat : native_String) (xv ysv : SmtRegLan)
    (hFullFalse :
      RuleProofs.native_str_in_re pat
          (native_re_inter (native_str_to_re pat) (native_re_inter xv ysv)) =
        false) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter (native_str_to_re pat) (native_re_inter xv ysv)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter (native_str_to_re pat) (native_re_inter xv ysv))
        native_re_none) =
    SmtValue.Boolean true
  congr
  simp
  intro str hValid
  simp only [← RuleProofs.native_str_in_re_eq_model]
  rw [RuleProofs.native_str_in_re_re_inter,
    RuleProofs.native_str_in_re_re_none]
  cases hSg : RuleProofs.native_str_in_re str (native_str_to_re pat)
  · simp [hSg]
  · have hStrEq : str = pat :=
      RuleProofs.native_str_in_re_str_to_re_eq hValid hSg
    have hFullAtStr :
        (RuleProofs.native_str_in_re str (native_str_to_re pat) &&
            RuleProofs.native_str_in_re str (native_re_inter xv ysv)) =
          false := by
      simpa [hStrEq, RuleProofs.native_str_in_re_re_inter] using hFullFalse
    rw [hSg] at hFullAtStr
    simp [hSg, hFullAtStr]

private theorem facts
    (M : SmtModel) (hM : model_wf M) (x ys s : Term)
    (hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hYsTy : __smtx_typeof (__eo_to_smt ys) = SmtType.RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hPrem : eo_interprets M (prem s x ys) true) :
    eo_interprets M (concl x ys s) true := by
  have hBool : RuleProofs.eo_has_bool_type (concl x ys s) :=
    typed_concl x ys s hXTy hYsTy hSTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.RegLan := by
    simpa [hXTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXTy]
        simp)
  have hYsEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt ys)) =
        SmtType.RegLan := by
    simpa [hYsTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt ys) (by
        unfold term_has_non_none_type
        rw [hYsTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  rcases reglan_value_canonical hXEvalTy with ⟨xv, hXEval⟩
  rcases reglan_value_canonical hYsEvalTy with ⟨ysv, hYsEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hSEval, __smtx_typeof_value] using hSEvalTy
  have hSUnpack :=
    native_unpack_seq_eq_string_to_values_of_typeof_seq_char hSsTy
  have hFullFalse :
      RuleProofs.native_str_in_re (native_unpack_string ss)
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter xv ysv)) =
        false := by
    rw [RuleProofs.native_str_in_re_eq_model]
    exact str_in_lhs_false_of_prem M s x ys ss xv ysv hSEval hXEval hYsEval
      hSsTy hPrem
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs x ys s)) =
        SmtValue.RegLan
          (native_re_inter (native_str_to_re (native_unpack_string ss))
            (native_re_inter xv ysv)) := by
    change __smtx_model_eval M
        (SmtTerm.re_inter
          (SmtTerm.str_to_re (__eo_to_smt s))
          (SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt ys))) =
      SmtValue.RegLan
        (native_re_inter (native_str_to_re (native_unpack_string ss))
          (native_re_inter xv ysv))
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
      __smtx_model_eval_re_inter, hSEval, hXEval, hYsEval, hSUnpack]
  have hRhsEval :
      __smtx_model_eval M (__eo_to_smt rhs) =
        SmtValue.RegLan native_re_none := by
    change __smtx_model_eval M SmtTerm.re_none = SmtValue.RegLan native_re_none
    rw [__smtx_model_eval.eq_def] <;> simp only
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs x ys s) rhs hBool <| by
    rw [hLhsEval, hRhsEval]
    exact smt_value_rel_inter_cstring_neg
      (native_unpack_string ss) xv ysv hFullFalse

end ReInterCstringNegProof

public theorem cmd_step_re_inter_cstring_neg_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_cstring_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_inter_cstring_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_cstring_neg args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_inter_cstring_neg args premises ≠
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
                  | cons n premises =>
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
                          show StepRuleProperties M [__eo_state_proven_nth s n]
                            (__eo_prog_re_inter_cstring_neg a1 a2 a3
                              (Proof.pf (__eo_state_proven_nth s n)))
                          generalize hP : __eo_state_proven_nth s n = P
                          have hProgNe :
                              __eo_prog_re_inter_cstring_neg a1 a2 a3
                                  (Proof.pf P) ≠
                                Term.Stuck := by
                            rw [← hP]
                            change __eo_cmd_step_proven s CRule.re_inter_cstring_neg
                                (CArgList.cons a1
                                  (CArgList.cons a2
                                    (CArgList.cons a3 CArgList.nil)))
                                (CIndexList.cons n CIndexList.nil) ≠ Term.Stuck
                            exact hProg
                          obtain ⟨hPShape, hProgEq⟩ :=
                            ReInterCstringNegProof.prog_form a1 a2 a3 P hProgNe
                          have hResultTyProg :
                              __eo_typeof
                                  (__eo_prog_re_inter_cstring_neg a1 a2 a3
                                    (Proof.pf P)) = Term.Bool := by
                            rw [← hP]
                            change __eo_typeof
                                (__eo_cmd_step_proven s CRule.re_inter_cstring_neg
                                  (CArgList.cons a1
                                    (CArgList.cons a2
                                      (CArgList.cons a3 CArgList.nil)))
                                  (CIndexList.cons n CIndexList.nil)) =
                              Term.Bool
                            exact hResultTy
                          have hConclTy :
                              __eo_typeof
                                  (ReInterCstringNegProof.concl a1 a2 a3) =
                                Term.Bool := by
                            rw [hProgEq] at hResultTyProg
                            exact hResultTyProg
                          change __eo_typeof_eq
                              (__eo_typeof (ReInterCstringNegProof.lhs a1 a2 a3))
                              (__eo_typeof ReInterCstringNegProof.rhs) =
                            Term.Bool at hConclTy
                          have hLhsNotStuck :
                              __eo_typeof (ReInterCstringNegProof.lhs a1 a2 a3) ≠
                                Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof (ReInterCstringNegProof.lhs a1 a2 a3))
                              (__eo_typeof ReInterCstringNegProof.rhs)
                              hConclTy).1
                          have hOuterArgs :
                              __eo_typeof
                                  (Term.Apply (Term.UOp UserOp.str_to_re) a3) =
                                  Term.UOp UserOp.RegLan ∧
                                __eo_typeof (ReInterCstringNegProof.reInter a1 a2) =
                                  Term.UOp UserOp.RegLan := by
                            change __eo_typeof_re_concat
                                (__eo_typeof
                                  (Term.Apply (Term.UOp UserOp.str_to_re) a3))
                                (__eo_typeof (ReInterCstringNegProof.reInter a1 a2)) ≠
                              Term.Stuck at hLhsNotStuck
                            exact
                              ReInterCstringProof.eo_typeof_re_concat_ne_stuck_args_reglan
                                _ _ hLhsNotStuck
                          have hInnerArgs :
                              __eo_typeof a1 = Term.UOp UserOp.RegLan ∧
                                __eo_typeof a2 = Term.UOp UserOp.RegLan := by
                            have hInnerTy := hOuterArgs.2
                            change __eo_typeof_re_concat (__eo_typeof a1)
                                (__eo_typeof a2) =
                              Term.UOp UserOp.RegLan at hInnerTy
                            exact
                              ReInterCstringProof.eo_typeof_re_concat_eq_reglan_args_reglan
                                _ _ hInnerTy
                          have hA1Ty : __eo_typeof a1 = Term.UOp UserOp.RegLan :=
                            hInnerArgs.1
                          have hA2Ty : __eo_typeof a2 = Term.UOp UserOp.RegLan :=
                            hInnerArgs.2
                          have hA3Ty :
                              __eo_typeof a3 = Term.Apply Term.Seq Term.Char := by
                            have hStrToReTy := hOuterArgs.1
                            change __eo_typeof_str_to_re (__eo_typeof a3) =
                              Term.UOp UserOp.RegLan at hStrToReTy
                            exact
                              ReInterCstringProof.eo_typeof_str_to_re_eq_seq_char_of_reglan
                                (__eo_typeof a3) hStrToReTy
                          have hA1SmtTy :
                              __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a1) =
                                  __eo_to_smt_type (__eo_typeof a1) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a1 hA1Trans
                            rw [hA1Ty] at hTyRaw
                            simpa [TranslationProofs.eo_to_smt_type_reglan] using
                              hTyRaw
                          have hA2SmtTy :
                              __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a2) =
                                  __eo_to_smt_type (__eo_typeof a2) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a2 hA2Trans
                            rw [hA2Ty] at hTyRaw
                            simpa [TranslationProofs.eo_to_smt_type_reglan] using
                              hTyRaw
                          have hA3SmtTy :
                              __smtx_typeof (__eo_to_smt a3) =
                                SmtType.Seq SmtType.Char := by
                            have hTyRaw :
                                __smtx_typeof (__eo_to_smt a3) =
                                  __eo_to_smt_type (__eo_typeof a3) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                a3 hA3Trans
                            rw [hA3Ty] at hTyRaw
                            have hsimpa := hTyRaw
                            try simp [TranslationProofs.eo_to_smt_type_seq, TranslationProofs.eo_to_smt_type_char] at hsimpa ⊢
                            exact hsimpa
                          have hProgBool :
                              RuleProofs.eo_has_bool_type
                                (__eo_prog_re_inter_cstring_neg a1 a2 a3
                                  (Proof.pf P)) := by
                            rw [hProgEq]
                            exact ReInterCstringNegProof.typed_concl a1 a2 a3
                              hA1SmtTy hA2SmtTy hA3SmtTy
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            hProgBool⟩
                          intro hEv
                          have hPrem :
                              eo_interprets M
                                (ReInterCstringNegProof.prem a3 a1 a2) true := by
                            have hHere := hEv.true_here P (by simp)
                            simpa [hPShape] using hHere
                          rw [hProgEq]
                          exact ReInterCstringNegProof.facts M hM a1 a2 a3
                            hA1SmtTy hA2SmtTy hA3SmtTy hPrem
