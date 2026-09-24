module

public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport
open StrSubstrContainsSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev substrReplaceLenPremise (t r : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len t))
    (Term.Apply Term.str_len r)

private abbrev substrReplaceOnePremise (t : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len t))
    (Term.Numeral 1)

private abbrev substrReplaceValue (s t r : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace s) t) r

private abbrev substrReplaceExtract (s n : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) (Term.Numeral 0)) n

private abbrev substrReplaceLhs (s t r n : Term) : Term :=
  substrReplaceExtract (substrReplaceValue s t r) n

private abbrev substrReplaceRhs (s t r n : Term) : Term :=
  substrReplaceValue (substrReplaceExtract s n) t r

private abbrev substrReplaceConclusion (s t r n : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrReplaceLhs s t r n))
    (substrReplaceRhs s t r n)

private theorem prog_str_substr_replace_info
    (s t r n P1 P2 : Term)
    (hProg :
      __eo_prog_str_substr_replace s t r n
          (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck) :
    ∃ t0 r0 t1,
      P1 = substrReplaceLenPremise t0 r0 ∧
      P2 = substrReplaceOnePremise t1 ∧
      t0 = t ∧ r0 = r ∧ t1 = t ∧
      __eo_prog_str_substr_replace s t r n
          (Proof.pf P1) (Proof.pf P2) =
        substrReplaceConclusion s t r n := by
  unfold __eo_prog_str_substr_replace at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases eqs_of_requires3_and_eq_true_not_stuck hProg with
      ⟨hT0, hR0, hT1⟩
    subst_vars
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_replace, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, substrReplaceConclusion, substrReplaceLhs,
      substrReplaceRhs, substrReplaceValue, substrReplaceExtract]

private theorem typed___eo_prog_str_substr_replace_impl
    (s t r n P1 P2 : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_replace s t r n
          (Proof.pf P1) (Proof.pf P2) =
        substrReplaceConclusion s t r n) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_replace s t r n
        (Proof.pf P1) (Proof.pf P2)) := by
  let value := substrReplaceValue s t r
  let extracted := substrReplaceExtract s n
  let lhs := substrReplaceLhs s t r n
  let rhs := substrReplaceRhs s t r n
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
          (__eo_to_smt r)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hSSmtTy, hTSmtTy, hRSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hExtractedTy :
      __smtx_typeof (__eo_to_smt extracted) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
          (__eo_to_smt n)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, __smtx_typeof_str_substr,
      __smtx_typeof.eq_def]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
            (__eo_to_smt r))
          (SmtTerm.Numeral 0) (__eo_to_smt n)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    rw [show
        __smtx_typeof
            (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
              (__eo_to_smt r)) =
          SmtType.Seq (__eo_to_smt_type T) by
      simpa [value, __eo_to_smt, __eo_to_smt_type, __smtx_typeof, substrReplaceValue] using hValueTy]
    simp [hNSmtTy, __smtx_typeof_str_substr, __smtx_typeof.eq_def]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace
          (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
            (__eo_to_smt n))
          (__eo_to_smt t) (__eo_to_smt r)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    rw [show
        __smtx_typeof
            (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
              (__eo_to_smt n)) =
          SmtType.Seq (__eo_to_smt_type T) by
      simpa [extracted, __eo_to_smt, __eo_to_smt_type, __smtx_typeof, substrReplaceExtract] using hExtractedTy]
    simp [hTSmtTy, hRSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (substrReplaceConclusion s t r n) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_substr_replace_impl
    (M : SmtModel) (hM : model_wf M)
    (s t r n P1 P2 : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hRTy : __eo_typeof r = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hPrem1 : eo_interprets M (substrReplaceLenPremise t r) true)
    (hPrem2 : eo_interprets M (substrReplaceOnePremise t) true)
    (hProgEq :
      __eo_prog_str_substr_replace s t r n
          (Proof.pf P1) (Proof.pf P2) =
        substrReplaceConclusion s t r n) :
    eo_interprets M
      (__eo_prog_str_substr_replace s t r n
        (Proof.pf P1) (Proof.pf P2)) true := by
  let lhs := substrReplaceLhs s t r n
  let rhs := substrReplaceRhs s t r n
  have hBool : RuleProofs.eo_has_bool_type
      (substrReplaceConclusion s t r n) := by
    simpa [hProgEq] using
      typed___eo_prog_str_substr_replace_impl
        s t r n P1 P2 hSTrans hTTrans hRTrans hNTrans
        hSTy hTTy hRTy hNTy hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hRSmtTy := smtx_typeof_of_eo_seq r T hRTrans hRTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases seq_value_canonical hTEvalTy with ⟨ts, hTEval⟩
  rcases seq_value_canonical hREvalTy with ⟨rs, hREval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  have hLenEq :
      (native_unpack_seq ts).length = (native_unpack_seq rs).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.str_len (__eo_to_smt r))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
          smtx_eval_str_len_term_eq, hTEval, hREval] at hEval
        have hLenInt :
            Int.ofNat (native_unpack_seq ts).length =
              Int.ofNat (native_unpack_seq rs).length := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        exact Int.ofNat.inj hLenInt
  have hTLen : (native_unpack_seq ts).length = 1 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.Numeral 1)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hTEval,
          smtx_eval_numeral_term_eq] at hEval
        have hLenInt :
            (Int.ofNat (native_unpack_seq ts).length : Int) = 1 := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        change Int.ofNat (native_unpack_seq ts).length = Int.ofNat 1 at hLenInt
        exact Int.ofNat.inj hLenInt
  have hRLen : (native_unpack_seq rs).length = 1 := by
    rw [← hLenEq]
    exact hTLen
  have hSSeqTy :
      __smtx_typeof_seq_value ss = SmtType.Seq (__eo_to_smt_type T) := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hSElem : __smtx_elem_typeof_seq_value ss = __eo_to_smt_type T :=
    elem_typeof_seq_value_of_typeof_seq_value hSSeqTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t)
            (__eo_to_smt r))
          (SmtTerm.Numeral 0) (__eo_to_smt n)) =
      __smtx_model_eval M
        (SmtTerm.str_replace
          (SmtTerm.str_substr (__eo_to_smt s) (SmtTerm.Numeral 0)
            (__eo_to_smt n))
          (__eo_to_smt t) (__eo_to_smt r))
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_str_replace_term_eq, smtx_eval_str_substr_term_eq,
      hSEval, hTEval, hREval, hNEval, smtx_eval_numeral_term_eq]
    simp [__smtx_model_eval_str_substr, __smtx_model_eval_str_replace,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq, hSElem,
      native_seq_extract_replace_of_length_one _ _ _ _ hTLen hRLen]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_replace_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_replace args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_replace args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_replace args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_replace args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | nil => exact absurd rfl hProg
      | cons a2 args =>
          cases args with
          | nil => exact absurd rfl hProg
          | cons a3 args =>
              cases args with
              | nil => exact absurd rfl hProg
              | cons a4 args =>
                  cases args with
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      cases premises with
                      | nil => exact absurd rfl hProg
                      | cons n1 premises =>
                          cases premises with
                          | nil => exact absurd rfl hProg
                          | cons n2 premises =>
                              cases premises with
                              | cons _ _ => exact absurd rfl hProg
                              | nil =>
                                  let P1 := __eo_state_proven_nth s n1
                                  let P2 := __eo_state_proven_nth s n2
                                  have hA1Trans :
                                      RuleProofs.eo_has_smt_translation a1 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using hCmdTrans.1
                                  have hA2Trans :
                                      RuleProofs.eo_has_smt_translation a2 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.1
                                  have hA3Trans :
                                      RuleProofs.eo_has_smt_translation a3 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.2.1
                                  have hA4Trans :
                                      RuleProofs.eo_has_smt_translation a4 := by
                                    simpa [cmdTranslationOk,
                                      cArgListTranslationOk] using
                                        hCmdTrans.2.2.2.1
                                  change __eo_typeof
                                      (__eo_prog_str_substr_replace
                                        a1 a2 a3 a4 (Proof.pf P1)
                                        (Proof.pf P2)) =
                                    Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_substr_replace
                                          a1 a2 a3 a4 (Proof.pf P1)
                                          (Proof.pf P2) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_substr_replace_info
                                      a1 a2 a3 a4 P1 P2 hRuleProg with
                                    ⟨t0, r0, t1, hP1, hP2, hT0, hR0,
                                      hT1, hProgEq⟩
                                  subst t0
                                  subst r0
                                  subst t1
                                  rw [hProgEq] at hResultTy
                                  have hLhsNN :
                                      __eo_typeof
                                          (substrReplaceLhs
                                            a1 a2 a3 a4) ≠
                                        Term.Stuck := by
                                    change __eo_typeof_eq
                                        (__eo_typeof
                                          (substrReplaceLhs
                                            a1 a2 a3 a4))
                                        (__eo_typeof
                                          (substrReplaceRhs
                                            a1 a2 a3 a4)) =
                                      Term.Bool at hResultTy
                                    exact
                                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                        (__eo_typeof
                                          (substrReplaceLhs
                                            a1 a2 a3 a4))
                                        (__eo_typeof
                                          (substrReplaceRhs
                                            a1 a2 a3 a4)) hResultTy).1
                                  have hArgTypes :
                                      ∃ T,
                                        __eo_typeof a1 =
                                            Term.Apply Term.Seq T ∧
                                          __eo_typeof a2 =
                                            Term.Apply Term.Seq T ∧
                                          __eo_typeof a3 =
                                            Term.Apply Term.Seq T ∧
                                          __eo_typeof a4 = Term.Int := by
                                    change __eo_typeof_str_substr
                                        (__eo_typeof
                                          (substrReplaceValue a1 a2 a3))
                                        (__eo_typeof (Term.Numeral 0))
                                        (__eo_typeof a4) ≠
                                      Term.Stuck at hLhsNN
                                    rcases eo_typeof_str_substr_args_of_ne_stuck
                                        (__eo_typeof
                                          (substrReplaceValue a1 a2 a3))
                                        (__eo_typeof (Term.Numeral 0))
                                        (__eo_typeof a4) hLhsNN with
                                      ⟨T, hValueTy, _hZeroTy, hA4Ty⟩
                                    have hValueNN :
                                        __eo_typeof
                                            (substrReplaceValue a1 a2 a3) ≠
                                          Term.Stuck := by
                                      rw [hValueTy]
                                      simp
                                    change __eo_typeof_str_replace
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) ≠
                                      Term.Stuck at hValueNN
                                    rcases eo_typeof_str_replace_args_of_ne_stuck
                                        (__eo_typeof a1) (__eo_typeof a2)
                                        (__eo_typeof a3) hValueNN with
                                      ⟨U, hA1Ty, hA2Ty, hA3Ty⟩
                                    have hValueTyU :
                                        __eo_typeof
                                            (substrReplaceValue a1 a2 a3) =
                                          Term.Apply Term.Seq U := by
                                      change __eo_typeof_str_replace
                                          (__eo_typeof a1) (__eo_typeof a2)
                                          (__eo_typeof a3) =
                                        Term.Apply Term.Seq U
                                      have hRawNN := hValueNN
                                      rw [hA1Ty, hA2Ty, hA3Ty] at hRawNN
                                      rw [hA1Ty, hA2Ty, hA3Ty]
                                      exact
                                        eo_typeof_str_replace_result_of_seq_args
                                          U hRawNN
                                    rw [hValueTy] at hValueTyU
                                    cases hValueTyU
                                    exact ⟨T, hA1Ty, hA2Ty, hA3Ty,
                                      hA4Ty⟩
                                  rcases hArgTypes with
                                    ⟨T, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPrem1Raw : eo_interprets M P1 true :=
                                      hTrue P1 (by
                                        simp [P1, premiseTermList])
                                    have hPrem2Raw : eo_interprets M P2 true :=
                                      hTrue P2 (by
                                        simp [P2, premiseTermList])
                                    have hPrem1 :
                                        eo_interprets M
                                          (substrReplaceLenPremise a2 a3)
                                          true := by
                                      simpa [hP1] using hPrem1Raw
                                    have hPrem2 :
                                        eo_interprets M
                                          (substrReplaceOnePremise a2)
                                          true := by
                                      simpa [hP2] using hPrem2Raw
                                    exact
                                      facts___eo_prog_str_substr_replace_impl
                                        M hM a1 a2 a3 a4 P1 P2 hA1Trans
                                        hA2Trans hA3Trans hA4Trans hA1Ty
                                        hA2Ty hA3Ty hA4Ty hPrem1 hPrem2
                                        hProgEq
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (typed___eo_prog_str_substr_replace_impl
                                          a1 a2 a3 a4 P1 P2 hA1Trans
                                          hA2Trans hA3Trans hA4Trans hA1Ty
                                          hA2Ty hA3Ty hA4Ty hProgEq)
