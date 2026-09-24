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

private abbrev substrCtnContraPremise (t s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains t) s))
    (Term.Boolean false)

private abbrev substrCtnContraExtract (t n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr t) n) m

private abbrev substrCtnContraLhs (t s n m : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains
    (substrCtnContraExtract t n m)) s

private abbrev substrCtnContraConclusion (t s n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrCtnContraLhs t s n m))
    (Term.Boolean false)

private theorem prog_str_substr_ctn_contra_info
    (t s n m P : Term)
    (hProg :
      __eo_prog_str_substr_ctn_contra t s n m (Proof.pf P) ≠
        Term.Stuck) :
    ∃ t0 s0,
      P = substrCtnContraPremise t0 s0 ∧ t0 = t ∧ s0 = s ∧
      __eo_prog_str_substr_ctn_contra t s n m (Proof.pf P) =
        substrCtnContraConclusion t s n m := by
  unfold __eo_prog_str_substr_ctn_contra at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hT, hS⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_ctn_contra, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, substrCtnContraConclusion,
      substrCtnContraLhs, substrCtnContraExtract]

private theorem typed___eo_prog_str_substr_ctn_contra_impl
    (t s n m P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_ctn_contra t s n m (Proof.pf P) =
        substrCtnContraConclusion t s n m) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_ctn_contra t s n m (Proof.pf P)) := by
  let extract := substrCtnContraExtract t n m
  let lhs := substrCtnContraLhs t s n m
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hExtractTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
            (__eo_to_smt m)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_substr_eq]
    simp [hTSmtTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr]
  have hLhsTy : RuleProofs.eo_has_bool_type lhs := by
    change __smtx_typeof
        (SmtTerm.str_contains
          (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
            (__eo_to_smt m))
          (__eo_to_smt s)) = SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hExtractTy, hSSmtTy, __smtx_typeof_seq_op_2_ret,
      native_ite, native_Teq]
  have hFalseTy : RuleProofs.eo_has_bool_type (Term.Boolean false) := by
    rfl
  have hBool : RuleProofs.eo_has_bool_type
      (substrCtnContraConclusion t s n m) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs
      (Term.Boolean false) (by rw [hLhsTy, hFalseTy])
      (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_substr_ctn_contra_impl
    (M : SmtModel) (hModel : model_wf M)
    (t s n m P : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq T)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hPrem : eo_interprets M (substrCtnContraPremise t s) true)
    (hProgEq :
      __eo_prog_str_substr_ctn_contra t s n m (Proof.pf P) =
        substrCtnContraConclusion t s n m) :
    eo_interprets M
      (__eo_prog_str_substr_ctn_contra t s n m (Proof.pf P)) true := by
  let lhs := substrCtnContraLhs t s n m
  have hBool : RuleProofs.eo_has_bool_type
      (substrCtnContraConclusion t s n m) := by
    simpa [hProgEq] using
      typed___eo_prog_str_substr_ctn_contra_impl
        t s n m P hTTrans hSTrans hNTrans hMTrans
        hTTy hSTy hNTy hMTy hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq t T hTTrans hTTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  have hNEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        SmtType.Int := by
    simpa [hNSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel (__eo_to_smt n) (by
        unfold term_has_non_none_type
        rw [hNSmtTy]
        simp)
  have hMEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
        SmtType.Int := by
    simpa [hMSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel (__eo_to_smt m) (by
        unfold term_has_non_none_type
        rw [hMSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hAbsent :
      native_seq_contains (native_unpack_seq st) (native_unpack_seq ss) =
        false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt t) (__eo_to_smt s))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hTEval, hSEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (SmtTerm.Boolean false) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_substr (__eo_to_smt t) (__eo_to_smt n)
            (__eo_to_smt m))
          (__eo_to_smt s)) =
      __smtx_model_eval M (SmtTerm.Boolean false)
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_substr_term_eq,
      hTEval, hSEval, hNEval, hMEval, smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_substr,
      Smtm.native_unpack_pack_seq,
      native_seq_contains_extract_target_false _ _ _ _ hAbsent]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs (Term.Boolean false)
    hBool <| by
      rw [hEvalEq]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (SmtTerm.Boolean false))

public theorem cmd_step_str_substr_ctn_contra_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_ctn_contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_ctn_contra args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_ctn_contra args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_ctn_contra args premises ≠
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
                      | cons p premises =>
                          cases premises with
                          | cons _ _ => exact absurd rfl hProg
                          | nil =>
                              let P := __eo_state_proven_nth s p
                              have hA1Trans :
                                  RuleProofs.eo_has_smt_translation a1 := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.1
                              have hA2Trans :
                                  RuleProofs.eo_has_smt_translation a2 := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using hCmdTrans.2.1
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
                                  (__eo_prog_str_substr_ctn_contra
                                    a1 a2 a3 a4 (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_substr_ctn_contra
                                      a1 a2 a3 a4 (Proof.pf P) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_substr_ctn_contra_info
                                  a1 a2 a3 a4 P hRuleProg with
                                ⟨t0, s0, hP, hT0, hS0, hProgEq⟩
                              subst t0
                              subst s0
                              rw [hProgEq] at hResultTy
                              have hLhsNN :
                                  __eo_typeof
                                      (substrCtnContraLhs a1 a2 a3 a4) ≠
                                    Term.Stuck := by
                                change __eo_typeof_eq
                                    (__eo_typeof
                                      (substrCtnContraLhs a1 a2 a3 a4))
                                    Term.Bool = Term.Bool at hResultTy
                                exact
                                  (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                    (__eo_typeof
                                      (substrCtnContraLhs a1 a2 a3 a4))
                                    Term.Bool hResultTy).1
                              change __eo_typeof_str_contains
                                  (__eo_typeof
                                    (substrCtnContraExtract a1 a3 a4))
                                  (__eo_typeof a2) ≠ Term.Stuck at hLhsNN
                              rcases eo_typeof_str_contains_args_of_ne_stuck
                                  (__eo_typeof
                                    (substrCtnContraExtract a1 a3 a4))
                                  (__eo_typeof a2) hLhsNN with
                                ⟨T, hExtractTy, hA2Ty⟩
                              have hExtractNN :
                                  __eo_typeof
                                      (substrCtnContraExtract a1 a3 a4) ≠
                                    Term.Stuck := by
                                rw [hExtractTy]
                                simp
                              change __eo_typeof_str_substr
                                  (__eo_typeof a1) (__eo_typeof a3)
                                  (__eo_typeof a4) ≠ Term.Stuck at hExtractNN
                              rcases eo_typeof_str_substr_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a3)
                                  (__eo_typeof a4) hExtractNN with
                                ⟨U, hA1Ty, hA3Ty, hA4Ty⟩
                              have hExtractCalc :
                                  __eo_typeof
                                      (substrCtnContraExtract a1 a3 a4) =
                                    Term.Apply Term.Seq U := by
                                change __eo_typeof_str_substr
                                    (__eo_typeof a1) (__eo_typeof a3)
                                    (__eo_typeof a4) =
                                  Term.Apply Term.Seq U
                                rw [hA1Ty, hA3Ty, hA4Ty]
                                exact eo_typeof_str_substr_result_of_seq_args
                                  U (by
                                    simpa [hA1Ty, hA3Ty, hA4Ty] using
                                      hExtractNN)
                              rw [hExtractTy] at hExtractCalc
                              cases hExtractCalc
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M
                                      (substrCtnContraPremise a1 a2) true := by
                                  simpa [hP] using hPremRaw
                                exact
                                  facts___eo_prog_str_substr_ctn_contra_impl
                                    M hM a1 a2 a3 a4 P hA1Trans hA2Trans
                                    hA3Trans hA4Trans hA1Ty hA2Ty hA3Ty
                                    hA4Ty hPrem hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_substr_ctn_contra_impl
                                      a1 a2 a3 a4 P hA1Trans hA2Trans
                                      hA3Trans hA4Trans hA1Ty hA2Ty hA3Ty
                                      hA4Ty hProgEq)
