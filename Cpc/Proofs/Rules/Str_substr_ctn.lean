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

private abbrev substrCtnExtract (s n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m

private abbrev substrCtnLhs (s n m : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains s) (substrCtnExtract s n m)

private abbrev substrCtnConclusion (s n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrCtnLhs s n m))
    (Term.Boolean true)

private theorem prog_str_substr_ctn_eq
    (s n m : Term)
    (hS : s ≠ Term.Stuck) (hN : n ≠ Term.Stuck)
    (hM : m ≠ Term.Stuck) :
    __eo_prog_str_substr_ctn s n m = substrCtnConclusion s n m := by
  unfold __eo_prog_str_substr_ctn
  split
  · contradiction
  · contradiction
  · contradiction
  · rfl

private theorem typed___eo_prog_str_substr_ctn_impl
    (s n m : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_substr_ctn s n m) := by
  let extract := substrCtnExtract s n m
  let lhs := substrCtnLhs s n m
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hExtractTy :
      __smtx_typeof (__eo_to_smt extract) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt m)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr]
  have hExtractTy' :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt m)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [extract, substrCtnExtract, __eo_to_smt, __eo_to_smt_type, __smtx_typeof] using hExtractTy
  have hLhsTy : RuleProofs.eo_has_bool_type lhs := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt s)
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt m))) = SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hSSmtTy, hExtractTy', __smtx_typeof_seq_op_2_ret,
      native_ite, native_Teq]
  have hTrueTy : RuleProofs.eo_has_bool_type (Term.Boolean true) := by
    rfl
  have hBool : RuleProofs.eo_has_bool_type
      (substrCtnConclusion s n m) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs
      (Term.Boolean true) (by rw [hLhsTy, hTrueTy])
      (by rw [hLhsTy]; simp)
  have hSNN := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hNNN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hMNN := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  rw [prog_str_substr_ctn_eq s n m hSNN hNNN hMNN]
  exact hBool

private theorem facts___eo_prog_str_substr_ctn_impl
    (M : SmtModel) (hModel : model_wf M)
    (s n m : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int) :
    eo_interprets M (__eo_prog_str_substr_ctn s n m) true := by
  let lhs := substrCtnLhs s n m
  have hSNN := RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hNNN := RuleProofs.term_ne_stuck_of_has_smt_translation n hNTrans
  have hMNN := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hProgEq := prog_str_substr_ctn_eq s n m hSNN hNNN hMNN
  have hBool : RuleProofs.eo_has_bool_type
      (substrCtnConclusion s n m) := by
    simpa [hProgEq] using
      typed___eo_prog_str_substr_ctn_impl s n m hSTrans hNTrans hMTrans
        hSTy hNTy hMTy
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
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
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (SmtTerm.Boolean true) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt s)
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
            (__eo_to_smt m))) =
      __smtx_model_eval M (SmtTerm.Boolean true)
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_substr_term_eq,
      hSEval, hNEval, hMEval, smtx_eval_boolean_term_eq]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_substr,
      Smtm.native_unpack_pack_seq, native_seq_contains_extract]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs (Term.Boolean true)
    hBool <| by
      rw [hEvalEq]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (SmtTerm.Boolean true))

public theorem cmd_step_str_substr_ctn_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_ctn args premises ≠
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
              | cons _ _ => exact absurd rfl hProg
              | nil =>
                  cases premises with
                  | cons _ _ => exact absurd rfl hProg
                  | nil =>
                      have hA1Trans :
                          RuleProofs.eo_has_smt_translation a1 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk]
                          using hCmdTrans.1
                      have hA2Trans :
                          RuleProofs.eo_has_smt_translation a2 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk]
                          using hCmdTrans.2.1
                      have hA3Trans :
                          RuleProofs.eo_has_smt_translation a3 := by
                        simpa [cmdTranslationOk, cArgListTranslationOk]
                          using hCmdTrans.2.2.1
                      have hA1NN :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation
                          a1 hA1Trans
                      have hA2NN :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation
                          a2 hA2Trans
                      have hA3NN :=
                        RuleProofs.term_ne_stuck_of_has_smt_translation
                          a3 hA3Trans
                      change __eo_typeof
                          (__eo_prog_str_substr_ctn a1 a2 a3) =
                        Term.Bool at hResultTy
                      have hProgEq :=
                        prog_str_substr_ctn_eq
                          a1 a2 a3 hA1NN hA2NN hA3NN
                      rw [hProgEq] at hResultTy
                      have hLhsNN :
                          __eo_typeof (substrCtnLhs a1 a2 a3) ≠
                            Term.Stuck := by
                        change __eo_typeof_eq
                            (__eo_typeof (substrCtnLhs a1 a2 a3))
                            Term.Bool = Term.Bool at hResultTy
                        exact
                          (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                            (__eo_typeof (substrCtnLhs a1 a2 a3))
                            Term.Bool hResultTy).1
                      change __eo_typeof_str_contains
                          (__eo_typeof a1)
                          (__eo_typeof (substrCtnExtract a1 a2 a3)) ≠
                        Term.Stuck at hLhsNN
                      rcases eo_typeof_str_contains_args_of_ne_stuck
                          (__eo_typeof a1)
                          (__eo_typeof (substrCtnExtract a1 a2 a3))
                          hLhsNN with
                        ⟨T, hA1Ty, hExtractTy⟩
                      have hExtractNN :
                          __eo_typeof (substrCtnExtract a1 a2 a3) ≠
                            Term.Stuck := by
                        rw [hExtractTy]
                        simp
                      change __eo_typeof_str_substr
                          (__eo_typeof a1) (__eo_typeof a2)
                          (__eo_typeof a3) ≠ Term.Stuck at hExtractNN
                      rcases eo_typeof_str_substr_args_of_ne_stuck
                          (__eo_typeof a1) (__eo_typeof a2)
                          (__eo_typeof a3) hExtractNN with
                        ⟨U, hA1Ty', hA2Ty, hA3Ty⟩
                      rw [hA1Ty] at hA1Ty'
                      cases hA1Ty'
                      refine ⟨?_, ?_⟩
                      · intro _hTrue
                        exact facts___eo_prog_str_substr_ctn_impl
                          M hM a1 a2 a3 hA1Trans hA2Trans hA3Trans
                          hA1Ty hA2Ty hA3Ty
                      · exact
                          RuleProofs.eo_has_smt_translation_of_has_bool_type _
                            (typed___eo_prog_str_substr_ctn_impl
                              a1 a2 a3 hA1Trans hA2Trans hA3Trans
                              hA1Ty hA2Ty hA3Ty)
