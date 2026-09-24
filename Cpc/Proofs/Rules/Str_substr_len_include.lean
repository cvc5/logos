module

public import Cpc.Proofs.RuleSupport.StrSubstrContainsSupport
import all Cpc.Proofs.RuleSupport.StrSubstrContainsSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrSubstrContainsSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev substrLenIncludePremise (s n m : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq
      (Term.Apply
        (Term.Apply Term.geq (Term.Apply Term.str_len s))
        (Term.Apply (Term.Apply Term.plus n)
          (Term.Apply (Term.Apply Term.plus m) (Term.Numeral 0)))))
    (Term.Boolean true)

private abbrev substrLenIncludeConcat (s tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat s) tail

private abbrev substrLenIncludeLhs
    (s tail n m : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.str_substr (substrLenIncludeConcat s tail)) n) m

private abbrev substrLenIncludeRhs (s n m : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_substr s) n) m

private abbrev substrLenIncludeConclusion
    (s tail n m : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (substrLenIncludeLhs s tail n m))
    (substrLenIncludeRhs s n m)

private theorem prog_str_substr_len_include_info
    (s tail n m P : Term)
    (hProg :
      __eo_prog_str_substr_len_include s tail n m (Proof.pf P) ≠
        Term.Stuck) :
    ∃ s0 n0 m0,
      P = substrLenIncludePremise s0 n0 m0 ∧
      s0 = s ∧ n0 = n ∧ m0 = m ∧
      __eo_prog_str_substr_len_include s tail n m (Proof.pf P) =
        substrLenIncludeConclusion s tail n m := by
  unfold __eo_prog_str_substr_len_include at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases StrEqReplSupport.eqs_of_requires3_and_eq_true_not_stuck
        hProg with ⟨hS, hN, hM⟩
    subst_vars
    refine ⟨_, _, _, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_substr_len_include, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, substrLenIncludeConclusion,
      substrLenIncludeLhs, substrLenIncludeRhs,
      substrLenIncludeConcat]

private theorem typed___eo_prog_str_substr_len_include_impl
    (s tail n m P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hProgEq :
      __eo_prog_str_substr_len_include s tail n m (Proof.pf P) =
        substrLenIncludeConclusion s tail n m) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_substr_len_include s tail n m (Proof.pf P)) := by
  let lhs := substrLenIncludeLhs s tail n m
  let rhs := substrLenIncludeRhs s n m
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTailSmtTy := smtx_typeof_of_eo_seq tail T hTailTrans hTailTy
  have hNSmtTy := smtx_typeof_of_eo_int n hNTrans hNTy
  have hMSmtTy := smtx_typeof_of_eo_int m hMTrans hMTy
  have hConcatTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt tail)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_concat_eq]
    simp [hSSmtTy, hTailSmtTy, __smtx_typeof_seq_op_2,
      native_ite, native_Teq]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr
          (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt tail))
          (__eo_to_smt n) (__eo_to_smt m)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hConcatTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt m)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_substr_eq]
    simp [hSSmtTy, hNSmtTy, hMSmtTy, __smtx_typeof_str_substr]
  have hBool : RuleProofs.eo_has_bool_type
      (substrLenIncludeConclusion s tail n m) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_substr_len_include_impl
    (M : SmtModel) (hModel : model_wf M)
    (s tail n m P : Term)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hNTrans : RuleProofs.eo_has_smt_translation n)
    (hMTrans : RuleProofs.eo_has_smt_translation m)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq T)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq T)
    (hNTy : __eo_typeof n = Term.Int)
    (hMTy : __eo_typeof m = Term.Int)
    (hPrem : eo_interprets M (substrLenIncludePremise s n m) true)
    (hProgEq :
      __eo_prog_str_substr_len_include s tail n m (Proof.pf P) =
        substrLenIncludeConclusion s tail n m) :
    eo_interprets M
      (__eo_prog_str_substr_len_include s tail n m (Proof.pf P)) true := by
  let lhs := substrLenIncludeLhs s tail n m
  let rhs := substrLenIncludeRhs s n m
  have hBool : RuleProofs.eo_has_bool_type
      (substrLenIncludeConclusion s tail n m) := by
    simpa [hProgEq] using
      typed___eo_prog_str_substr_len_include_impl
        s tail n m P hSTrans hTailTrans hNTrans hMTrans
        hSTy hTailTy hNTy hMTy hProgEq
  have hSSmtTy := smtx_typeof_of_eo_seq s T hSTrans hSTy
  have hTailSmtTy := smtx_typeof_of_eo_seq tail T hTailTrans hTailTy
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
  have hTailEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hTailSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hModel
        (__eo_to_smt tail) (by
          unfold term_has_non_none_type
          rw [hTailSmtTy]
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
  rcases seq_value_canonical hTailEvalTy with ⟨stail, hTailEval⟩
  rcases int_value_canonical hNEvalTy with ⟨ni, hNEval⟩
  rcases int_value_canonical hMEvalTy with ⟨mi, hMEval⟩
  have hBound :
      ni + mi ≤ (native_unpack_seq ss).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.geq
                (SmtTerm.str_len (__eo_to_smt s))
                (SmtTerm.plus (__eo_to_smt n)
                  (SmtTerm.plus (__eo_to_smt m) (SmtTerm.Numeral 0))))
              (SmtTerm.Boolean true)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_geq_term_eq,
          smtx_eval_str_len_term_eq, hSEval, smtx_eval_plus_term_eq,
          hNEval, smtx_eval_plus_term_eq, hMEval,
          smtx_eval_numeral_term_eq, smtx_eval_boolean_term_eq] at hEval
        have hLeBool :
            native_zleq
              (native_zplus ni (native_zplus mi 0))
              (Int.ofNat (native_unpack_seq ss).length) = true := by
          simpa [__smtx_model_eval_geq, __smtx_model_eval_leq,
            __smtx_model_eval_plus, __smtx_model_eval_str_len,
            __smtx_model_eval_eq, native_veq, native_seq_len] using hEval
        have hLe :
            native_zplus ni (native_zplus mi 0) ≤
              Int.ofNat (native_unpack_seq ss).length := by
          simpa [SmtEval.native_zleq] using hLeBool
        simpa [native_zplus, SmtEval.native_zplus] using hLe
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_substr
          (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt tail))
          (__eo_to_smt n) (__eo_to_smt m)) =
      __smtx_model_eval M
        (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n)
          (__eo_to_smt m))
    rw [smtx_eval_str_substr_term_eq, smtx_eval_str_concat_term_eq,
      smtx_eval_str_substr_term_eq, hSEval, hTailEval, hNEval, hMEval]
    simp [__smtx_model_eval_str_substr, __smtx_model_eval_str_concat,
      native_seq_concat, Smtm.native_unpack_pack_seq,
      elem_typeof_pack_seq,
      native_seq_extract_append_left _ _ _ _ hBound]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_substr_len_include_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_len_include args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_substr_len_include args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_len_include args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_substr_len_include args premises ≠
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
                                  (__eo_prog_str_substr_len_include
                                    a1 a2 a3 a4 (Proof.pf P)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_substr_len_include
                                      a1 a2 a3 a4 (Proof.pf P) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_substr_len_include_info
                                  a1 a2 a3 a4 P hRuleProg with
                                ⟨s0, n0, m0, hP, hS0, hN0, hM0, hProgEq⟩
                              subst s0
                              subst n0
                              subst m0
                              rw [hProgEq] at hResultTy
                              have hOpsNN :
                                  __eo_typeof
                                      (substrLenIncludeLhs a1 a2 a3 a4) ≠
                                      Term.Stuck ∧
                                    __eo_typeof
                                      (substrLenIncludeRhs a1 a3 a4) ≠
                                      Term.Stuck := by
                                change __eo_typeof_eq
                                    (__eo_typeof
                                      (substrLenIncludeLhs a1 a2 a3 a4))
                                    (__eo_typeof
                                      (substrLenIncludeRhs a1 a3 a4)) =
                                  Term.Bool at hResultTy
                                exact
                                  RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                    (__eo_typeof
                                      (substrLenIncludeLhs a1 a2 a3 a4))
                                    (__eo_typeof
                                      (substrLenIncludeRhs a1 a3 a4))
                                    hResultTy
                              have hRhsNN := hOpsNN.2
                              change __eo_typeof_str_substr
                                  (__eo_typeof a1) (__eo_typeof a3)
                                  (__eo_typeof a4) ≠ Term.Stuck at hRhsNN
                              rcases eo_typeof_str_substr_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a3)
                                  (__eo_typeof a4) hRhsNN with
                                ⟨T, hA1Ty, hA3Ty, hA4Ty⟩
                              have hLhsNN := hOpsNN.1
                              change __eo_typeof_str_substr
                                  (__eo_typeof
                                    (substrLenIncludeConcat a1 a2))
                                  (__eo_typeof a3) (__eo_typeof a4) ≠
                                Term.Stuck at hLhsNN
                              rcases eo_typeof_str_substr_args_of_ne_stuck
                                  (__eo_typeof
                                    (substrLenIncludeConcat a1 a2))
                                  (__eo_typeof a3) (__eo_typeof a4)
                                  hLhsNN with
                                ⟨U, hConcatTy, _hA3Ty', _hA4Ty'⟩
                              have hConcatNN :
                                  __eo_typeof
                                      (substrLenIncludeConcat a1 a2) ≠
                                    Term.Stuck := by
                                rw [hConcatTy]
                                simp
                              change __eo_typeof_str_concat
                                  (__eo_typeof a1) (__eo_typeof a2) ≠
                                Term.Stuck at hConcatNN
                              rcases eo_typeof_str_concat_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a2)
                                  hConcatNN with
                                ⟨V, hA1Ty', hA2Ty⟩
                              rw [hA1Ty] at hA1Ty'
                              cases hA1Ty'
                              have hConcatCalc :
                                  __eo_typeof
                                      (substrLenIncludeConcat a1 a2) =
                                    Term.Apply Term.Seq T := by
                                change __eo_typeof_str_concat
                                    (__eo_typeof a1) (__eo_typeof a2) =
                                  Term.Apply Term.Seq T
                                rw [hA1Ty, hA2Ty]
                                exact eo_typeof_str_concat_result_of_seq_args
                                  T (by
                                    simpa [hA1Ty, hA2Ty] using hConcatNN)
                              rw [hConcatTy] at hConcatCalc
                              cases hConcatCalc
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPremRaw : eo_interprets M P true :=
                                  hTrue P (by simp [P, premiseTermList])
                                have hPrem :
                                    eo_interprets M
                                      (substrLenIncludePremise a1 a3 a4)
                                      true := by
                                  simpa [hP] using hPremRaw
                                exact
                                  facts___eo_prog_str_substr_len_include_impl
                                    M hM a1 a2 a3 a4 P hA1Trans hA2Trans
                                    hA3Trans hA4Trans hA1Ty hA2Ty hA3Ty
                                    hA4Ty hPrem hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_substr_len_include_impl
                                      a1 a2 a3 a4 P hA1Trans hA2Trans
                                      hA3Trans hA4Trans hA1Ty hA2Ty hA3Ty
                                      hA4Ty hProgEq)
