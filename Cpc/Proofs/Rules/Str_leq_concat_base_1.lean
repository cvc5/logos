module

public import Cpc.Proofs.RuleSupport.StrLeqConcatSupport
import all Cpc.Proofs.RuleSupport.StrLeqConcatSupport

open Eo
open SmtEval
open Smtm
open StrLeqConcatSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev leqBase1LenPremise (t s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len t))
    (Term.Apply Term.str_len s)

private abbrev leqBase1NePremise (t s : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s))
    (Term.Boolean false)

private abbrev leqBase1Concat (t tail : Term) : Term :=
  Term.Apply (Term.Apply Term.str_concat t) tail

private abbrev leqBase1Lhs (t tail s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_leq (leqBase1Concat t tail)) s

private abbrev leqBase1Rhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_leq t) s

private abbrev leqBase1Conclusion (t tail s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (leqBase1Lhs t tail s))
    (leqBase1Rhs t s)

private theorem prog_str_leq_concat_base_1_info
    (t tail s P1 P2 : Term)
    (hProg :
      __eo_prog_str_leq_concat_base_1 t tail s
          (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck) :
    ∃ t0 s0 t1 s1,
      P1 = leqBase1LenPremise t0 s0 ∧
      P2 = leqBase1NePremise t1 s1 ∧
      t0 = t ∧ s0 = s ∧ t1 = t ∧ s1 = s ∧
      __eo_prog_str_leq_concat_base_1 t tail s
          (Proof.pf P1) (Proof.pf P2) =
        leqBase1Conclusion t tail s := by
  unfold __eo_prog_str_leq_concat_base_1 at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases eqs_of_requires4_and_eq_true_not_stuck _ _ _ _ _ _ _ _ _
        hProg with ⟨hT0, hS0, hT1, hS1⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_leq_concat_base_1, __eo_requires, __eo_eq,
      __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, leqBase1Conclusion, leqBase1Lhs,
      leqBase1Rhs, leqBase1Concat]

private theorem typed___eo_prog_str_leq_concat_base_1_impl
    (t tail s P1 P2 : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq Term.Char)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (hProgEq :
      __eo_prog_str_leq_concat_base_1 t tail s
          (Proof.pf P1) (Proof.pf P2) =
        leqBase1Conclusion t tail s) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_leq_concat_base_1 t tail s
        (Proof.pf P1) (Proof.pf P2)) := by
  let lhs := leqBase1Lhs t tail s
  let rhs := leqBase1Rhs t s
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hTailSmtTy :=
    smtx_typeof_of_eo_seq_char tail hTailTrans hTailTy
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  have hConcatTy :
      __smtx_typeof
          (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt tail)) =
        SmtType.Seq SmtType.Char := by
    rw [typeof_str_concat_eq]
    simp [hTSmtTy, hTailSmtTy, __smtx_typeof_seq_op_2, native_ite,
      native_Teq]
  have hLhsTy : RuleProofs.eo_has_bool_type lhs := by
    change __smtx_typeof
        (SmtTerm.str_leq
          (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt tail))
          (__eo_to_smt s)) = SmtType.Bool
    rw [typeof_str_leq_eq]
    simp [hConcatTy, hSSmtTy, native_ite, native_Teq]
  have hRhsTy : RuleProofs.eo_has_bool_type rhs := by
    change __smtx_typeof
        (SmtTerm.str_leq (__eo_to_smt t) (__eo_to_smt s)) =
      SmtType.Bool
    rw [typeof_str_leq_eq]
    simp [hTSmtTy, hSSmtTy, native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (leqBase1Conclusion t tail s) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_leq_concat_base_1_impl
    (M : SmtModel) (hM : model_wf M)
    (t tail s P1 P2 : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hTailTrans : RuleProofs.eo_has_smt_translation tail)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTTy : __eo_typeof t = Term.Apply Term.Seq Term.Char)
    (hTailTy : __eo_typeof tail = Term.Apply Term.Seq Term.Char)
    (hSTy : __eo_typeof s = Term.Apply Term.Seq Term.Char)
    (hPrem1 : eo_interprets M (leqBase1LenPremise t s) true)
    (hPrem2 : eo_interprets M (leqBase1NePremise t s) true)
    (hProgEq :
      __eo_prog_str_leq_concat_base_1 t tail s
          (Proof.pf P1) (Proof.pf P2) =
        leqBase1Conclusion t tail s) :
    eo_interprets M
      (__eo_prog_str_leq_concat_base_1 t tail s
        (Proof.pf P1) (Proof.pf P2)) true := by
  let lhs := leqBase1Lhs t tail s
  let rhs := leqBase1Rhs t s
  have hBool : RuleProofs.eo_has_bool_type
      (leqBase1Conclusion t tail s) := by
    simpa [hProgEq] using
      typed___eo_prog_str_leq_concat_base_1_impl
        t tail s P1 P2 hTTrans hTailTrans hSTrans
        hTTy hTailTy hSTy hProgEq
  have hTSmtTy := smtx_typeof_of_eo_seq_char t hTTrans hTTy
  have hTailSmtTy :=
    smtx_typeof_of_eo_seq_char tail hTailTrans hTailTy
  have hSSmtTy := smtx_typeof_of_eo_seq_char s hSTrans hSTy
  have hTEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTSmtTy]
        simp)
  have hTailEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt tail)) =
        SmtType.Seq SmtType.Char := by
    simpa [hTailSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt tail) (by
        unfold term_has_non_none_type
        rw [hTailSmtTy]
        simp)
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSSmtTy]
        simp)
  rcases seq_value_canonical hTEvalTy with ⟨st, hTEval⟩
  rcases seq_value_canonical hTailEvalTy with ⟨stail, hTailEval⟩
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  have hStTy :
      __smtx_typeof_seq_value st = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hTEval] using hTEvalTy
  have hStailTy :
      __smtx_typeof_seq_value stail = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hTailEval] using hTailEvalTy
  have hSsTy :
      __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [__smtx_typeof_value, hSEval] using hSEvalTy
  have hLen :
      (native_unpack_string st).length =
        (native_unpack_string ss).length := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem1
    cases hPrem1 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt t))
              (SmtTerm.str_len (__eo_to_smt s))) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq,
          smtx_eval_str_len_term_eq, hTEval, hSEval] at hEval
        have hLenInt :
            ((native_unpack_seq st).length : Int) =
              ((native_unpack_seq ss).length : Int) := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_seq_len, native_veq] using hEval
        have hListLen :
            (native_unpack_seq st).length =
              (native_unpack_seq ss).length :=
          Int.ofNat_inj.mp hLenInt
        simpa [native_unpack_string] using hListLen
  have hSeqNe : st ≠ ss := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem2
    cases hPrem2 with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt s))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_eq_term_eq, hTEval, hSEval,
          smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_eq, native_veq] using hEval
  have hTPack : native_pack_string (native_unpack_string st) = st :=
    native_pack_string_unpack_string_of_typeof_seq_char st hStTy
  have hTailPack :
      native_pack_string (native_unpack_string stail) = stail :=
    native_pack_string_unpack_string_of_typeof_seq_char stail hStailTy
  have hSPack : native_pack_string (native_unpack_string ss) = ss :=
    native_pack_string_unpack_string_of_typeof_seq_char ss hSsTy
  have hStringNe : native_unpack_string st ≠ native_unpack_string ss := by
    intro hEq
    apply hSeqNe
    rw [← hTPack, ← hSPack, hEq]
  have hConcatPack :
      native_pack_seq (__smtx_elem_typeof_seq_value st)
          (native_unpack_seq st ++ native_unpack_seq stail) =
        native_pack_string
          (native_unpack_string st ++ native_unpack_string stail) :=
    native_pack_seq_concat_eq_pack_string_append st stail hStTy hStailTy
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_leq
          (SmtTerm.str_concat (__eo_to_smt t) (__eo_to_smt tail))
          (__eo_to_smt s)) =
      __smtx_model_eval M
        (SmtTerm.str_leq (__eo_to_smt t) (__eo_to_smt s))
    rw [smtx_eval_str_leq_term_eq, smtx_eval_str_concat_term_eq,
      smtx_eval_str_leq_term_eq, hTEval, hTailEval, hSEval]
    change __smtx_model_eval_str_leq
        (SmtValue.Seq
          (native_pack_seq (__smtx_elem_typeof_seq_value st)
            (native_unpack_seq st ++ native_unpack_seq stail)))
        (SmtValue.Seq ss) =
      __smtx_model_eval_str_leq (SmtValue.Seq st) (SmtValue.Seq ss)
    rw [hConcatPack, ← hTPack, ← hSPack,
      smtx_eval_str_leq_pack_string, smtx_eval_str_leq_pack_string]
    simp only [native_unpack_string_pack_string]
    congr 1
    exact native_str_leq_bool_append_left_of_same_len_ne
      _ _ _ hLen hStringNe
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_leq_concat_base_1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_concat_base_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_leq_concat_base_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_concat_base_1 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_leq_concat_base_1 args premises ≠
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
                                  cArgListTranslationOk] using hCmdTrans.2.1
                              have hA3Trans :
                                  RuleProofs.eo_has_smt_translation a3 := by
                                simpa [cmdTranslationOk,
                                  cArgListTranslationOk] using
                                    hCmdTrans.2.2.1
                              change __eo_typeof
                                  (__eo_prog_str_leq_concat_base_1
                                    a1 a2 a3 (Proof.pf P1) (Proof.pf P2)) =
                                Term.Bool at hResultTy
                              have hRuleProg :
                                  __eo_prog_str_leq_concat_base_1
                                      a1 a2 a3 (Proof.pf P1) (Proof.pf P2) ≠
                                    Term.Stuck :=
                                term_ne_stuck_of_typeof_bool hResultTy
                              rcases prog_str_leq_concat_base_1_info
                                  a1 a2 a3 P1 P2 hRuleProg with
                                ⟨t0, s0, t1, s1, hP1, hP2, hT0, hS0,
                                  hT1, hS1, hProgEq⟩
                              subst t0
                              subst s0
                              subst t1
                              subst s1
                              rw [hProgEq] at hResultTy
                              have hOpsNN :
                                  __eo_typeof (leqBase1Lhs a1 a2 a3) ≠
                                      Term.Stuck ∧
                                    __eo_typeof (leqBase1Rhs a1 a3) ≠
                                      Term.Stuck := by
                                change __eo_typeof_eq
                                    (__eo_typeof (leqBase1Lhs a1 a2 a3))
                                    (__eo_typeof (leqBase1Rhs a1 a3)) =
                                  Term.Bool at hResultTy
                                exact
                                  RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                    (__eo_typeof (leqBase1Lhs a1 a2 a3))
                                    (__eo_typeof (leqBase1Rhs a1 a3))
                                    hResultTy
                              have hRhsNN := hOpsNN.2
                              change __eo_typeof_str_lt
                                  (__eo_typeof a1) (__eo_typeof a3) ≠
                                Term.Stuck at hRhsNN
                              have hRhsArgs :=
                                eo_typeof_str_leq_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a3) hRhsNN
                              have hA1Ty := hRhsArgs.1
                              have hA3Ty := hRhsArgs.2
                              have hLhsNN := hOpsNN.1
                              change __eo_typeof_str_lt
                                  (__eo_typeof (leqBase1Concat a1 a2))
                                  (__eo_typeof a3) ≠
                                Term.Stuck at hLhsNN
                              have hConcatTy :=
                                (eo_typeof_str_leq_args_of_ne_stuck
                                  (__eo_typeof (leqBase1Concat a1 a2))
                                  (__eo_typeof a3) hLhsNN).1
                              have hConcatNN :
                                  __eo_typeof (leqBase1Concat a1 a2) ≠
                                    Term.Stuck := by
                                rw [hConcatTy]
                                simp
                              change __eo_typeof_str_concat
                                  (__eo_typeof a1) (__eo_typeof a2) ≠
                                Term.Stuck at hConcatNN
                              rcases eo_typeof_str_concat_args_of_ne_stuck
                                  (__eo_typeof a1) (__eo_typeof a2)
                                  hConcatNN with ⟨U, hA1Ty', hA2Ty⟩
                              rw [hA1Ty] at hA1Ty'
                              cases hA1Ty'
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                have hPrem1Raw : eo_interprets M P1 true :=
                                  hTrue P1 (by simp [P1, premiseTermList])
                                have hPrem2Raw : eo_interprets M P2 true :=
                                  hTrue P2 (by simp [P2, premiseTermList])
                                have hPrem1 :
                                    eo_interprets M
                                      (leqBase1LenPremise a1 a3) true := by
                                  simpa [hP1] using hPrem1Raw
                                have hPrem2 :
                                    eo_interprets M
                                      (leqBase1NePremise a1 a3) true := by
                                  simpa [hP2] using hPrem2Raw
                                exact
                                  facts___eo_prog_str_leq_concat_base_1_impl
                                    M hM a1 a2 a3 P1 P2 hA1Trans hA2Trans
                                    hA3Trans hA1Ty hA2Ty hA3Ty hPrem1 hPrem2
                                    hProgEq
                              · exact
                                  RuleProofs.eo_has_smt_translation_of_has_bool_type
                                    _
                                    (typed___eo_prog_str_leq_concat_base_1_impl
                                      a1 a2 a3 P1 P2 hA1Trans hA2Trans
                                      hA3Trans hA1Ty hA2Ty hA3Ty hProgEq)
