module

public import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import all Cpc.Proofs.RuleSupport.StrContainsReplCharSupport

open Eo
open SmtEval
open Smtm
open StrEqReplSupport
open StrContainsReplCharSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev containsReplSelfCharPremise (w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply Term.str_len w))
    (Term.Numeral 1)

private abbrev containsReplSelfCharValue (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) x

private abbrev containsReplSelfCharLhs (x y w : Term) : Term :=
  Term.Apply
    (Term.Apply Term.str_contains (containsReplSelfCharValue x y)) w

private abbrev containsReplSelfCharRhs (x w : Term) : Term :=
  Term.Apply (Term.Apply Term.str_contains x) w

private abbrev containsReplSelfCharConclusion (x y w : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (containsReplSelfCharLhs x y w))
    (containsReplSelfCharRhs x w)

private theorem prog_str_contains_repl_self_tgt_char_info
    (x y w P : Term)
    (hProg :
      __eo_prog_str_contains_repl_self_tgt_char x y w (Proof.pf P) ≠
        Term.Stuck) :
    ∃ w0,
      P = containsReplSelfCharPremise w0 ∧ w0 = w ∧
      __eo_prog_str_contains_repl_self_tgt_char x y w (Proof.pf P) =
        containsReplSelfCharConclusion x y w := by
  unfold __eo_prog_str_contains_repl_self_tgt_char at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    have hW := RuleProofs.eq_of_requires_eq_true_not_stuck _ _ _ hProg
    subst_vars
    refine ⟨_, rfl, rfl, ?_⟩
    simp [__eo_prog_str_contains_repl_self_tgt_char, __eo_requires,
      __eo_eq, SmtEval.native_ite, native_teq, SmtEval.native_not,
      containsReplSelfCharConclusion, containsReplSelfCharLhs,
      containsReplSelfCharRhs, containsReplSelfCharValue]

private theorem typed___eo_prog_str_contains_repl_self_tgt_char_impl
    (x y w P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_contains_repl_self_tgt_char x y w (Proof.pf P) =
        containsReplSelfCharConclusion x y w) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_contains_repl_self_tgt_char x y w (Proof.pf P)) := by
  let value := containsReplSelfCharValue x y
  let lhs := containsReplSelfCharLhs x y w
  let rhs := containsReplSelfCharRhs x w
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
  have hValueTy :
      __smtx_typeof (__eo_to_smt value) = SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_3, native_ite,
      native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt x))
          (__eo_to_smt w)) = SmtType.Bool
    rw [typeof_str_contains_eq]
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hWSmtTy, __smtx_typeof_seq_op_3,
      __smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt w)) =
      SmtType.Bool
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hWSmtTy, __smtx_typeof_seq_op_2_ret, native_ite,
      native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (containsReplSelfCharConclusion x y w) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_contains_repl_self_tgt_char_impl
    (M : SmtModel) (hM : model_wf M)
    (x y w P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (containsReplSelfCharPremise w) true)
    (hProgEq :
      __eo_prog_str_contains_repl_self_tgt_char x y w (Proof.pf P) =
        containsReplSelfCharConclusion x y w) :
    eo_interprets M
      (__eo_prog_str_contains_repl_self_tgt_char x y w (Proof.pf P)) true := by
  let lhs := containsReplSelfCharLhs x y w
  let rhs := containsReplSelfCharRhs x w
  have hBool : RuleProofs.eo_has_bool_type
      (containsReplSelfCharConclusion x y w) := by
    simpa [hProgEq] using
      typed___eo_prog_str_contains_repl_self_tgt_char_impl
        x y w P hXTrans hYTrans hWTrans hXTy hYTy hWTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  have hYEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hYSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        rw [hYSmtTy]
        simp)
  have hWEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt w)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hWSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt w) (by
        unfold term_has_non_none_type
        rw [hWSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hWEvalTy with ⟨sw, hWEval⟩
  have hWLen : (native_unpack_seq sw).length = 1 := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt w))
              (SmtTerm.Numeral 1)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_len_term_eq, hWEval,
          smtx_eval_numeral_term_eq] at hEval
        have hLenInt :
            (Int.ofNat (native_unpack_seq sw).length : Int) = 1 := by
          simpa [__smtx_model_eval_str_len, __smtx_model_eval_eq,
            native_veq, native_seq_len] using hEval
        change Int.ofNat (native_unpack_seq sw).length = Int.ofNat 1 at hLenInt
        exact Int.ofNat.inj hLenInt
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_contains
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt x))
          (__eo_to_smt w)) =
      __smtx_model_eval M
        (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt w))
    rw [smtx_eval_str_contains_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_str_contains_term_eq, hXEval, hYEval, hWEval]
    simp [__smtx_model_eval_str_contains, __smtx_model_eval_str_replace,
      Smtm.native_unpack_pack_seq,
      native_seq_contains_replace_self_of_target_len_one _ _ _ hWLen]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_contains_repl_self_tgt_char_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_self_tgt_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_contains_repl_self_tgt_char args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_self_tgt_char args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_contains_repl_self_tgt_char args premises ≠
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
                  | cons n premises =>
                      cases premises with
                      | cons _ _ => exact absurd rfl hProg
                      | nil =>
                          let P := __eo_state_proven_nth s n
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
                          change __eo_typeof
                              (__eo_prog_str_contains_repl_self_tgt_char
                                a1 a2 a3 (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_contains_repl_self_tgt_char
                                  a1 a2 a3 (Proof.pf P) ≠
                                Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_contains_repl_self_tgt_char_info
                              a1 a2 a3 P hRuleProg with
                            ⟨w0, hP, hW0, hProgEq⟩
                          subst w0
                          rw [hProgEq] at hResultTy
                          have hOperandsNN :
                              __eo_typeof
                                  (containsReplSelfCharLhs a1 a2 a3) ≠
                                  Term.Stuck ∧
                                __eo_typeof
                                  (containsReplSelfCharRhs a1 a3) ≠
                                  Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof
                                  (containsReplSelfCharLhs a1 a2 a3))
                                (__eo_typeof
                                  (containsReplSelfCharRhs a1 a3)) =
                              Term.Bool at hResultTy
                            exact
                              RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof
                                  (containsReplSelfCharLhs a1 a2 a3))
                                (__eo_typeof
                                  (containsReplSelfCharRhs a1 a3)) hResultTy
                          have hArgTypes :
                              ∃ T,
                                __eo_typeof a1 = Term.Apply Term.Seq T ∧
                                __eo_typeof a2 = Term.Apply Term.Seq T ∧
                                __eo_typeof a3 = Term.Apply Term.Seq T := by
                            have hRhsNN := hOperandsNN.2
                            change __eo_typeof_str_contains
                                (__eo_typeof a1) (__eo_typeof a3) ≠
                              Term.Stuck at hRhsNN
                            rcases eo_typeof_str_contains_args_of_ne_stuck
                                (__eo_typeof a1) (__eo_typeof a3)
                                hRhsNN with
                              ⟨T, hA1Ty, hA3Ty⟩
                            have hLhsNN := hOperandsNN.1
                            change __eo_typeof_str_contains
                                (__eo_typeof
                                  (containsReplSelfCharValue a1 a2))
                                (__eo_typeof a3) ≠
                              Term.Stuck at hLhsNN
                            rcases eo_typeof_str_contains_args_of_ne_stuck
                                (__eo_typeof
                                  (containsReplSelfCharValue a1 a2))
                                (__eo_typeof a3) hLhsNN with
                              ⟨U, hValueTy, _hA3Ty'⟩
                            have hValueNN :
                                __eo_typeof
                                    (containsReplSelfCharValue a1 a2) ≠
                                  Term.Stuck := by
                              rw [hValueTy]
                              simp
                            change __eo_typeof_str_replace
                                (__eo_typeof a1) (__eo_typeof a2)
                                (__eo_typeof a1) ≠
                              Term.Stuck at hValueNN
                            rcases eo_typeof_str_replace_args_of_ne_stuck
                                (__eo_typeof a1) (__eo_typeof a2)
                                (__eo_typeof a1) hValueNN with
                              ⟨V, hA1Ty', hA2Ty, _hA1Ty''⟩
                            rw [hA1Ty] at hA1Ty'
                            cases hA1Ty'
                            exact ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          rcases hArgTypes with ⟨T, hA1Ty, hA2Ty, hA3Ty⟩
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (containsReplSelfCharPremise a3) true := by
                              simpa [hP] using hPremRaw
                            exact
                              facts___eo_prog_str_contains_repl_self_tgt_char_impl
                                M hM a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                _
                                (typed___eo_prog_str_contains_repl_self_tgt_char_impl
                                  a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                  hA1Ty hA2Ty hA3Ty hProgEq)
