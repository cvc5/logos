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

private abbrev replSrcInvNoCtn2Premise (y z : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains y) z))
    (Term.Boolean false)

private abbrev replSrcInvNoCtn2Inner (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace y) x) z

private abbrev replSrcInvNoCtn2Lhs (x y z : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply Term.str_replace x)
      (replSrcInvNoCtn2Inner x y z)) x

private abbrev replSrcInvNoCtn2Rhs (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) x

private abbrev replSrcInvNoCtn2Conclusion (x y z : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replSrcInvNoCtn2Lhs x y z))
    (replSrcInvNoCtn2Rhs x y)

private theorem prog_str_repl_repl_src_inv_no_ctn2_info
    (x y z P : Term)
    (hProg :
      __eo_prog_str_repl_repl_src_inv_no_ctn2 x y z (Proof.pf P) ≠
        Term.Stuck) :
    ∃ y0 z0,
      P = replSrcInvNoCtn2Premise y0 z0 ∧ y0 = y ∧ z0 = z ∧
      __eo_prog_str_repl_repl_src_inv_no_ctn2 x y z (Proof.pf P) =
        replSrcInvNoCtn2Conclusion x y z := by
  unfold __eo_prog_str_repl_repl_src_inv_no_ctn2 at hProg
  split at hProg <;> try contradiction
  next heq =>
    cases heq
    rcases RuleProofs.eqs_of_requires_and_eq_true_not_stuck
        _ _ _ _ _ hProg with ⟨hY, hZ⟩
    subst_vars
    refine ⟨_, _, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_repl_repl_src_inv_no_ctn2, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, replSrcInvNoCtn2Conclusion,
      replSrcInvNoCtn2Lhs, replSrcInvNoCtn2Rhs, replSrcInvNoCtn2Inner]

private theorem typed___eo_prog_str_repl_repl_src_inv_no_ctn2_impl
    (x y z P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_repl_repl_src_inv_no_ctn2 x y z (Proof.pf P) =
        replSrcInvNoCtn2Conclusion x y z) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_repl_repl_src_inv_no_ctn2 x y z (Proof.pf P)) := by
  let lhs := replSrcInvNoCtn2Lhs x y z
  let rhs := replSrcInvNoCtn2Rhs x y
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt x)
            (__eo_to_smt z))
          (__eo_to_smt x)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq, typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (replSrcInvNoCtn2Conclusion x y z) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_repl_repl_src_inv_no_ctn2_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z P : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replSrcInvNoCtn2Premise y z) true)
    (hProgEq :
      __eo_prog_str_repl_repl_src_inv_no_ctn2 x y z (Proof.pf P) =
        replSrcInvNoCtn2Conclusion x y z) :
    eo_interprets M
      (__eo_prog_str_repl_repl_src_inv_no_ctn2 x y z (Proof.pf P)) true := by
  let lhs := replSrcInvNoCtn2Lhs x y z
  let rhs := replSrcInvNoCtn2Rhs x y
  have hBool : RuleProofs.eo_has_bool_type
      (replSrcInvNoCtn2Conclusion x y z) := by
    simpa [hProgEq] using
      typed___eo_prog_str_repl_repl_src_inv_no_ctn2_impl
        x y z P hXTrans hYTrans hZTrans hXTy hYTy hZTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
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
  have hZEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt z)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hZSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt z) (by
        unfold term_has_non_none_type
        rw [hZSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  have hAbsent :
      native_seq_contains (native_unpack_seq sy) (native_unpack_seq sz) =
        false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
    cases hPrem with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt z))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hYEval, hZEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt x)
            (__eo_to_smt z))
          (__eo_to_smt x)) =
      __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt x))
    rw [smtx_eval_str_replace_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_str_replace_term_eq, hXEval, hYEval, hZEval]
    simp [__smtx_model_eval_str_replace, Smtm.native_unpack_pack_seq,
      native_seq_replace_src_inv_no_contains2 _ _ _ hAbsent]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_repl_repl_src_inv_no_ctn2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_inv_no_ctn2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn2 args premises ≠
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
                              (__eo_prog_str_repl_repl_src_inv_no_ctn2
                                a1 a2 a3 (Proof.pf P)) =
                            Term.Bool at hResultTy
                          have hRuleProg :
                              __eo_prog_str_repl_repl_src_inv_no_ctn2
                                  a1 a2 a3 (Proof.pf P) ≠ Term.Stuck :=
                            term_ne_stuck_of_typeof_bool hResultTy
                          rcases prog_str_repl_repl_src_inv_no_ctn2_info
                              a1 a2 a3 P hRuleProg with
                            ⟨y0, z0, hP, hY0, hZ0, hProgEq⟩
                          subst y0
                          subst z0
                          rw [hProgEq] at hResultTy
                          have hLhsNN :
                              __eo_typeof
                                  (replSrcInvNoCtn2Lhs a1 a2 a3) ≠
                                Term.Stuck := by
                            change __eo_typeof_eq
                                (__eo_typeof
                                  (replSrcInvNoCtn2Lhs a1 a2 a3))
                                (__eo_typeof
                                  (replSrcInvNoCtn2Rhs a1 a2)) =
                              Term.Bool at hResultTy
                            exact
                              (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                (__eo_typeof
                                  (replSrcInvNoCtn2Lhs a1 a2 a3))
                                (__eo_typeof
                                  (replSrcInvNoCtn2Rhs a1 a2))
                                hResultTy).1
                          change __eo_typeof_str_replace
                              (__eo_typeof a1)
                              (__eo_typeof
                                (replSrcInvNoCtn2Inner a1 a2 a3))
                              (__eo_typeof a1) ≠ Term.Stuck at hLhsNN
                          rcases eo_typeof_str_replace_args_of_ne_stuck
                              (__eo_typeof a1)
                              (__eo_typeof
                                (replSrcInvNoCtn2Inner a1 a2 a3))
                              (__eo_typeof a1) hLhsNN with
                            ⟨T, hA1Ty, hInnerTy, _hA1Ty'⟩
                          have hInnerNN :
                              __eo_typeof
                                  (replSrcInvNoCtn2Inner a1 a2 a3) ≠
                                Term.Stuck := by
                            rw [hInnerTy]
                            simp
                          change __eo_typeof_str_replace
                              (__eo_typeof a2) (__eo_typeof a1)
                              (__eo_typeof a3) ≠ Term.Stuck at hInnerNN
                          rcases eo_typeof_str_replace_args_of_ne_stuck
                              (__eo_typeof a2) (__eo_typeof a1)
                              (__eo_typeof a3) hInnerNN with
                            ⟨U, hA2Ty, hA1Ty', hA3Ty⟩
                          rw [hA1Ty] at hA1Ty'
                          cases hA1Ty'
                          refine ⟨?_, ?_⟩
                          · intro hTrue
                            have hPremRaw : eo_interprets M P true :=
                              hTrue P (by simp [P, premiseTermList])
                            have hPrem :
                                eo_interprets M
                                  (replSrcInvNoCtn2Premise a2 a3) true := by
                              simpa [hP] using hPremRaw
                            exact
                              facts___eo_prog_str_repl_repl_src_inv_no_ctn2_impl
                                M hM a1 a2 a3 P hA1Trans hA2Trans
                                hA3Trans hA1Ty hA2Ty hA3Ty hPrem hProgEq
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type
                                _
                                (typed___eo_prog_str_repl_repl_src_inv_no_ctn2_impl
                                  a1 a2 a3 P hA1Trans hA2Trans hA3Trans
                                  hA1Ty hA2Ty hA3Ty hProgEq)

