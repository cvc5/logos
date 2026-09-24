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

private abbrev replDualIte2Premise (x y : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains x) y))
    (Term.Boolean false)

private abbrev replDualIte2Inner (x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) z

private abbrev replDualIte2Lhs (x y z w : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply Term.str_replace x)
      (replDualIte2Inner x y z)) w

private abbrev replDualIte2Rhs (x y w : Term) : Term :=
  Term.Apply
    (Term.Apply
      (Term.Apply Term.ite
        (Term.Apply (Term.Apply Term.str_contains x) y)) x) w

private abbrev replDualIte2Conclusion (x y z w : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replDualIte2Lhs x y z w))
    (replDualIte2Rhs x y w)

private theorem prog_str_repl_repl_dual_ite2_info
    (x y z w P1 P2 : Term)
    (hProg :
      __eo_prog_str_repl_repl_dual_ite2 x y z w
          (Proof.pf P1) (Proof.pf P2) ≠
        Term.Stuck) :
    ∃ y0 z0 z1 y1,
      P1 = replDualIte2Premise y0 z0 ∧
      P2 = replDualIte2Premise z1 y1 ∧
      y0 = y ∧ z0 = z ∧ z1 = z ∧ y1 = y ∧
      __eo_prog_str_repl_repl_dual_ite2 x y z w
          (Proof.pf P1) (Proof.pf P2) =
        replDualIte2Conclusion x y z w := by
  unfold __eo_prog_str_repl_repl_dual_ite2 at hProg
  split at hProg <;> try contradiction
  next heq1 heq2 =>
    cases heq1
    cases heq2
    rcases eqs_of_requires4_and_eq_true_not_stuck _ _ _ _ _ _ _ _ _
        hProg with ⟨hY0, hZ0, hZ1, hY1⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_repl_repl_dual_ite2, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, replDualIte2Conclusion, replDualIte2Lhs,
      replDualIte2Rhs, replDualIte2Inner]

private theorem typed___eo_prog_str_repl_repl_dual_ite2_impl
    (x y z w P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_repl_repl_dual_ite2 x y z w
          (Proof.pf P1) (Proof.pf P2) =
        replDualIte2Conclusion x y z w) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_repl_repl_dual_ite2 x y z w
        (Proof.pf P1) (Proof.pf P2)) := by
  let lhs := replDualIte2Lhs x y z w
  let rhs := replDualIte2Rhs x y w
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
  have hContainsTy :
      __smtx_typeof
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.Bool := by
    rw [typeof_str_contains_eq]
    simp [hXSmtTy, hYSmtTy, __smtx_typeof_seq_op_2_ret,
      native_ite, native_Teq]
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt w)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq, typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, hWSmtTy,
      __smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt x) (__eo_to_smt w)) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_ite_eq]
    simp [__smtx_typeof_ite, hContainsTy, hXSmtTy, hWSmtTy,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (replDualIte2Conclusion x y z w) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_repl_repl_dual_ite2_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z w P1 P2 : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hPrem : eo_interprets M (replDualIte2Premise y z) true)
    (hProgEq :
      __eo_prog_str_repl_repl_dual_ite2 x y z w
          (Proof.pf P1) (Proof.pf P2) =
        replDualIte2Conclusion x y z w) :
    eo_interprets M
      (__eo_prog_str_repl_repl_dual_ite2 x y z w
        (Proof.pf P1) (Proof.pf P2)) true := by
  let lhs := replDualIte2Lhs x y z w
  let rhs := replDualIte2Rhs x y w
  have hBool : RuleProofs.eo_has_bool_type
      (replDualIte2Conclusion x y z w) := by
    simpa [hProgEq] using
      typed___eo_prog_str_repl_repl_dual_ite2_impl
        x y z w P1 P2 hXTrans hYTrans hZTrans hWTrans
        hXTy hYTy hZTy hWTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
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
  have hZEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt z)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hZSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt z) (by
        unfold term_has_non_none_type
        rw [hZSmtTy]
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
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  rcases seq_value_canonical hWEvalTy with ⟨sw, hWEval⟩
  have hSxValueTy :
      __smtx_typeof_value (SmtValue.Seq sx) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXEval] using hXEvalTy
  have hSwValueTy :
      __smtx_typeof_value (SmtValue.Seq sw) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hWEval] using hWEvalTy
  have hElem :
      __smtx_elem_typeof_seq_value sx =
        __smtx_elem_typeof_seq_value sw := by
    rw [elem_typeof_seq_value_of_typeof_seq_value hSxValueTy,
      elem_typeof_seq_value_of_typeof_seq_value hSwValueTy]
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
          (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z))
          (__eo_to_smt w)) =
      __smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt x) (__eo_to_smt w))
    rw [smtx_eval_str_replace_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_ite_term_eq, smtx_eval_str_contains_term_eq,
      hXEval, hYEval, hZEval, hWEval]
    cases hContains :
        native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy)
    · simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_contains,
        __smtx_model_eval_ite, Smtm.native_unpack_pack_seq, hContains,
        native_seq_replace_dual_ite1_of_contains_false _ _ _ _ hContains,
        hElem, native_pack_unpack_seq]
    · simp [__smtx_model_eval_str_replace, __smtx_model_eval_str_contains,
        __smtx_model_eval_ite, Smtm.native_unpack_pack_seq, hContains,
        native_seq_replace_dual_ite2_of_contains_true _ _ _ _
          hAbsent hContains,
        native_pack_unpack_seq]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_repl_repl_dual_ite2_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_dual_ite2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_repl_repl_dual_ite2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_dual_ite2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_repl_repl_dual_ite2 args premises ≠
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
                                      (__eo_prog_str_repl_repl_dual_ite2
                                        a1 a2 a3 a4 (Proof.pf P1)
                                        (Proof.pf P2)) =
                                    Term.Bool at hResultTy
                                  have hRuleProg :
                                      __eo_prog_str_repl_repl_dual_ite2
                                          a1 a2 a3 a4 (Proof.pf P1)
                                          (Proof.pf P2) ≠
                                        Term.Stuck :=
                                    term_ne_stuck_of_typeof_bool hResultTy
                                  rcases prog_str_repl_repl_dual_ite2_info
                                      a1 a2 a3 a4 P1 P2 hRuleProg with
                                    ⟨y0, z0, z1, y1, hP1, hP2, hY0, hZ0,
                                      hZ1, hY1, hProgEq⟩
                                  subst y0
                                  subst z0
                                  subst z1
                                  subst y1
                                  rw [hProgEq] at hResultTy
                                  have hLhsNN :
                                      __eo_typeof
                                          (replDualIte2Lhs
                                            a1 a2 a3 a4) ≠
                                        Term.Stuck := by
                                    change __eo_typeof_eq
                                        (__eo_typeof
                                          (replDualIte2Lhs
                                            a1 a2 a3 a4))
                                        (__eo_typeof
                                          (replDualIte2Rhs a1 a2 a4)) =
                                      Term.Bool at hResultTy
                                    exact
                                      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                        (__eo_typeof
                                          (replDualIte2Lhs
                                            a1 a2 a3 a4))
                                        (__eo_typeof
                                          (replDualIte2Rhs a1 a2 a4))
                                        hResultTy).1
                                  change __eo_typeof_str_replace
                                      (__eo_typeof a1)
                                      (__eo_typeof
                                        (replDualIte2Inner a1 a2 a3))
                                      (__eo_typeof a4) ≠ Term.Stuck at hLhsNN
                                  rcases eo_typeof_str_replace_args_of_ne_stuck
                                      (__eo_typeof a1)
                                      (__eo_typeof
                                        (replDualIte2Inner a1 a2 a3))
                                      (__eo_typeof a4) hLhsNN with
                                    ⟨T, hA1Ty, hInnerTy, hA4Ty⟩
                                  have hInnerNN :
                                      __eo_typeof
                                          (replDualIte2Inner a1 a2 a3) ≠
                                        Term.Stuck := by
                                    rw [hInnerTy]
                                    simp
                                  change __eo_typeof_str_replace
                                      (__eo_typeof a1) (__eo_typeof a2)
                                      (__eo_typeof a3) ≠ Term.Stuck at hInnerNN
                                  rcases eo_typeof_str_replace_args_of_ne_stuck
                                      (__eo_typeof a1) (__eo_typeof a2)
                                      (__eo_typeof a3) hInnerNN with
                                    ⟨U, hA1Ty', hA2Ty, hA3Ty⟩
                                  rw [hA1Ty] at hA1Ty'
                                  cases hA1Ty'
                                  refine ⟨?_, ?_⟩
                                  · intro hTrue
                                    have hPremRaw : eo_interprets M P1 true :=
                                      hTrue P1 (by
                                        simp [P1, premiseTermList])
                                    have hPrem :
                                        eo_interprets M
                                          (replDualIte2Premise a2 a3)
                                          true := by
                                      simpa [hP1] using hPremRaw
                                    exact
                                      facts___eo_prog_str_repl_repl_dual_ite2_impl
                                        M hM a1 a2 a3 a4 P1 P2 hA1Trans
                                        hA2Trans hA3Trans hA4Trans hA1Ty
                                        hA2Ty hA3Ty hA4Ty hPrem hProgEq
                                  · exact
                                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        _
                                        (typed___eo_prog_str_repl_repl_dual_ite2_impl
                                          a1 a2 a3 a4 P1 P2 hA1Trans
                                          hA2Trans hA3Trans hA4Trans hA1Ty
                                          hA2Ty hA3Ty hA4Ty hProgEq)
