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

private abbrev replSrcInvNoCtn3Premise (x z : Term) : Term :=
  Term.Apply
    (Term.Apply Term.eq (Term.Apply (Term.Apply Term.str_contains x) z))
    (Term.Boolean false)

private abbrev replSrcInvNoCtn3Inner (y z w : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace y) z) w

private abbrev replSrcInvNoCtn3Lhs
    (x y z w u : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.Apply Term.str_replace x)
      (replSrcInvNoCtn3Inner y z w)) u

private abbrev replSrcInvNoCtn3Rhs (x y u : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply Term.str_replace x) y) u

private abbrev replSrcInvNoCtn3Conclusion
    (x y z w u : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (replSrcInvNoCtn3Lhs x y z w u))
    (replSrcInvNoCtn3Rhs x y u)

private theorem prog_str_repl_repl_src_inv_no_ctn3_info
    (x y z w u P Q : Term)
    (hProg :
      __eo_prog_str_repl_repl_src_inv_no_ctn3 x y z w u
          (Proof.pf P) (Proof.pf Q) ≠ Term.Stuck) :
    ∃ x0 z0 x1 w0,
      P = replSrcInvNoCtn3Premise x0 z0 ∧
      Q = replSrcInvNoCtn3Premise x1 w0 ∧
      x0 = x ∧ z0 = z ∧ x1 = x ∧ w0 = w ∧
      __eo_prog_str_repl_repl_src_inv_no_ctn3 x y z w u
          (Proof.pf P) (Proof.pf Q) =
        replSrcInvNoCtn3Conclusion x y z w u := by
  unfold __eo_prog_str_repl_repl_src_inv_no_ctn3 at hProg
  split at hProg <;> try contradiction
  next heqP heqQ =>
    cases heqP
    cases heqQ
    rcases eqs_of_requires4_and_eq_true_not_stuck
        _ _ _ _ _ _ _ _ _ hProg with ⟨hX0, hZ0, hX1, hW0⟩
    subst_vars
    refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp [__eo_prog_str_repl_repl_src_inv_no_ctn3, __eo_requires,
      __eo_eq, __eo_and, SmtEval.native_ite, native_teq, native_and,
      SmtEval.native_not, replSrcInvNoCtn3Conclusion,
      replSrcInvNoCtn3Lhs, replSrcInvNoCtn3Rhs, replSrcInvNoCtn3Inner]

private theorem typed___eo_prog_str_repl_repl_src_inv_no_ctn3_impl
    (x y z w u P Q : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hUTrans : RuleProofs.eo_has_smt_translation u)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hUTy : __eo_typeof u = Term.Apply Term.Seq T)
    (hProgEq :
      __eo_prog_str_repl_repl_src_inv_no_ctn3 x y z w u
          (Proof.pf P) (Proof.pf Q) =
        replSrcInvNoCtn3Conclusion x y z w u) :
    RuleProofs.eo_has_bool_type
      (__eo_prog_str_repl_repl_src_inv_no_ctn3 x y z w u
        (Proof.pf P) (Proof.pf Q)) := by
  let lhs := replSrcInvNoCtn3Lhs x y z w u
  let rhs := replSrcInvNoCtn3Rhs x y u
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
  have hUSmtTy := smtx_typeof_of_eo_seq u T hUTrans hUTy
  have hLhsTy :
      __smtx_typeof (__eo_to_smt lhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt z)
            (__eo_to_smt w))
          (__eo_to_smt u)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq, typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hZSmtTy, hWSmtTy, hUSmtTy,
      __smtx_typeof_seq_op_3, native_ite, native_Teq]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt rhs) =
        SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt u)) = SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_replace_eq]
    simp [hXSmtTy, hYSmtTy, hUSmtTy, __smtx_typeof_seq_op_3,
      native_ite, native_Teq]
  have hBool : RuleProofs.eo_has_bool_type
      (replSrcInvNoCtn3Conclusion x y z w u) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  rw [hProgEq]
  exact hBool

private theorem facts___eo_prog_str_repl_repl_src_inv_no_ctn3_impl
    (M : SmtModel) (hM : model_wf M)
    (x y z w u P Q : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hYTrans : RuleProofs.eo_has_smt_translation y)
    (hZTrans : RuleProofs.eo_has_smt_translation z)
    (hWTrans : RuleProofs.eo_has_smt_translation w)
    (hUTrans : RuleProofs.eo_has_smt_translation u)
    (hXTy : __eo_typeof x = Term.Apply Term.Seq T)
    (hYTy : __eo_typeof y = Term.Apply Term.Seq T)
    (hZTy : __eo_typeof z = Term.Apply Term.Seq T)
    (hWTy : __eo_typeof w = Term.Apply Term.Seq T)
    (hUTy : __eo_typeof u = Term.Apply Term.Seq T)
    (hPremZ : eo_interprets M (replSrcInvNoCtn3Premise x z) true)
    (hPremW : eo_interprets M (replSrcInvNoCtn3Premise x w) true)
    (hProgEq :
      __eo_prog_str_repl_repl_src_inv_no_ctn3 x y z w u
          (Proof.pf P) (Proof.pf Q) =
        replSrcInvNoCtn3Conclusion x y z w u) :
    eo_interprets M
      (__eo_prog_str_repl_repl_src_inv_no_ctn3 x y z w u
        (Proof.pf P) (Proof.pf Q)) true := by
  let lhs := replSrcInvNoCtn3Lhs x y z w u
  let rhs := replSrcInvNoCtn3Rhs x y u
  have hBool : RuleProofs.eo_has_bool_type
      (replSrcInvNoCtn3Conclusion x y z w u) := by
    simpa [hProgEq] using
      typed___eo_prog_str_repl_repl_src_inv_no_ctn3_impl
        x y z w u P Q hXTrans hYTrans hZTrans hWTrans hUTrans
        hXTy hYTy hZTy hWTy hUTy hProgEq
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hYSmtTy := smtx_typeof_of_eo_seq y T hYTrans hYTy
  have hZSmtTy := smtx_typeof_of_eo_seq z T hZTrans hZTy
  have hWSmtTy := smtx_typeof_of_eo_seq w T hWTrans hWTy
  have hUSmtTy := smtx_typeof_of_eo_seq u T hUTrans hUTy
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
  have hUEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hUSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt u) (by
        unfold term_has_non_none_type
        rw [hUSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  rcases seq_value_canonical hYEvalTy with ⟨sy, hYEval⟩
  rcases seq_value_canonical hZEvalTy with ⟨sz, hZEval⟩
  rcases seq_value_canonical hWEvalTy with ⟨sw, hWEval⟩
  rcases seq_value_canonical hUEvalTy with ⟨su, hUEval⟩
  have hZAbsent :
      native_seq_contains (native_unpack_seq sx) (native_unpack_seq sz) =
        false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremZ
    cases hPremZ with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt z))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hXEval, hZEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hWAbsent :
      native_seq_contains (native_unpack_seq sx) (native_unpack_seq sw) =
        false := by
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPremW
    cases hPremW with
    | intro_true _ hEval =>
        change __smtx_model_eval M
            (SmtTerm.eq
              (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt w))
              (SmtTerm.Boolean false)) =
          SmtValue.Boolean true at hEval
        rw [smtx_eval_eq_term_eq, smtx_eval_str_contains_term_eq,
          hXEval, hWEval, smtx_eval_boolean_term_eq] at hEval
        simpa [__smtx_model_eval_str_contains, __smtx_model_eval_eq,
          native_veq] using hEval
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt x)
          (SmtTerm.str_replace (__eo_to_smt y) (__eo_to_smt z)
            (__eo_to_smt w))
          (__eo_to_smt u)) =
      __smtx_model_eval M
        (SmtTerm.str_replace (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt u))
    rw [smtx_eval_str_replace_term_eq, smtx_eval_str_replace_term_eq,
      smtx_eval_str_replace_term_eq, hXEval, hYEval, hZEval, hWEval,
      hUEval]
    simp [__smtx_model_eval_str_replace, Smtm.native_unpack_pack_seq,
      native_seq_replace_src_inv_no_contains3 _ _ _ _ _
        hZAbsent hWAbsent]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_str_repl_repl_src_inv_no_ctn3_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_inv_no_ctn3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn3 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn3 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn3 args premises ≠
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
                  | nil => exact absurd rfl hProg
                  | cons a5 args =>
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
                                      let P := __eo_state_proven_nth s n1
                                      let Q := __eo_state_proven_nth s n2
                                      have hA1Trans :
                                          RuleProofs.eo_has_smt_translation a1 := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.1
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
                                      have hA5Trans :
                                          RuleProofs.eo_has_smt_translation a5 := by
                                        simpa [cmdTranslationOk,
                                          cArgListTranslationOk] using
                                            hCmdTrans.2.2.2.2.1
                                      change __eo_typeof
                                          (__eo_prog_str_repl_repl_src_inv_no_ctn3
                                            a1 a2 a3 a4 a5
                                            (Proof.pf P) (Proof.pf Q)) =
                                        Term.Bool at hResultTy
                                      have hRuleProg :
                                          __eo_prog_str_repl_repl_src_inv_no_ctn3
                                              a1 a2 a3 a4 a5
                                              (Proof.pf P) (Proof.pf Q) ≠
                                            Term.Stuck :=
                                        term_ne_stuck_of_typeof_bool hResultTy
                                      rcases
                                          prog_str_repl_repl_src_inv_no_ctn3_info
                                            a1 a2 a3 a4 a5 P Q hRuleProg with
                                        ⟨x0, z0, x1, w0, hP, hQ,
                                          hX0, hZ0, hX1, hW0, hProgEq⟩
                                      subst x0
                                      subst z0
                                      subst x1
                                      subst w0
                                      rw [hProgEq] at hResultTy
                                      have hLhsNN :
                                          __eo_typeof
                                              (replSrcInvNoCtn3Lhs
                                                a1 a2 a3 a4 a5) ≠
                                            Term.Stuck := by
                                        change __eo_typeof_eq
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Lhs
                                                a1 a2 a3 a4 a5))
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Rhs
                                                a1 a2 a5)) =
                                          Term.Bool at hResultTy
                                        exact
                                          (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Lhs
                                                a1 a2 a3 a4 a5))
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Rhs
                                                a1 a2 a5))
                                            hResultTy).1
                                      have hRhsNN :
                                          __eo_typeof
                                              (replSrcInvNoCtn3Rhs
                                                a1 a2 a5) ≠ Term.Stuck := by
                                        change __eo_typeof_eq
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Lhs
                                                a1 a2 a3 a4 a5))
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Rhs
                                                a1 a2 a5)) =
                                          Term.Bool at hResultTy
                                        exact
                                          (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Lhs
                                                a1 a2 a3 a4 a5))
                                            (__eo_typeof
                                              (replSrcInvNoCtn3Rhs
                                                a1 a2 a5))
                                            hResultTy).2
                                      change __eo_typeof_str_replace
                                          (__eo_typeof a1) (__eo_typeof a2)
                                          (__eo_typeof a5) ≠ Term.Stuck at hRhsNN
                                      rcases eo_typeof_str_replace_args_of_ne_stuck
                                          (__eo_typeof a1) (__eo_typeof a2)
                                          (__eo_typeof a5) hRhsNN with
                                        ⟨T, hA1Ty, hA2Ty, hA5Ty⟩
                                      change __eo_typeof_str_replace
                                          (__eo_typeof a1)
                                          (__eo_typeof
                                            (replSrcInvNoCtn3Inner a2 a3 a4))
                                          (__eo_typeof a5) ≠ Term.Stuck at hLhsNN
                                      rcases eo_typeof_str_replace_args_of_ne_stuck
                                          (__eo_typeof a1)
                                          (__eo_typeof
                                            (replSrcInvNoCtn3Inner a2 a3 a4))
                                          (__eo_typeof a5) hLhsNN with
                                        ⟨U, hA1Ty', hInnerTy, _hA5Ty'⟩
                                      rw [hA1Ty] at hA1Ty'
                                      cases hA1Ty'
                                      have hInnerNN :
                                          __eo_typeof
                                              (replSrcInvNoCtn3Inner
                                                a2 a3 a4) ≠ Term.Stuck := by
                                        rw [hInnerTy]
                                        simp
                                      change __eo_typeof_str_replace
                                          (__eo_typeof a2) (__eo_typeof a3)
                                          (__eo_typeof a4) ≠ Term.Stuck at hInnerNN
                                      rcases eo_typeof_str_replace_args_of_ne_stuck
                                          (__eo_typeof a2) (__eo_typeof a3)
                                          (__eo_typeof a4) hInnerNN with
                                        ⟨V, hA2Ty', hA3Ty, hA4Ty⟩
                                      rw [hA2Ty] at hA2Ty'
                                      cases hA2Ty'
                                      refine ⟨?_, ?_⟩
                                      · intro hTrue
                                        have hPremPRaw :
                                            eo_interprets M P true :=
                                          hTrue P (by
                                            simp [P, Q, premiseTermList])
                                        have hPremP :
                                            eo_interprets M
                                              (replSrcInvNoCtn3Premise
                                                a1 a3) true := by
                                          simpa [hP] using hPremPRaw
                                        have hPremQRaw :
                                            eo_interprets M Q true :=
                                          hTrue Q (by
                                            simp [P, Q, premiseTermList])
                                        have hPremQ :
                                            eo_interprets M
                                              (replSrcInvNoCtn3Premise
                                                a1 a4) true := by
                                          simpa [hQ] using hPremQRaw
                                        exact
                                          facts___eo_prog_str_repl_repl_src_inv_no_ctn3_impl
                                            M hM a1 a2 a3 a4 a5 P Q
                                            hA1Trans hA2Trans hA3Trans
                                            hA4Trans hA5Trans hA1Ty hA2Ty
                                            hA3Ty hA4Ty hA5Ty hPremP hPremQ
                                            hProgEq
                                      · exact
                                          RuleProofs.eo_has_smt_translation_of_has_bool_type
                                            _
                                            (typed___eo_prog_str_repl_repl_src_inv_no_ctn3_impl
                                              a1 a2 a3 a4 a5 P Q
                                              hA1Trans hA2Trans hA3Trans
                                              hA4Trans hA5Trans hA1Ty hA2Ty
                                              hA3Ty hA4Ty hA5Ty hProgEq)
