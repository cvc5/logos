module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_str_rev_str_rev_arg_seq_of_ne_stuck
    (T : Term)
    (h : __eo_typeof_str_rev (__eo_typeof_str_rev T) ≠ Term.Stuck) :
    ∃ U, T = Term.Apply Term.Seq U := by
  cases T <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f x =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

private theorem smtx_typeof_of_eo_seq
    (a T : Term)
    (hTrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof a = Term.Apply Term.Seq T) :
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq (__eo_to_smt_type T) := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hTrans
  have hComponentNN : __eo_to_smt_type T ≠ SmtType.None := by
    intro hNone
    unfold RuleProofs.eo_has_smt_translation at hTrans
    apply hTrans
    rw [hTyRaw, hTy]
    simp [TranslationProofs.eo_to_smt_type_seq,
      __smtx_typeof_guard, hNone, native_ite, native_Teq]
  rw [hTy] at hTyRaw
  rw [TranslationProofs.eo_to_smt_type_seq] at hTyRaw
  simpa using hTyRaw.trans
    (TranslationProofs.smtx_typeof_guard_of_non_none
      (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) hComponentNN)

private theorem smtx_eval_str_rev_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_rev x) =
      __smtx_model_eval_str_rev (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem typed___eo_prog_seq_rev_rev_impl
    (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : ∃ T, __eo_typeof x = Term.Apply Term.Seq T) :
    RuleProofs.eo_has_bool_type (__eo_prog_seq_rev_rev x) := by
  rcases hXTy with ⟨T, hXTy⟩
  let lhs := Term.Apply Term.str_rev (Term.Apply Term.str_rev x)
  let rhs := x
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hRevTy :
      __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    rw [typeof_str_rev_eq, hXSmtTy]
    simp [__smtx_typeof_seq_op_1]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) =
      SmtType.Seq (__eo_to_smt_type T) := by
    change __smtx_typeof
        (SmtTerm.str_rev (SmtTerm.str_rev (__eo_to_smt x))) =
      SmtType.Seq (__eo_to_smt_type T)
    rw [typeof_str_rev_eq, hRevTy]
    simp [__smtx_typeof_seq_op_1]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hXSmtTy]) (by rw [hLhsTy]; simp)
  have hXNotStuck : x ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProg :
      __eo_prog_seq_rev_rev x = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_seq_rev_rev x =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_rev (Term.Apply Term.str_rev x)))
            x := by
      cases x <;> simp [__eo_prog_seq_rev_rev] at hXNotStuck ⊢
    simpa [lhs, rhs] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_seq_rev_rev_impl
    (M : SmtModel) (hM : model_wf M) (x : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation x)
    (hXTy : ∃ T, __eo_typeof x = Term.Apply Term.Seq T) :
    eo_interprets M (__eo_prog_seq_rev_rev x) true := by
  rcases hXTy with ⟨T, hXTy⟩
  let lhs := Term.Apply Term.str_rev (Term.Apply Term.str_rev x)
  let rhs := x
  have hXNotStuck : x ≠ Term.Stuck := by
    exact RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hProg :
      __eo_prog_seq_rev_rev x = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_seq_rev_rev x =
          Term.Apply
            (Term.Apply Term.eq
              (Term.Apply Term.str_rev (Term.Apply Term.str_rev x)))
            x := by
      cases x <;> simp [__eo_prog_seq_rev_rev] at hXNotStuck ⊢
    simpa [lhs, rhs] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [hProg] using
      typed___eo_prog_seq_rev_rev_impl x hXTrans ⟨T, hXTy⟩
  have hXSmtTy := smtx_typeof_of_eo_seq x T hXTrans hXTy
  have hXEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.Seq (__eo_to_smt_type T) := by
    simpa [hXSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        rw [hXSmtTy]
        simp)
  rcases seq_value_canonical hXEvalTy with ⟨sx, hXEval⟩
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt lhs) =
        __smtx_model_eval M (__eo_to_smt rhs) := by
    change __smtx_model_eval M
        (SmtTerm.str_rev (SmtTerm.str_rev (__eo_to_smt x))) =
      __smtx_model_eval M (__eo_to_smt x)
    rw [smtx_eval_str_rev_term_eq, smtx_eval_str_rev_term_eq]
    rw [hXEval]
    simp [__smtx_model_eval_str_rev, native_seq_rev,
      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
      List.reverse_reverse, native_pack_unpack_seq]
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt rhs))

public theorem cmd_step_seq_rev_rev_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_rev_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.seq_rev_rev args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_rev_rev args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.seq_rev_rev args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              have hA1NotStuck : a1 ≠ Term.Stuck := by
                intro hStuck
                subst a1
                apply hProg
                rfl
              let lhs := Term.Apply Term.str_rev (Term.Apply Term.str_rev a1)
              let rhs := a1
              have hProgEq :
                  __eo_cmd_step_proven s CRule.seq_rev_rev
                    (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq lhs) rhs := by
                have hProgEqRaw :
                    __eo_cmd_step_proven s CRule.seq_rev_rev
                        (CArgList.cons a1 CArgList.nil) CIndexList.nil =
                      Term.Apply
                        (Term.Apply Term.eq
                          (Term.Apply Term.str_rev (Term.Apply Term.str_rev a1)))
                        a1 := by
                  cases hA1 : a1 <;> first
                    | exact False.elim (hA1NotStuck hA1)
                    | rfl
                simpa [lhs, rhs] using hProgEqRaw
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                Term.Bool at hResultTy
              have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
              have hA1Ty : ∃ T, __eo_typeof a1 = Term.Apply Term.Seq T := by
                change __eo_typeof_str_rev
                    (__eo_typeof_str_rev (__eo_typeof a1)) ≠ Term.Stuck
                  at hLhsNotStuck
                exact eo_typeof_str_rev_str_rev_arg_seq_of_ne_stuck
                  (__eo_typeof a1) hLhsNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_seq_rev_rev a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_seq_rev_rev_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_seq_rev_rev_impl M hM a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_seq_rev_rev a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
