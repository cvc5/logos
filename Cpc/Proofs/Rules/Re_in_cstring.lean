module

public import Cpc.Proofs.RuleSupport.ReConstSupport
import all Cpc.Proofs.RuleSupport.ReConstSupport

open Eo
open SmtEval
open Smtm
open ReConstSupport

-- Keep string coercions on the model's explicit string-to-value embedding.
attribute [-instance] List.instMonad List.instAlternativeMonad_mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ReInCStringProof

private abbrev lhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.str_in_re t)
    (Term.Apply (Term.UOp UserOp.str_to_re) s)

private abbrev rhs (t s : Term) : Term :=
  Term.Apply (Term.Apply Term.eq t) s

private theorem typed___eo_prog_re_in_cstring_impl
    (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char)
    (hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char) :
    RuleProofs.eo_has_bool_type (__eo_prog_re_in_cstring a1 a2) := by
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char :=
    smt_seq_char_of_eo_type a1 hA1Trans hA1Ty
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.Seq SmtType.Char :=
    smt_seq_char_of_eo_type a2 hA2Trans hA2Ty
  have hStrToReTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) a2)) =
        SmtType.RegLan :=
    smtx_typeof_str_to_re_of_seq_char a2 hA2SmtTy
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs a1 a2)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.str_in_re (__eo_to_smt a1)
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) a2))) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hA1SmtTy, hStrToReTy, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt (rhs a1 a2)) = SmtType.Bool := by
    change __smtx_typeof
      (SmtTerm.eq (__eo_to_smt a1) (__eo_to_smt a2)) = SmtType.Bool
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hA1SmtTy, hA2SmtTy,
      native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type (lhs a1 a2) (rhs a1 a2)
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_in_cstring a1 a2 =
        Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2) := by
    cases hA1 : a1 <;>
      first | exact False.elim (hA1NotStuck hA1) | all_goals
        cases hA2 : a2 <;>
          first | exact False.elim (hA2NotStuck hA2) | rfl
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_in_cstring_impl
    (M : SmtModel) (hM : model_wf M) (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char)
    (hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char) :
    eo_interprets M (__eo_prog_re_in_cstring a1 a2) true := by
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.Seq SmtType.Char :=
    smt_seq_char_of_eo_type a1 hA1Trans hA1Ty
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.Seq SmtType.Char :=
    smt_seq_char_of_eo_type a2 hA2Trans hA2Ty
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) =
        SmtType.Seq SmtType.Char := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1) (by
        unfold term_has_non_none_type
        rw [hA1SmtTy]
        simp)
  have hA2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a2)) =
        SmtType.Seq SmtType.Char := by
    simpa [hA2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a2) (by
        unfold term_has_non_none_type
        rw [hA2SmtTy]
        simp)
  rcases seq_value_canonical hA1EvalTy with ⟨st, hst⟩
  rcases seq_value_canonical hA2EvalTy with ⟨ss, hss⟩
  have hStTy : __smtx_typeof_seq_value st = SmtType.Seq SmtType.Char := by
    simpa [hst, __smtx_typeof_value] using hA1EvalTy
  have hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
    simpa [hss, __smtx_typeof_value] using hA2EvalTy
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2)) := by
    have hTyped :=
      typed___eo_prog_re_in_cstring_impl a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
    have hA1NotStuck : a1 ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hA1Ty
      have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
        native_decide
      exact hBad hA1Ty
    have hA2NotStuck : a2 ≠ Term.Stuck := by
      intro hStuck
      rw [hStuck] at hA2Ty
      have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
        native_decide
      exact hBad hA2Ty
    have hProg :
        __eo_prog_re_in_cstring a1 a2 =
          Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2) := by
      cases hA1 : a1 <;>
        first | exact False.elim (hA1NotStuck hA1) | all_goals
          cases hA2 : a2 <;>
            first | exact False.elim (hA2NotStuck hA2) | rfl
    rwa [hProg] at hTyped
  have hEvalEq :
      __smtx_model_eval M (__eo_to_smt (lhs a1 a2)) =
        __smtx_model_eval M (__eo_to_smt (rhs a1 a2)) := by
    change
      __smtx_model_eval M
          (SmtTerm.str_in_re (__eo_to_smt a1)
            (SmtTerm.str_to_re (__eo_to_smt a2))) =
        __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt a1) (__eo_to_smt a2))
    simp [__smtx_model_eval]
    change
      __smtx_model_eval_str_in_re
          (__smtx_model_eval M (__eo_to_smt a1))
          (__smtx_model_eval_str_to_re
            (__smtx_model_eval M (__eo_to_smt a2))) =
        __smtx_model_eval_eq
          (__smtx_model_eval M (__eo_to_smt a1))
          (__smtx_model_eval M (__eo_to_smt a2))
    rw [hst, hss]
    simp [__smtx_model_eval_str_to_re]
    exact smtx_model_eval_re_in_cstring_eq st ss hStTy hSsTy
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.Apply Term.Seq Term.Char := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_in_cstring a1 a2 =
        Term.Apply (Term.Apply Term.eq (lhs a1 a2)) (rhs a1 a2) := by
    cases hA1 : a1 <;>
      first | exact False.elim (hA1NotStuck hA1) | all_goals
        cases hA2 : a2 <;>
          first | exact False.elim (hA2NotStuck hA2) | rfl
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs a1 a2) (rhs a1 a2) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt (rhs a1 a2)))

end ReInCStringProof

public theorem cmd_step_re_in_cstring_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_cstring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_in_cstring args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_cstring args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_in_cstring args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                  have hA1NotStuck : a1 ≠ Term.Stuck := by
                    intro hStuck
                    subst a1
                    apply hProg
                    rfl
                  have hA2NotStuck : a2 ≠ Term.Stuck := by
                    intro hStuck
                    subst a2
                    apply hProg
                    cases a1 <;> rfl
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.re_in_cstring
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply
                          (Term.Apply Term.eq
                            (ReInCStringProof.lhs a1 a2))
                          (ReInCStringProof.rhs a1 a2) := by
                    cases hA1 : a1 <;>
                      first | exact False.elim (hA1NotStuck hA1) | all_goals
                        cases hA2 : a2 <;>
                          first | exact False.elim (hA2NotStuck hA2) | rfl
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq
                      (__eo_typeof (ReInCStringProof.lhs a1 a2))
                      (__eo_typeof (ReInCStringProof.rhs a1 a2)) = Term.Bool
                    at hResultTy
                  have hLhsNotStuck :
                      __eo_typeof (ReInCStringProof.lhs a1 a2) ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof (ReInCStringProof.lhs a1 a2))
                      (__eo_typeof (ReInCStringProof.rhs a1 a2))
                      hResultTy).1
                  have hA1Ty : __eo_typeof a1 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_in_re (__eo_typeof a1)
                        (__eo_typeof
                          (Term.Apply (Term.UOp UserOp.str_to_re) a2)) ≠
                      Term.Stuck at hLhsNotStuck
                    exact (ReConstSupport.eo_typeof_str_in_re_args_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof
                        (Term.Apply (Term.UOp UserOp.str_to_re) a2))
                      hLhsNotStuck).1
                  have hStrToReTy :
                      __eo_typeof
                          (Term.Apply (Term.UOp UserOp.str_to_re) a2) =
                        Term.RegLan := by
                    change __eo_typeof_str_in_re (__eo_typeof a1)
                        (__eo_typeof
                          (Term.Apply (Term.UOp UserOp.str_to_re) a2)) ≠
                      Term.Stuck at hLhsNotStuck
                    exact (ReConstSupport.eo_typeof_str_in_re_args_of_ne_stuck
                      (__eo_typeof a1)
                      (__eo_typeof
                        (Term.Apply (Term.UOp UserOp.str_to_re) a2))
                      hLhsNotStuck).2
                  have hA2Ty : __eo_typeof a2 = Term.Apply Term.Seq Term.Char := by
                    change __eo_typeof_str_to_re (__eo_typeof a2) =
                      Term.RegLan at hStrToReTy
                    have hStrToReNotStuck :
                        __eo_typeof_str_to_re (__eo_typeof a2) ≠ Term.Stuck := by
                      rw [hStrToReTy]
                      simp
                    exact ReConstSupport.eo_typeof_str_to_re_eq_seq_char_of_ne_stuck
                      (__eo_typeof a2) hStrToReNotStuck
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_re_in_cstring a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (ReInCStringProof.typed___eo_prog_re_in_cstring_impl
                        a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty)⟩
                    intro _hTrue
                    exact ReInCStringProof.facts___eo_prog_re_in_cstring_impl
                      M hM a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
                  change StepRuleProperties M []
                    (__eo_prog_re_in_cstring a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
