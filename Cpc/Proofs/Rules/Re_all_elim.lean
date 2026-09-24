module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem typed___eo_prog_re_all_elim :
  RuleProofs.eo_has_bool_type __eo_prog_re_all_elim := by
  change RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply Term.eq Term.re_all)
      (Term.Apply Term.re_mult Term.re_allchar))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    Term.re_all (Term.Apply Term.re_mult Term.re_allchar)
    (by
      change __smtx_typeof SmtTerm.re_all =
        __smtx_typeof (SmtTerm.re_mult SmtTerm.re_allchar)
      rw [__smtx_typeof.eq_106, typeof_re_mult_eq, __smtx_typeof.eq_104]
      native_decide)
    (by
      change __smtx_typeof SmtTerm.re_all ≠ SmtType.None
      rw [__smtx_typeof.eq_106]
      native_decide)

private theorem facts___eo_prog_re_all_elim (M : SmtModel) :
  eo_interprets M __eo_prog_re_all_elim true := by
  change eo_interprets M
    (Term.Apply (Term.Apply Term.eq Term.re_all)
      (Term.Apply Term.re_mult Term.re_allchar)) true
  apply RuleProofs.eo_interprets_eq_of_rel M
    Term.re_all (Term.Apply Term.re_mult Term.re_allchar)
  · exact typed___eo_prog_re_all_elim
  · have hEvalEq :
        __smtx_model_eval M (__eo_to_smt Term.re_all) =
          __smtx_model_eval M (__eo_to_smt (Term.Apply Term.re_mult Term.re_allchar)) := by
      change __smtx_model_eval M SmtTerm.re_all =
        __smtx_model_eval M (SmtTerm.re_mult SmtTerm.re_allchar)
      rw [__smtx_model_eval.eq_106, __smtx_model_eval.eq_108, __smtx_model_eval.eq_104]
      rfl
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.re_mult Term.re_allchar)))

public theorem cmd_step_re_all_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_all_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_all_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_all_elim args premises) :=
by
  intro _hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_all_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
            typed___eo_prog_re_all_elim⟩
          intro _hTrue
          exact facts___eo_prog_re_all_elim M
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
