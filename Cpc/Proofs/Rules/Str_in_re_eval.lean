module

public import Cpc.Proofs.RuleSupport.StrInReEvalSupport
import all Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs
private theorem str_in_re_eval_valid_properties
    (M : SmtModel) (hM : model_wf M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b))
    (hProgNe :
      __eo_prog_str_in_re_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_eval
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b)) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  let side := __str_eval_str_in_re_rec (__str_flatten (__str_nary_intro s)) r
  let checkedSide := __eo_requires (__eo_is_str s) (Term.Boolean true) side
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires checkedSide b body ≠ Term.Stuck at hProgNe
  have hReqEq : checkedSide = b :=
    eo_requires_eq_of_ne_stuck checkedSide b body hProgNe
  have hReqResult : __eo_requires checkedSide b body = body :=
    eo_requires_result_eq_of_ne_stuck checkedSide b body hProgNe
  have hCheckedNe : checkedSide ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck checkedSide b body hProgNe
  have hStrReq : __eo_is_str s = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_str s) (Term.Boolean true) side hCheckedNe
  have hCheckedResult : checkedSide = side :=
    eo_requires_result_eq_of_ne_stuck (__eo_is_str s) (Term.Boolean true) side
      hCheckedNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_str s) (Term.Boolean true)
      side hCheckedNe
  have hSideEqB : side = b := by
    rw [hCheckedResult] at hReqEq
    exact hReqEq
  rcases eo_is_str_eq_true_cases s hStrReq with ⟨str, rfl⟩
  subst b
  change StepRuleProperties M []
    (__eo_requires checkedSide side body)
  rw [hSideEqB, hReqResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    exact hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn side hEqTrans with
    ⟨hStrInTrans, _hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation (Term.String str) r (by
      simpa [strIn] using hStrInTrans) with
    ⟨hSTy, hRTy⟩
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  have hLeftEval :
      __smtx_model_eval M (__eo_to_smt strIn) =
        SmtValue.Boolean (native_str_in_re str rv) := by
    exact smtx_model_eval_str_in_re_string M str r rv hREval
  have hSideEval :
      __smtx_model_eval M (__eo_to_smt side) =
    SmtValue.Boolean (native_str_in_re str rv) := by
    exact smtx_model_eval_str_in_re_eval_side M hM str r side rv hSTy hRTy
      hREval rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by exact hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool <| by
    rw [hLeftEval, hSideEval]
    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean (native_str_in_re str rv))

end RuleProofs

public theorem cmd_step_str_in_re_eval_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_eval args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_eval args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_eval args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp r =>
                                  cases inApp with
                                  | Apply inOp str =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              have hProps :=
                                                RuleProofs.str_in_re_eval_valid_properties
                                                  M hM str r b (by
                                                    simpa using hA1Trans) (by
                                                    change
                                                      __eo_prog_str_in_re_eval
                                                        (Term.Apply
                                                          (Term.Apply (Term.UOp UserOp.eq)
                                                            (Term.Apply
                                                              (Term.Apply
                                                                (Term.UOp UserOp.str_in_re) str) r)) b) ≠
                                                        Term.Stuck at hProg
                                                    exact hProg)
                                              change StepRuleProperties M []
                                                (__eo_prog_str_in_re_eval
                                                  (Term.Apply
                                                    (Term.Apply (Term.UOp UserOp.eq)
                                                      (Term.Apply
                                                        (Term.Apply
                                                          (Term.UOp UserOp.str_in_re) str) r)) b))
                                              simpa [premiseTermList] using hProps
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
