module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_re_mult_eq_reglan_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ =>
      simp [__eo_typeof_re_mult] at h

private theorem smtx_model_eval_re_star_star (v : SmtValue) :
    __smtx_model_eval_re_mult (__smtx_model_eval_re_mult v) =
      __smtx_model_eval_re_mult v := by
  cases v <;> simp [__smtx_model_eval_re_mult, native_re_mult]
  case RegLan r =>
    cases r <;> simp

private theorem typed___eo_prog_re_star_star_impl
    (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
  RuleProofs.eo_has_bool_type (__eo_prog_re_star_star a1) := by
  let lhs := Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)
  let rhs := Term.Apply Term.re_mult a1
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hInnerTranslate :
      __eo_to_smt (Term.Apply Term.re_mult a1) =
        SmtTerm.re_mult (__eo_to_smt a1) := by
    rfl
  have hInnerTyRaw :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.re_mult a1)) = SmtType.RegLan := by
    rw [hInnerTranslate]
    rw [typeof_re_mult_eq]
    simp [hA1SmtTy, native_ite, native_Teq]
  have hLhsTyRaw :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1))) =
        SmtType.RegLan := by
    change __smtx_typeof
      (SmtTerm.re_mult (__eo_to_smt (Term.Apply Term.re_mult a1))) = SmtType.RegLan
    rw [typeof_re_mult_eq]
    simp [hInnerTyRaw, native_ite, native_Teq]
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan := by
    simpa [lhs] using hLhsTyRaw
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    simpa [rhs] using hInnerTyRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hProg :
      __eo_prog_re_star_star a1 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    cases a1 <;> simp [__eo_prog_re_star_star, lhs, rhs] at hA1NotStuck ⊢
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_star_star_impl
    (M : SmtModel) (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
  eo_interprets M (__eo_prog_re_star_star a1) true := by
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hProg :
      __eo_prog_re_star_star a1 =
        Term.Apply
          (Term.Apply Term.eq
            (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)))
          (Term.Apply Term.re_mult a1) := by
    cases a1 <;> simp [__eo_prog_re_star_star] at hA1NotStuck ⊢
  have hBoolEq :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)))
          (Term.Apply Term.re_mult a1)) := by
    rw [← hProg]
    exact typed___eo_prog_re_star_star_impl a1 hA1Trans hA1Ty
  have hOuterTranslate :
      __eo_to_smt (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)) =
        SmtTerm.re_mult (__eo_to_smt (Term.Apply Term.re_mult a1)) := by
    rfl
  have hInnerTranslate :
      __eo_to_smt (Term.Apply Term.re_mult a1) =
        SmtTerm.re_mult (__eo_to_smt a1) := by
    rfl
  have hEvalEq :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1))) =
        __smtx_model_eval M (__eo_to_smt (Term.Apply Term.re_mult a1)) := by
    rw [hOuterTranslate, hInnerTranslate]
    rw [__smtx_model_eval.eq_108, __smtx_model_eval.eq_108]
    exact smtx_model_eval_re_star_star (__smtx_model_eval M (__eo_to_smt a1))
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1))
    (Term.Apply Term.re_mult a1) hBoolEq <| by
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.re_mult a1)))

public theorem cmd_step_re_star_star_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_star_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_star_star args premises ≠ Term.Stuck :=
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
              have hProgEq :
                  __eo_cmd_step_proven s CRule.re_star_star (CArgList.cons a1 CArgList.nil)
                    CIndexList.nil =
                    Term.Apply (Term.Apply Term.eq
                      (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)))
                      (Term.Apply Term.re_mult a1) := by
                cases hA1 : a1 <;> first | exact False.elim (hA1NotStuck hA1) | rfl
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq
                  (__eo_typeof (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)))
                  (__eo_typeof (Term.Apply Term.re_mult a1)) = Term.Bool at hResultTy
              have hRhsNotStuck :
                  __eo_typeof (Term.Apply Term.re_mult a1) ≠ Term.Stuck :=
                (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                  (__eo_typeof (Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)))
                  (__eo_typeof (Term.Apply Term.re_mult a1)) hResultTy).2
              have hA1Ty : __eo_typeof a1 = Term.RegLan := by
                have hTypeNotStuck : __eo_typeof_re_mult (__eo_typeof a1) ≠ Term.Stuck := by
                  change __eo_typeof (Term.Apply Term.re_mult a1) ≠ Term.Stuck
                  exact hRhsNotStuck
                exact eo_typeof_re_mult_eq_reglan_of_ne_stuck (__eo_typeof a1) hTypeNotStuck
              have hProps :
                  StepRuleProperties M (premiseTermList s CIndexList.nil)
                    (__eo_prog_re_star_star a1) := by
                refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_re_star_star_impl a1 hA1Trans hA1Ty)⟩
                intro _hTrue
                exact facts___eo_prog_re_star_star_impl M a1 hA1Trans hA1Ty
              change StepRuleProperties M [] (__eo_prog_re_star_star a1)
              simpa [premiseTermList] using hProps
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
