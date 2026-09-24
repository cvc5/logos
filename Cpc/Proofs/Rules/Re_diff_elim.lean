module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.RuleSupport.RegexSupport
import all Cpc.Proofs.RuleSupport.RegexSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_re_concat_eq_reglan_of_ne_stuck (T U : Term)
    (h : __eo_typeof_re_concat T U ≠ Term.Stuck) :
    T = Term.RegLan ∧ U = Term.RegLan := by
  cases T with
  | UOp opT =>
      cases opT <;> cases U with
      | UOp opU =>
          cases opU <;> simp [__eo_typeof_re_concat] at h ⊢
      | _ =>
          simp [__eo_typeof_re_concat] at h
  | _ =>
      cases U <;> simp [__eo_typeof_re_concat] at h

private theorem smt_value_rel_re_diff_elim (r s : SmtRegLan) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_re_diff (SmtValue.RegLan r) (SmtValue.RegLan s))
      (__smtx_model_eval_re_inter (SmtValue.RegLan r)
        (__smtx_model_eval_re_inter
          (__smtx_model_eval_re_comp (SmtValue.RegLan s))
          (SmtValue.RegLan native_re_all))) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq (native_re_diff r s)
        (native_re_inter r (native_re_inter (native_re_comp s) native_re_all))) =
    SmtValue.Boolean true
  have hExt :
      ∀ str : native_String,
        native_string_valid str = true ->
          RuleProofs.native_str_in_re str (native_re_diff r s) =
            RuleProofs.native_str_in_re str
              (native_re_inter r (native_re_inter (native_re_comp s) native_re_all)) := by
    intro str hValid
    rw [native_re_diff, RuleProofs.native_str_in_re_mk_inter,
      RuleProofs.native_str_in_re_re_inter,
      RuleProofs.native_str_in_re_re_inter,
      RuleProofs.native_str_in_re_mk_comp,
      RuleProofs.native_str_in_re_re_all _ hValid]
    simp [hValid]
  have hExtModel :
      ∀ str : native_String,
        native_string_valid str = true ->
          native_str_in_re str (native_re_diff r s) =
            native_str_in_re str
              (native_re_inter r (native_re_inter (native_re_comp s) native_re_all)) := by
    intro str hValid
    rw [← RuleProofs.native_str_in_re_eq_model str (native_re_diff r s),
      ← RuleProofs.native_str_in_re_eq_model str
        (native_re_inter r (native_re_inter (native_re_comp s) native_re_all))]
    exact hExt str hValid
  simpa [hExtModel]

private theorem typed___eo_prog_re_diff_elim_impl
    (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.RegLan)
    (hA2Ty : __eo_typeof a2 = Term.RegLan) :
    RuleProofs.eo_has_bool_type (__eo_prog_re_diff_elim a1 a2) := by
  let lhs := Term.Apply (Term.Apply Term.re_diff a1) a2
  let comp := Term.Apply Term.re_comp a2
  let inner := Term.Apply (Term.Apply Term.re_inter comp) Term.re_all
  let rhs := Term.Apply (Term.Apply Term.re_inter a1) inner
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
    rw [hA2Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_diff (__eo_to_smt a1) (__eo_to_smt a2)) =
      SmtType.RegLan
    rw [typeof_re_diff_eq]
    simp [hA1SmtTy, hA2SmtTy, native_ite, native_Teq]
  have hCompTy : __smtx_typeof (__eo_to_smt comp) = SmtType.RegLan := by
    change __smtx_typeof (SmtTerm.re_comp (__eo_to_smt a2)) = SmtType.RegLan
    rw [typeof_re_comp_eq]
    simp [hA2SmtTy, native_ite, native_Teq]
  have hInnerTy : __smtx_typeof (__eo_to_smt inner) = SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_inter (__eo_to_smt comp) SmtTerm.re_all) =
      SmtType.RegLan
    rw [typeof_re_inter_eq]
    simp [hCompTy, __smtx_typeof.eq_106, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    change __smtx_typeof
        (SmtTerm.re_inter (__eo_to_smt a1) (__eo_to_smt inner)) =
      SmtType.RegLan
    rw [typeof_re_inter_eq]
    simp [hA1SmtTy, hInnerTy, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by rw [hLhsTy]; simp)
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_diff_elim a1 a2 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_re_diff_elim a1 a2 =
          Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_diff a1) a2))
            (Term.Apply
              (Term.Apply Term.re_inter a1)
              (Term.Apply
                (Term.Apply Term.re_inter (Term.Apply Term.re_comp a2))
                Term.re_all)) := by
      cases hA1 : a1 <;> cases hA2 : a2 <;> first
        | exact False.elim (hA1NotStuck hA1)
        | exact False.elim (hA2NotStuck hA2)
        | rfl
    simpa [lhs, rhs, inner, comp] using hProgRaw
  rw [hProg]
  exact hBoolEq

private theorem facts___eo_prog_re_diff_elim_impl
    (M : SmtModel) (hM : model_wf M) (a1 a2 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA2Trans : RuleProofs.eo_has_smt_translation a2)
    (hA1Ty : __eo_typeof a1 = Term.RegLan)
    (hA2Ty : __eo_typeof a2 = Term.RegLan) :
    eo_interprets M (__eo_prog_re_diff_elim a1 a2) true := by
  let lhs := Term.Apply (Term.Apply Term.re_diff a1) a2
  let comp := Term.Apply Term.re_comp a2
  let inner := Term.Apply (Term.Apply Term.re_inter comp) Term.re_all
  let rhs := Term.Apply (Term.Apply Term.re_inter a1) inner
  have hA1NotStuck : a1 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA1Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA1Ty
  have hA2NotStuck : a2 ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hA2Ty
    have hBad : __eo_typeof Term.Stuck ≠ Term.RegLan := by
      native_decide
    exact hBad hA2Ty
  have hProg :
      __eo_prog_re_diff_elim a1 a2 = Term.Apply (Term.Apply Term.eq lhs) rhs := by
    have hProgRaw :
        __eo_prog_re_diff_elim a1 a2 =
          Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.re_diff a1) a2))
            (Term.Apply
              (Term.Apply Term.re_inter a1)
              (Term.Apply
                (Term.Apply Term.re_inter (Term.Apply Term.re_comp a2))
                Term.re_all)) := by
      cases hA1 : a1 <;> cases hA2 : a2 <;> first
        | exact False.elim (hA1NotStuck hA1)
        | exact False.elim (hA2NotStuck hA2)
        | rfl
    simpa [lhs, rhs, inner, comp] using hProgRaw
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    rw [← hProg]
    exact typed___eo_prog_re_diff_elim_impl a1 a2 hA1Trans hA2Trans hA1Ty hA2Ty
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hA2SmtTy : __smtx_typeof (__eo_to_smt a2) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a2) = __eo_to_smt_type (__eo_typeof a2) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a2 hA2Trans
    rw [hA2Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hA1EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a1)) = SmtType.RegLan := by
    simpa [hA1SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a1) (by
        unfold term_has_non_none_type
        rw [hA1SmtTy]
        simp)
  have hA2EvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a2)) = SmtType.RegLan := by
    simpa [hA2SmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a2) (by
        unfold term_has_non_none_type
        rw [hA2SmtTy]
        simp)
  rcases reglan_value_canonical hA1EvalTy with ⟨r, hEval1⟩
  rcases reglan_value_canonical hA2EvalTy with ⟨s, hEval2⟩
  rw [hProg]
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq <| by
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.re_diff (__eo_to_smt a1) (__eo_to_smt a2)))
      (__smtx_model_eval M
        (SmtTerm.re_inter (__eo_to_smt a1)
          (SmtTerm.re_inter (SmtTerm.re_comp (__eo_to_smt a2)) SmtTerm.re_all)))
    simp [__smtx_model_eval, hEval1, hEval2]
    exact smt_value_rel_re_diff_elim r s

public theorem cmd_step_re_diff_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_diff_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_diff_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_diff_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_diff_elim args premises ≠ Term.Stuck :=
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
                  let lhs := Term.Apply (Term.Apply Term.re_diff a1) a2
                  let comp := Term.Apply Term.re_comp a2
                  let inner := Term.Apply (Term.Apply Term.re_inter comp) Term.re_all
                  let rhs := Term.Apply (Term.Apply Term.re_inter a1) inner
                  have hProgEq :
                      __eo_cmd_step_proven s CRule.re_diff_elim
                        (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                        CIndexList.nil =
                        Term.Apply (Term.Apply Term.eq lhs) rhs := by
                    have hProgEqRaw :
                        __eo_cmd_step_proven s CRule.re_diff_elim
                          (CArgList.cons a1 (CArgList.cons a2 CArgList.nil))
                          CIndexList.nil =
                          Term.Apply
                            (Term.Apply Term.eq
                              (Term.Apply (Term.Apply Term.re_diff a1) a2))
                            (Term.Apply
                              (Term.Apply Term.re_inter a1)
                              (Term.Apply
                                (Term.Apply Term.re_inter
                                  (Term.Apply Term.re_comp a2))
                                Term.re_all)) := by
                      cases hA1 : a1 <;> cases hA2 : a2 <;> first
                        | exact False.elim (hA1NotStuck hA1)
                        | exact False.elim (hA2NotStuck hA2)
                        | rfl
                    simpa [lhs, rhs, inner, comp] using hProgEqRaw
                  rw [hProgEq] at hResultTy
                  change __eo_typeof_eq (__eo_typeof lhs) (__eo_typeof rhs) =
                    Term.Bool at hResultTy
                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy).1
                  have hArgTypes :
                      __eo_typeof a1 = Term.RegLan ∧ __eo_typeof a2 = Term.RegLan := by
                    change __eo_typeof_re_concat (__eo_typeof a1) (__eo_typeof a2) ≠
                      Term.Stuck at hLhsNotStuck
                    exact eo_typeof_re_concat_eq_reglan_of_ne_stuck
                      (__eo_typeof a1) (__eo_typeof a2) hLhsNotStuck
                  have hProps :
                      StepRuleProperties M (premiseTermList s CIndexList.nil)
                        (__eo_prog_re_diff_elim a1 a2) := by
                    refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_re_diff_elim_impl a1 a2 hA1Trans hA2Trans
                        hArgTypes.1 hArgTypes.2)⟩
                    intro _hTrue
                    exact facts___eo_prog_re_diff_elim_impl M hM a1 a2 hA1Trans hA2Trans
                      hArgTypes.1 hArgTypes.2
                  change StepRuleProperties M [] (__eo_prog_re_diff_elim a1 a2)
                  simpa [premiseTermList] using hProps
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
