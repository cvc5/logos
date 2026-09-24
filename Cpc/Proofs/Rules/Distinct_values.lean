module

public import Cpc.Proofs.RuleSupport.DistinctTermsSupport
import all Cpc.Proofs.RuleSupport.DistinctTermsSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_eq_true_eq {a b : Term} :
    __eo_eq a b = Term.Boolean true -> a = b := by
  intro h
  cases a <;> cases b <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals simpa [eq_comm, and_assoc] using h

private theorem eo_typeof_eq_bool_operands_eq {A B : Term} :
    __eo_typeof_eq A B = Term.Bool -> A = B := by
  intro h
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp [__eo_typeof_eq] at h hA
  have hDef :
      __eo_typeof_eq A B =
        __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool := by
    cases A <;> cases B <;> simp [__eo_typeof_eq] at hA hB ⊢
  have hReq :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool = Term.Bool := by
    simpa [hDef] using h
  have hReqNe :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    rw [hReq]
    intro hBad
    cases hBad
  exact eo_eq_true_eq (_root_.eo_requires_arg_eq_of_ne_stuck hReqNe)

private theorem eo_typeof_not_eq_bool_operands_eq {a b : Term} :
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
      Term.Bool ->
    __eo_typeof a = __eo_typeof b := by
  intro h
  change __eo_typeof_not
      (__eo_typeof_eq (__eo_typeof a) (__eo_typeof b)) = Term.Bool at h
  cases hEqTy : __eo_typeof_eq (__eo_typeof a) (__eo_typeof b) <;>
    simp [__eo_typeof_not, hEqTy] at h
  exact eo_typeof_eq_bool_operands_eq hEqTy

private theorem eq_has_bool_type_of_not_eq_typeof_bool
    (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  intro haTrans hbTrans hTy
  have hEoTy : __eo_typeof a = __eo_typeof b :=
    eo_typeof_not_eq_bool_operands_eq hTy
  have haSmtTy :
      __smtx_typeof (__eo_to_smt a) = __eo_to_smt_type (__eo_typeof a) :=
    (TranslationProofs.eo_to_smt_type_typeof_of_smt_type a rfl haTrans).symm
  have hbSmtTy :
      __smtx_typeof (__eo_to_smt b) = __eo_to_smt_type (__eo_typeof b) :=
    (TranslationProofs.eo_to_smt_type_typeof_of_smt_type b rfl hbTrans).symm
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [haSmtTy, hbSmtTy, hEoTy]
  · exact haTrans

private theorem prog_distinct_values_shape_of_ne_stuck {a b : Term} :
    __eo_prog_distinct_values a b ≠ Term.Stuck ->
    __eo_ite (__eo_eq a b) (Term.Boolean false)
        (__are_distinct_terms_type a b (__eo_typeof a)) =
      Term.Boolean true ∧
    __eo_prog_distinct_values a b =
      Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  intro hProg
  cases a <;> cases b <;>
    try
      (change Term.Stuck ≠ Term.Stuck at hProg
       exact False.elim (hProg rfl))
  all_goals
    constructor
    · exact _root_.eo_requires_arg_eq_of_ne_stuck hProg
    · exact _root_.eo_requires_result_eq_of_ne_stuck hProg

private theorem prog_distinct_values_shape_of_typeof_bool {a b : Term} :
    __eo_typeof (__eo_prog_distinct_values a b) = Term.Bool ->
    __eo_ite (__eo_eq a b) (Term.Boolean false)
        (__are_distinct_terms_type a b (__eo_typeof a)) =
      Term.Boolean true ∧
    __eo_prog_distinct_values a b =
      Term.Apply (Term.UOp UserOp.not)
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) := by
  intro hTy
  exact prog_distinct_values_shape_of_ne_stuck
    (term_ne_stuck_of_typeof_bool hTy)

private theorem typed___eo_prog_distinct_values_impl
    (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_typeof (__eo_prog_distinct_values a b) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_distinct_values a b) := by
  intro haTrans hbTrans hTy
  rcases prog_distinct_values_shape_of_typeof_bool hTy with
    ⟨_hGuard, hProgEq⟩
  have hBodyTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    eq_has_bool_type_of_not_eq_typeof_bool a b haTrans hbTrans hBodyTy
  rw [hProgEq]
  exact RuleProofs.eo_has_bool_type_not_of_bool_arg
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hEqBool

private theorem facts___eo_prog_distinct_values_of_eval_eq_false
    (M : SmtModel) (a b : Term) :
    RuleProofs.eo_has_smt_translation a ->
    RuleProofs.eo_has_smt_translation b ->
    __eo_typeof (__eo_prog_distinct_values a b) = Term.Bool ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) = SmtValue.Boolean false ->
    eo_interprets M (__eo_prog_distinct_values a b) true := by
  intro haTrans hbTrans hTy hEvalEqFalse
  rcases prog_distinct_values_shape_of_typeof_bool hTy with
    ⟨_hGuard, hProgEq⟩
  have hBodyTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    eq_has_bool_type_of_not_eq_typeof_bool a b haTrans hbTrans hBodyTy
  have hEqFalse :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) false := by
    apply RuleProofs.eo_interprets_of_bool_eval M
    · exact hEqBool
    · change __smtx_model_eval M
          (SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b)) =
        SmtValue.Boolean false
      simp [__smtx_model_eval, hEvalEqFalse]
  rw [hProgEq]
  exact RuleProofs.eo_interprets_not_of_false M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hEqFalse

public theorem cmd_step_distinct_values_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_values args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.distinct_values args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_values args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.distinct_values args premises ≠
        Term.Stuck :=
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              cases premises with
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | nil =>
                  let A1 := a1
                  let A2 := a2
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons A1 (CArgList.cons A2 CArgList.nil)) := by
                    simpa [cmdTranslationOk, A1, A2] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                    simpa [A1, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hArgsTrans.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation A2 := by
                    simpa [A2, RuleProofs.eo_has_smt_translation,
                      eoHasSmtTranslation] using hArgsTrans.2.1
                  change __eo_typeof (__eo_prog_distinct_values A1 A2) =
                    Term.Bool at hResultTy
                  rcases prog_distinct_values_shape_of_typeof_bool hResultTy with
                    ⟨hGuardTrue, _hProgEq⟩
                  rcases eo_ite_eq_false_guard_true hGuardTrue with
                    ⟨hEqFalse, hDistinct⟩
                  have hEvalEqFalse :
                      __smtx_model_eval_eq
                        (__smtx_model_eval M (__eo_to_smt A1))
                        (__smtx_model_eval M (__eo_to_smt A2)) =
                        SmtValue.Boolean false := by
                    exact are_distinct_terms_type_model_eval_eq_false
                      M hM A1 A2 hA1Trans hA2Trans hEqFalse hDistinct
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_distinct_values A1 A2) true
                    exact facts___eo_prog_distinct_values_of_eval_eq_false
                      M A1 A2 hA1Trans hA2Trans hResultTy hEvalEqFalse
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_distinct_values A1 A2)
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                      (__eo_prog_distinct_values A1 A2)
                      (typed___eo_prog_distinct_values_impl
                        A1 A2 hA1Trans hA2Trans hResultTy)
