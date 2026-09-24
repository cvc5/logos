module

public import Cpc.Proofs.RuleSupport.CnfSupport
import all Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_bool_impl_elim_eq_of_ne_stuck (t1 s1 : Term) :
    t1 ≠ Term.Stuck ->
    s1 ≠ Term.Stuck ->
    __eo_prog_bool_impl_elim t1 s1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply Term.imp t1) s1))
        (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t1))
          (Term.Apply (Term.Apply Term.or s1) (Term.Boolean false))) := by
  intro hT1 hS1
  cases t1 <;> cases s1 <;> simp [__eo_prog_bool_impl_elim] at hT1 hS1 ⊢

private theorem typeof_args_of_prog_bool_impl_elim_bool (t1 s1 : Term) :
    __eo_typeof (__eo_prog_bool_impl_elim t1 s1) = Term.Bool ->
    __eo_typeof t1 = Term.Bool ∧ __eo_typeof s1 = Term.Bool := by
  intro hTy
  by_cases hT1 : t1 = Term.Stuck
  · subst t1
    change __eo_typeof Term.Stuck = Term.Bool at hTy
    have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
      native_decide
    exact False.elim (hStuckTy hTy)
  · by_cases hS1 : s1 = Term.Stuck
    · subst s1
      simp [__eo_prog_bool_impl_elim] at hTy
      have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
        native_decide
      exact False.elim (hStuckTy hTy)
    · rw [prog_bool_impl_elim_eq_of_ne_stuck t1 s1 hT1 hS1] at hTy
      change __eo_typeof_eq
        (__eo_typeof (Term.Apply (Term.Apply Term.imp t1) s1))
        (__eo_typeof (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t1))
          (Term.Apply (Term.Apply Term.or s1) (Term.Boolean false)))) =
          Term.Bool at hTy
      change __eo_typeof_eq
        (__eo_typeof_or (__eo_typeof t1) (__eo_typeof s1))
        (__eo_typeof_or (__eo_typeof_not (__eo_typeof t1))
          (__eo_typeof_or (__eo_typeof s1) Term.Bool)) = Term.Bool at hTy
      cases hTT : __eo_typeof t1 <;> cases hTS : __eo_typeof s1 <;>
        simp [__eo_typeof_eq, __eo_typeof_or, __eo_typeof_not, __eo_requires, __eo_eq,
          native_ite, native_teq, native_not, hTT, hTS] at hTy ⊢

private theorem typed___eo_prog_bool_impl_elim_impl (t1 s1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  __eo_typeof (__eo_prog_bool_impl_elim t1 s1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_bool_impl_elim t1 s1) := by
  intro hT1Trans hS1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  rcases typeof_args_of_prog_bool_impl_elim_bool t1 s1 hResultTy with
    ⟨hT1Type, hS1Type⟩
  have hT1Bool : RuleProofs.eo_has_bool_type t1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Bool (__eo_to_smt t1) rfl hT1Trans hT1Type
  have hS1Bool : RuleProofs.eo_has_bool_type s1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s1 Term.Bool (__eo_to_smt s1) rfl hS1Trans hS1Type
  have hLeftBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.imp t1) s1) :=
    CnfSupport.eo_has_bool_type_imp_of_bool_args t1 s1 hT1Bool hS1Bool
  have hNotT1Bool : RuleProofs.eo_has_bool_type (Term.Apply Term.not t1) :=
    RuleProofs.eo_has_bool_type_not_of_bool_arg t1 hT1Bool
  have hInnerOrBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or s1) (Term.Boolean false)) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args s1 (Term.Boolean false) hS1Bool
      RuleProofs.eo_has_bool_type_false
  have hRightBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t1))
          (Term.Apply (Term.Apply Term.or s1) (Term.Boolean false))) :=
    RuleProofs.eo_has_bool_type_or_of_bool_args (Term.Apply Term.not t1) _
      hNotT1Bool hInnerOrBool
  rw [prog_bool_impl_elim_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLeftBool.trans hRightBool.symm)
    (by
      rw [hLeftBool]
      decide)

private theorem facts___eo_prog_bool_impl_elim_impl
    (M : SmtModel) (hM : model_wf M) (t1 s1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation s1 ->
  __eo_typeof (__eo_prog_bool_impl_elim t1 s1) = Term.Bool ->
  eo_interprets M (__eo_prog_bool_impl_elim t1 s1) true := by
  intro hT1Trans hS1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hS1NotStuck : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1Trans
  have hProgBool : RuleProofs.eo_has_bool_type (__eo_prog_bool_impl_elim t1 s1) :=
    typed___eo_prog_bool_impl_elim_impl t1 s1 hT1Trans hS1Trans hResultTy
  rcases typeof_args_of_prog_bool_impl_elim_bool t1 s1 hResultTy with
    ⟨hT1Type, hS1Type⟩
  have hT1Bool : RuleProofs.eo_has_bool_type t1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Bool (__eo_to_smt t1) rfl hT1Trans hT1Type
  have hS1Bool : RuleProofs.eo_has_bool_type s1 :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      s1 Term.Bool (__eo_to_smt s1) rfl hS1Trans hS1Type
  rw [prog_bool_impl_elim_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [prog_bool_impl_elim_eq_of_ne_stuck t1 s1 hT1NotStuck hS1NotStuck]
      using hProgBool
  · rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t1 hT1Bool with
      ⟨bt, hEvalT1⟩
    rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM s1 hS1Bool with
      ⟨bs, hEvalS1⟩
    rw [show __eo_to_smt (Term.Apply (Term.Apply Term.imp t1) s1) =
      SmtTerm.imp (__eo_to_smt t1) (__eo_to_smt s1) by rfl]
    rw [show __eo_to_smt
      (Term.Apply (Term.Apply Term.or (Term.Apply Term.not t1))
        (Term.Apply (Term.Apply Term.or s1) (Term.Boolean false))) =
      SmtTerm.or (SmtTerm.not (__eo_to_smt t1))
        (SmtTerm.or (__eo_to_smt s1) (SmtTerm.Boolean false)) by rfl]
    simp only [__smtx_model_eval.eq_1, __smtx_model_eval.eq_7,
      __smtx_model_eval.eq_8, __smtx_model_eval.eq_10, hEvalT1, hEvalS1]
    cases bt <;> cases bs <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq,
        __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not, native_veq,
        SmtEval.native_or, SmtEval.native_not]

public theorem cmd_step_bool_impl_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_impl_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_impl_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_impl_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_impl_elim args premises ≠ Term.Stuck :=
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
                  have hATransPair :
                      RuleProofs.eo_has_smt_translation a1 ∧
                        RuleProofs.eo_has_smt_translation a2 ∧ True := by
                    simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
                  have hA2Trans : RuleProofs.eo_has_smt_translation a2 := hATransPair.2.1
                  change __eo_typeof (__eo_prog_bool_impl_elim a1 a2) = Term.Bool
                    at hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    change eo_interprets M (__eo_prog_bool_impl_elim a1 a2) true
                    exact facts___eo_prog_bool_impl_elim_impl M hM a1 a2 hA1Trans
                      hA2Trans hResultTy
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_bool_impl_elim_impl a1 a2 hA1Trans hA2Trans
                        hResultTy)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
