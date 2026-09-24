module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_eq_refl_eq_of_ne_stuck (t1 : Term) :
    t1 ≠ Term.Stuck ->
    __eo_prog_eq_refl t1 =
      Term.Apply (Term.Apply Term.eq
        (Term.Apply (Term.Apply Term.eq t1) t1)) (Term.Boolean true) := by
  intro hT1
  cases t1 <;> simp [__eo_prog_eq_refl] at hT1 ⊢

private theorem eo_has_bool_type_eq_true_of_bool (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t) (Term.Boolean true)) := by
  intro hBool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t (Term.Boolean true)
    (hBool.trans RuleProofs.eo_has_bool_type_true.symm)
    (by
      rw [hBool]
      decide)

private theorem eo_interprets_eq_true_of_true (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq t) (Term.Boolean true)) true := by
  intro hTrue
  have hBool : RuleProofs.eo_has_bool_type t :=
    RuleProofs.eo_has_bool_type_of_interprets_true M t hTrue
  apply RuleProofs.eo_interprets_eq_of_rel M t (Term.Boolean true)
  · exact eo_has_bool_type_eq_true_of_bool t hBool
  · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue
    cases hTrue with
    | intro_true _ hEval =>
        have hTrueEval :
            __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
              SmtValue.Boolean true := by
          change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
          rw [__smtx_model_eval.eq_1]
        rw [hEval, hTrueEval]
        exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

private theorem typed___eo_prog_eq_refl_impl (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_eq_refl t1) := by
  intro hT1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hInnerBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t1) t1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t1 t1 rfl hT1Trans
  rw [prog_eq_refl_eq_of_ne_stuck t1 hT1NotStuck]
  exact eo_has_bool_type_eq_true_of_bool (Term.Apply (Term.Apply Term.eq t1) t1)
    hInnerBool

private theorem facts___eo_prog_eq_refl_impl
    (M : SmtModel) (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  eo_interprets M (__eo_prog_eq_refl t1) true := by
  intro hT1Trans
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hInnerBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t1) t1) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t1 t1 rfl hT1Trans
  have hInnerTrue :
      eo_interprets M (Term.Apply (Term.Apply Term.eq t1) t1) true :=
    RuleProofs.eo_interprets_eq_of_rel M t1 t1 hInnerBool
      (RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt t1)))
  rw [prog_eq_refl_eq_of_ne_stuck t1 hT1NotStuck]
  exact eo_interprets_eq_true_of_true M (Term.Apply (Term.Apply Term.eq t1) t1)
    hInnerTrue

public theorem cmd_step_eq_refl_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.eq_refl args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_refl args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.eq_refl args premises ≠ Term.Stuck :=
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
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_eq_refl a1) true
                exact facts___eo_prog_eq_refl_impl M a1 hATrans
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_eq_refl_impl a1 hATrans)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
