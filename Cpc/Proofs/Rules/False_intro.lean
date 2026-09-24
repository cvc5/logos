module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shows that the EO program for `false_intro` is well typed. -/
theorem typed___eo_prog_false_intro_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_false_intro (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_false_intro (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              have hABool : RuleProofs.eo_has_bool_type a :=
                RuleProofs.eo_has_bool_type_not_arg a hX1Bool
              have hATrans : RuleProofs.eo_has_smt_translation a :=
                RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
              change RuleProofs.eo_has_bool_type
                (Term.Apply (Term.Apply Term.eq a) (Term.Boolean false))
              have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := hABool
              have hTyEq :
                  __smtx_typeof (__eo_to_smt a) =
                    __smtx_typeof (__eo_to_smt (Term.Boolean false)) := by
                have hFalseTy : __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
                  change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
                  rw [__smtx_typeof.eq_1]
                exact hATy.trans hFalseTy.symm
              exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type a (Term.Boolean false)
                hTyEq hATrans
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

/-- Derives the checker facts exposed by the EO program for `false_intro`. -/
theorem facts___eo_prog_false_intro_impl (M : SmtModel) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_false_intro (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_false_intro (Proof.pf x1)) true := by
  intro hX1True hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              have hAFalse : eo_interprets M a false :=
                RuleProofs.eo_interprets_not_true_implies_false M a hX1True
              have hBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_prog_false_intro (Proof.pf (Term.Apply Term.not a))) :=
                typed___eo_prog_false_intro_impl (Term.Apply Term.not a)
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hX1True) hProg
              change eo_interprets M (Term.Apply (Term.Apply Term.eq a) (Term.Boolean false)) true
              apply RuleProofs.eo_interprets_eq_of_rel M a (Term.Boolean false)
              · exact hBool
              · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse
                cases hAFalse with
                | intro_false _ hEvalA =>
                    have hFalseEval :
                        __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
                          SmtValue.Boolean false := by
                      change __smtx_model_eval M (SmtTerm.Boolean false) =
                        SmtValue.Boolean false
                      rw [__smtx_model_eval.eq_1]
                    rw [hEvalA, hFalseEval]
                    exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

public theorem cmd_step_false_intro_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.false_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.false_intro args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.false_intro args premises) := by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.false_intro args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgFalseIntro : __eo_prog_false_intro (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_false_intro (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_false_intro (Proof.pf X1)) true
                exact facts___eo_prog_false_intro_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgFalseIntro
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_false_intro (Proof.pf X1))
                    exact typed___eo_prog_false_intro_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgFalseIntro)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
