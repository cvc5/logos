module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_interprets_of_not_false (M : SmtModel) (F : Term) :
  eo_interprets M (Term.Apply Term.not F) false ->
  eo_interprets M F true := by
  intro hNotFalse
  have hNotBool : RuleProofs.eo_has_bool_type (Term.Apply Term.not F) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hNotFalse
  have hFBool : RuleProofs.eo_has_bool_type F :=
    RuleProofs.eo_has_bool_type_not_arg F hNotBool
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hNotFalse
  change smt_interprets M (SmtTerm.not (__eo_to_smt F)) false at hNotFalse
  cases hNotFalse with
  | intro_false _ hEvalNot =>
      rw [__smtx_model_eval.eq_7] at hEvalNot
      cases hEvalF : __smtx_model_eval M (__eo_to_smt F) with
      | NotValue =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Boolean b =>
          cases b with
          | false =>
              exfalso
              simp [hEvalF, __smtx_model_eval_not, SmtEval.native_not] at hEvalNot
          | true =>
              exact RuleProofs.eo_interprets_of_bool_eval M F true hFBool hEvalF
      | Numeral _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Rational _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Binary _ _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Map _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Fun _ _ _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Set _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Seq _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Char _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | UValue _ _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | RegLan _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | DtCons _ _ _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot
      | Apply _ _ =>
          exfalso
          simp [hEvalF, __smtx_model_eval_not] at hEvalNot

/-- Shows that the EO program for `not_not_elim` is well typed. -/
theorem typed___eo_prog_not_not_elim_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_not_not_elim (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_not_not_elim (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply g F =>
                  cases g with
                  | UOp op' =>
                      cases op' with
                      | not =>
                          have hNotFBool : RuleProofs.eo_has_bool_type (Term.Apply Term.not F) :=
                            RuleProofs.eo_has_bool_type_not_arg _ hX1Bool
                          exact RuleProofs.eo_has_bool_type_not_arg F hNotFBool
                      | _ =>
                          simp [__eo_prog_not_not_elim] at hProg
                  | _ =>
                      simp [__eo_prog_not_not_elim] at hProg
              | _ =>
                  simp [__eo_prog_not_not_elim] at hProg
          | _ =>
              simp [__eo_prog_not_not_elim] at hProg
      | _ =>
          simp [__eo_prog_not_not_elim] at hProg
  | _ =>
      simp [__eo_prog_not_not_elim] at hProg

/-- Derives the checker facts exposed by the EO program for `not_not_elim`. -/
theorem facts___eo_prog_not_not_elim_impl (M : SmtModel) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_not_not_elim (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_not_not_elim (Proof.pf x1)) true := by
  intro hX1True hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply g F =>
                  cases g with
                  | UOp op' =>
                      cases op' with
                      | not =>
                          exact eo_interprets_of_not_false M F
                            (RuleProofs.eo_interprets_not_true_implies_false M
                              (Term.Apply Term.not F) hX1True)
                      | _ =>
                          simp [__eo_prog_not_not_elim] at hProg
                  | _ =>
                      simp [__eo_prog_not_not_elim] at hProg
              | _ =>
                  simp [__eo_prog_not_not_elim] at hProg
          | _ =>
              simp [__eo_prog_not_not_elim] at hProg
      | _ =>
          simp [__eo_prog_not_not_elim] at hProg
  | _ =>
      simp [__eo_prog_not_not_elim] at hProg

public theorem cmd_step_not_not_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_not_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_not_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_not_elim args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_not_elim args premises ≠ Term.Stuck :=
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
              have hProgNotNot : __eo_prog_not_not_elim (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_not_elim (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_not_elim (Proof.pf X1)) true
                exact facts___eo_prog_not_not_elim_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgNotNot
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_not_not_elim (Proof.pf X1))
                    exact typed___eo_prog_not_not_elim_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgNotNot)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
