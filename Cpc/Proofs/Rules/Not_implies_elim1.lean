module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_has_bool_type_imp_left (A B : Term) :
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.imp A) B) ->
  RuleProofs.eo_has_bool_type A := by
  intro hImp
  unfold RuleProofs.eo_has_bool_type at hImp ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool at hImp
  have hNN : term_has_non_none_type (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hImp]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1

/-- Shows that the EO program for `not_implies_elim1` is well typed. -/
theorem typed___eo_prog_not_implies_elim1_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_not_implies_elim1 (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_not_implies_elim1 (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | imp =>
                              exact eo_has_bool_type_imp_left F1 F2
                                (RuleProofs.eo_has_bool_type_not_arg _ hX1Bool)
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

/-- Derives the checker facts exposed by the EO program for `not_implies_elim1`. -/
theorem facts___eo_prog_not_implies_elim1_impl (M : SmtModel) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_not_implies_elim1 (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_not_implies_elim1 (Proof.pf x1)) true := by
  intro hX1True hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply g F2 =>
                  cases g with
                  | Apply h F1 =>
                      cases h with
                      | UOp op' =>
                          cases op' with
                          | imp =>
                              exact RuleProofs.eo_interprets_imp_false_left M F1 F2
                                (RuleProofs.eo_interprets_not_true_implies_false M
                                  (Term.Apply (Term.Apply Term.imp F1) F2) hX1True)
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

public theorem cmd_step_not_implies_elim1_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_implies_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.not_implies_elim1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_implies_elim1 args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.not_implies_elim1 args premises ≠ Term.Stuck :=
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
              have hProgNotImplies :
                  __eo_prog_not_implies_elim1 (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_not_implies_elim1
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_not_implies_elim1 (Proof.pf X1)) true
                exact facts___eo_prog_not_implies_elim1_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgNotImplies
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_not_implies_elim1 (Proof.pf X1))
                    exact typed___eo_prog_not_implies_elim1_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgNotImplies)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
