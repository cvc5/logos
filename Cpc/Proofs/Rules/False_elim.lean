module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_has_bool_type_false :
  RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  change __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by
    rfl]
  rw [__smtx_typeof.eq_1]

private theorem eo_has_bool_type_eq_left (A B : Term) :
  RuleProofs.eo_has_bool_type B ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq A) B) ->
  RuleProofs.eo_has_bool_type A := by
  intro hBBool hEqBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type A B hEqBool with
    ⟨hTy, _hNonNone⟩
  exact hTy.trans hBBool

/-- Shows that the EO program for `false_elim` is well typed. -/
theorem typed___eo_prog_false_elim_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_false_elim (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_false_elim (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f a =>
      cases a with
      | Boolean v =>
          cases v with
          | false =>
              cases f with
              | Apply g b =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          simpa [__eo_prog_false_elim] using
                            (RuleProofs.eo_has_bool_type_not_of_bool_arg b
                              (eo_has_bool_type_eq_left b (Term.Boolean false)
                                eo_has_bool_type_false hX1Bool))
                      | _ =>
                          simp [__eo_prog_false_elim] at hProg
                  | _ =>
                      simp [__eo_prog_false_elim] at hProg
              | _ =>
                  simp [__eo_prog_false_elim] at hProg
          | true =>
              simp [__eo_prog_false_elim] at hProg
      | _ =>
          simp [__eo_prog_false_elim] at hProg
  | _ =>
      simp [__eo_prog_false_elim] at hProg

/-- Derives the checker facts exposed by the EO program for `false_elim`. -/
theorem facts___eo_prog_false_elim_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_false_elim (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_false_elim (Proof.pf x1)) true := by
  intro hX1True hProg
  cases x1 with
  | Apply f a =>
      cases a with
      | Boolean v =>
          cases v with
          | false =>
              cases f with
              | Apply g b =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          have hEqBool :
                              RuleProofs.eo_has_bool_type
                                (Term.Apply (Term.Apply Term.eq b) (Term.Boolean false)) :=
                            RuleProofs.eo_has_bool_type_of_interprets_true M _ hX1True
                          have hBBool : RuleProofs.eo_has_bool_type b :=
                            eo_has_bool_type_eq_left b (Term.Boolean false)
                              eo_has_bool_type_false hEqBool
                          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM b hBBool with
                            ⟨bv, hEvalB⟩
                          have hRel :
                              RuleProofs.smt_value_rel (__smtx_model_eval M (__eo_to_smt b))
                                (SmtValue.Boolean false) := by
                            have hRel' :=
                              RuleProofs.eo_interprets_eq_rel M b (Term.Boolean false) hX1True
                            rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by
                              rfl] at hRel'
                            rw [__smtx_model_eval.eq_1] at hRel'
                            exact hRel'
                          cases bv with
                          | false =>
                              have hBFalse : eo_interprets M b false :=
                                RuleProofs.eo_interprets_of_bool_eval M b false hBBool hEvalB
                              simpa [__eo_prog_false_elim] using
                                (RuleProofs.eo_interprets_not_of_false M b hBFalse)
                          | true =>
                              rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
                              rw [hEvalB] at hRel
                              simp [__smtx_model_eval_eq, native_veq] at hRel
                      | _ =>
                          simp [__eo_prog_false_elim] at hProg
                  | _ =>
                      simp [__eo_prog_false_elim] at hProg
              | _ =>
                  simp [__eo_prog_false_elim] at hProg
          | true =>
              simp [__eo_prog_false_elim] at hProg
      | _ =>
          simp [__eo_prog_false_elim] at hProg
  | _ =>
      simp [__eo_prog_false_elim] at hProg

public theorem cmd_step_false_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.false_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.false_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.false_elim args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.false_elim args premises ≠ Term.Stuck :=
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
              have hProgFalseElim : __eo_prog_false_elim (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_false_elim (Proof.pf (__eo_state_proven_nth s n1)) ≠
                  Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_false_elim (Proof.pf X1)) true
                exact facts___eo_prog_false_elim_impl M hM X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgFalseElim
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_false_elim (Proof.pf X1))
                    exact typed___eo_prog_false_elim_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgFalseElim)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
