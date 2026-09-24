module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_or_eq (A B : Term) :
  __eo_to_smt (Term.Apply (Term.Apply Term.or A) B) =
    SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_has_bool_type_false :
  RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  unfold RuleProofs.eo_has_bool_type
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by rfl]
  rw [__smtx_typeof.eq_1]

private theorem eo_has_bool_type_or_of_bool_args (A B : Term) :
  RuleProofs.eo_has_bool_type A ->
  RuleProofs.eo_has_bool_type B ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.or A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  rw [eo_to_smt_or_eq A B, typeof_or_eq]
  simp [hA, hB, native_ite, native_Teq]

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

private theorem eo_has_bool_type_imp_right (A B : Term) :
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.imp A) B) ->
  RuleProofs.eo_has_bool_type B := by
  intro hImp
  unfold RuleProofs.eo_has_bool_type at hImp ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool at hImp
  have hNN : term_has_non_none_type (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hImp]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2

private theorem eo_interprets_or_left_intro
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
  eo_interprets M A true ->
  RuleProofs.eo_has_bool_type B ->
  eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true := by
  intro hATrue hBBool
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_of_interprets_true M A hATrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue ⊢
  rw [eo_to_smt_or_eq A B]
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with ⟨b, hEvalB⟩
  cases hATrue with
  | intro_true _ hEvalA =>
      refine smt_interprets.intro_true M
        (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · simpa [RuleProofs.eo_has_bool_type, eo_to_smt_or_eq] using
          (eo_has_bool_type_or_of_bool_args A B hABool hBBool)
      · rw [__smtx_model_eval.eq_8]
        rw [hEvalA, hEvalB]
        simp [__smtx_model_eval_or, SmtEval.native_or]

private theorem eo_interprets_or_right_intro
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
  RuleProofs.eo_has_bool_type A ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true := by
  intro hABool hBTrue
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_of_interprets_true M B hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBTrue ⊢
  rw [eo_to_smt_or_eq A B]
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with ⟨a, hEvalA⟩
  cases hBTrue with
  | intro_true _ hEvalB =>
      refine smt_interprets.intro_true M
        (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) ?_ ?_
      · simpa [RuleProofs.eo_has_bool_type, eo_to_smt_or_eq] using
          (eo_has_bool_type_or_of_bool_args A B hABool hBBool)
      · rw [__smtx_model_eval.eq_8]
        rw [hEvalA, hEvalB]
        cases a <;> simp [__smtx_model_eval_or, SmtEval.native_or]

/-- Shows that the EO program for `implies_elim` is well typed. -/
theorem typed___eo_prog_implies_elim_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_implies_elim (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_implies_elim (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | imp =>
                  have hF1Bool : RuleProofs.eo_has_bool_type F1 :=
                    eo_has_bool_type_imp_left F1 F2 hX1Bool
                  have hF2Bool : RuleProofs.eo_has_bool_type F2 :=
                    eo_has_bool_type_imp_right F1 F2 hX1Bool
                  have hInnerBool :
                      RuleProofs.eo_has_bool_type
                        (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)) :=
                    eo_has_bool_type_or_of_bool_args F2 (Term.Boolean false)
                      hF2Bool eo_has_bool_type_false
                  exact eo_has_bool_type_or_of_bool_args
                    (Term.Apply Term.not F1)
                    (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))
                    (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                    hInnerBool
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

/-- Derives the checker facts exposed by the EO program for `implies_elim`. -/
theorem facts___eo_prog_implies_elim_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_implies_elim (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_implies_elim (Proof.pf x1)) true := by
  intro hX1True hProg
  cases x1 with
  | Apply f F2 =>
      cases f with
      | Apply g F1 =>
          cases g with
          | UOp op =>
              cases op with
              | imp =>
                  have hImpBool : RuleProofs.eo_has_bool_type
                      (Term.Apply (Term.Apply Term.imp F1) F2) :=
                    RuleProofs.eo_has_bool_type_of_interprets_true M
                      (Term.Apply (Term.Apply Term.imp F1) F2) hX1True
                  have hF1Bool : RuleProofs.eo_has_bool_type F1 :=
                    eo_has_bool_type_imp_left F1 F2 hImpBool
                  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM F1 hF1Bool with
                    ⟨b, hEvalF1⟩
                  cases b with
                  | false =>
                      have hF1False : eo_interprets M F1 false :=
                        RuleProofs.eo_interprets_of_bool_eval M F1 false hF1Bool hEvalF1
                      have hInnerBool :
                          RuleProofs.eo_has_bool_type
                            (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)) := by
                        have hF2Bool : RuleProofs.eo_has_bool_type F2 :=
                          eo_has_bool_type_imp_right F1 F2 hImpBool
                        exact eo_has_bool_type_or_of_bool_args F2 (Term.Boolean false)
                          hF2Bool eo_has_bool_type_false
                      exact eo_interprets_or_left_intro M hM
                        (Term.Apply Term.not F1)
                        (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))
                        (RuleProofs.eo_interprets_not_of_false M F1 hF1False)
                        hInnerBool
                  | true =>
                      have hF1True : eo_interprets M F1 true :=
                        RuleProofs.eo_interprets_of_bool_eval M F1 true hF1Bool hEvalF1
                      have hF2True : eo_interprets M F2 true :=
                        RuleProofs.eo_interprets_imp_elim M F1 F2 hX1True hF1True
                      have hInnerTrue :
                          eo_interprets M
                            (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false)) true :=
                        eo_interprets_or_left_intro M hM F2 (Term.Boolean false)
                          hF2True eo_has_bool_type_false
                      exact eo_interprets_or_right_intro M hM
                        (Term.Apply Term.not F1)
                        (Term.Apply (Term.Apply Term.or F2) (Term.Boolean false))
                        (RuleProofs.eo_has_bool_type_not_of_bool_arg F1 hF1Bool)
                        hInnerTrue
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

public theorem cmd_step_implies_elim_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.implies_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.implies_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.implies_elim args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.implies_elim args premises ≠ Term.Stuck :=
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
              have hProgImplies :
                  __eo_prog_implies_elim (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_implies_elim
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_implies_elim (Proof.pf X1)) true
                exact facts___eo_prog_implies_elim_impl M hM X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgImplies
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_implies_elim (Proof.pf X1))
                    exact typed___eo_prog_implies_elim_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgImplies)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
