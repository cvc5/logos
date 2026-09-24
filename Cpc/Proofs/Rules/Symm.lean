module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shows that the EO program for `symm_impl` is well typed. -/
theorem typed___eo_prog_symm_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) := by
  intro hXBool hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | Apply g b =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  change RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq a) b)
                  exact RuleProofs.eo_has_bool_type_eq_symm b a hXBool
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply f2 a2 =>
                  cases f2 with
                  | Apply g2 b2 =>
                      cases g2 with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply Term.eq b2) a2) :=
                                RuleProofs.eo_has_bool_type_not_arg
                                  (Term.Apply (Term.Apply Term.eq b2) a2) hXBool
                              have hSymmEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply Term.eq a2) b2) :=
                                RuleProofs.eo_has_bool_type_eq_symm b2 a2 hEqBool
                              change RuleProofs.eo_has_bool_type
                                (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq a2) b2))
                              exact RuleProofs.eo_has_bool_type_not_of_bool_arg
                                (Term.Apply (Term.Apply Term.eq a2) b2) hSymmEqBool
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

/-- Establishes an equality relating `eo_interprets` and `symm_true`. -/
private theorem eo_interprets_eq_symm_true (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq y) x) true := by
  intro hEqTrue
  have hTy :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq y) x) :=
    RuleProofs.eo_has_bool_type_eq_symm x y
      (RuleProofs.eo_has_bool_type_of_interprets_true M _ hEqTrue)
  exact RuleProofs.eo_interprets_eq_of_rel M y x hTy
    (RuleProofs.smt_value_rel_symm _ _
      (RuleProofs.eo_interprets_eq_rel M x y hEqTrue))

/-- Proves correctness of the EO program for `symm_impl`. -/
theorem correct___eo_prog_symm_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) ->
  eo_interprets M (__eo_prog_symm (Proof.pf x1)) true := by
  intro hXTrue hTy
  have hProgNotStuck : __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _ hTy
  cases x1 with
  | Apply f a =>
      cases f with
      | Apply g b =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  change eo_interprets M (Term.Apply (Term.Apply Term.eq a) b) true
                  exact eo_interprets_eq_symm_true M b a hXTrue
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProgNotStuck
                  exact False.elim (hProgNotStuck rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProgNotStuck
              exact False.elim (hProgNotStuck rfl)
      | UOp op =>
          cases op with
          | not =>
              cases a with
              | Apply f2 a2 =>
                  cases f2 with
                  | Apply g2 b2 =>
                      cases g2 with
                      | UOp op' =>
                          cases op' with
                          | eq =>
                              have hOrigEqFalse :
                                  eo_interprets M (Term.Apply (Term.Apply Term.eq b2) a2) false :=
                                RuleProofs.eo_interprets_not_true_implies_false M _ hXTrue
                              have hOrigEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply Term.eq b2) a2) :=
                                RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrigEqFalse
                              have hSymmEqBool :
                                  RuleProofs.eo_has_bool_type
                                    (Term.Apply (Term.Apply Term.eq a2) b2) :=
                                RuleProofs.eo_has_bool_type_eq_symm b2 a2 hOrigEqBool
                              rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM
                                  (Term.Apply (Term.Apply Term.eq a2) b2) hSymmEqBool with
                                ⟨b, hEval⟩
                              cases b with
                              | false =>
                                  have hSymmEqFalse :
                                      eo_interprets M
                                        (Term.Apply (Term.Apply Term.eq a2) b2) false :=
                                    RuleProofs.eo_interprets_of_bool_eval M
                                      (Term.Apply (Term.Apply Term.eq a2) b2) false
                                      hSymmEqBool hEval
                                  change eo_interprets M
                                    (Term.Apply Term.not
                                      (Term.Apply (Term.Apply Term.eq a2) b2)) true
                                  exact RuleProofs.eo_interprets_not_of_false M
                                    (Term.Apply (Term.Apply Term.eq a2) b2) hSymmEqFalse
                              | true =>
                                  have hSymmEqTrue :
                                      eo_interprets M
                                        (Term.Apply (Term.Apply Term.eq a2) b2) true :=
                                    RuleProofs.eo_interprets_of_bool_eval M
                                      (Term.Apply (Term.Apply Term.eq a2) b2) true
                                      hSymmEqBool hEval
                                  have hOrigEqTrue :
                                      eo_interprets M
                                        (Term.Apply (Term.Apply Term.eq b2) a2) true :=
                                    eo_interprets_eq_symm_true M a2 b2 hSymmEqTrue
                                  exact False.elim
                                    ((RuleProofs.eo_interprets_true_not_false M _ hOrigEqTrue)
                                      hOrigEqFalse)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProgNotStuck
                              exact False.elim (hProgNotStuck rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProgNotStuck
                          exact False.elim (hProgNotStuck rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProgNotStuck
                      exact False.elim (hProgNotStuck rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProgNotStuck
                  exact False.elim (hProgNotStuck rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProgNotStuck
              exact False.elim (hProgNotStuck rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProgNotStuck
          exact False.elim (hProgNotStuck rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProgNotStuck
      exact False.elim (hProgNotStuck rfl)

/-- Derives the checker facts exposed by the EO program for `symm_impl`. -/
theorem facts___eo_prog_symm_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_symm (Proof.pf x1)) true := by
  intro hXTrue hProg
  let hXBool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hXTrue
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
    typed___eo_prog_symm_impl x1 hXBool hProg
  exact correct___eo_prog_symm_impl M hM x1 hXTrue hBool

public theorem cmd_step_symm_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.symm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.symm args premises) := by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.symm args premises ≠ Term.Stuck :=
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
              let X := __eo_state_proven_nth s n1
              have hProgSymm : __eo_prog_symm (Proof.pf X) ≠ Term.Stuck := by
                change __eo_prog_symm (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_symm (Proof.pf X)) true
                exact facts___eo_prog_symm_impl M hM X
                  (hTrue X (by simp [X, premiseTermList]))
                  hProgSymm
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf X))
                    exact typed___eo_prog_symm_impl X
                      (hPremisesBool X (by simp [X, premiseTermList]))
                      hProgSymm)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
