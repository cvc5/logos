module

public import CpcMini.Proofs.RuleSupport.Support
import all CpcMini.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Shows that the EO program for `contra_impl` is well typed. -/
theorem typed___eo_prog_contra_impl (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
by
  intro hX1Bool _hX2Bool hProg
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type x1 hX1Bool
  cases x2 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hEqTerm : __eo_eq x1 x1 = Term.Boolean true := by
              by_cases hStuck : x1 = Term.Stuck
              · exact False.elim (hX1NotStuck hStuck)
              · simp [__eo_eq, native_teq]
            have hContraFalse :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply (Term.UOp UserOp.not) x1)) =
                  Term.Boolean false := by
              rw [__eo_prog_contra, hEqTerm]
              simp [__eo_requires, native_teq, native_ite, native_not, SmtEval.native_not]
            simp [RuleProofs.eo_has_bool_type, hContraFalse, __smtx_typeof]
          · have hEqNe : __eo_eq x1 a ≠ Term.Boolean true := by
              intro hEqTerm
              by_cases hXStuck : x1 = Term.Stuck
              · subst hXStuck
                simp [__eo_eq] at hEqTerm
              · by_cases hAStuck : a = Term.Stuck
                · subst hAStuck
                  simp [__eo_eq] at hEqTerm
                · simp [__eo_eq, native_teq] at hEqTerm
                  exact hEq hEqTerm.symm
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply (Term.UOp UserOp.not) a)) =
                  Term.Stuck := by
              rw [__eo_prog_contra]
              simp [__eo_requires, native_teq, native_ite, hEqNe]
            exact False.elim (hProg hContraStuck)
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_contra]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_contra]))

namespace RuleProofs

/-- Proves correctness of the EO program for `contra`. -/
theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M x2 true ->
  eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true := by
  intro hX1True hX2True hTy
  have hProgNotStuck : __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck := by
    intro hStuck
    simp [eo_has_bool_type, hStuck, __eo_to_smt, __smtx_typeof] at hTy
  cases x2 with
  | Apply f a =>
      cases f with
      | UOp op =>
          cases op with
          | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hX1False : eo_interprets M x1 false :=
              eo_interprets_not_true_implies_false M x1 hX2True
            exact False.elim ((eo_interprets_true_not_false M x1 hX1True) hX1False)
          · exfalso
            have hEq' : a ≠ x1 := by
              simpa [eq_comm] using hEq
            have hx1NotStuck : x1 ≠ Term.Stuck :=
              term_ne_stuck_of_interprets_true M x1 hX1True
            have hAFalse : eo_interprets M a false :=
              eo_interprets_not_true_implies_false M a hX2True
            have hANotStuck : a ≠ Term.Stuck :=
              term_ne_stuck_of_interprets_false M a hAFalse
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply (Term.UOp UserOp.not) a)) =
                  Term.Stuck := by
              simp [__eo_prog_contra, __eo_requires, __eo_eq, native_teq, hEq', native_ite]
            exact hProgNotStuck hContraStuck
          | _ =>
              exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))
      | _ =>
          exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))

end RuleProofs

/-- Proves correctness of the EO program for `contra_impl`. -/
theorem correct___eo_prog_contra_impl
    (M : SmtModel) (_hM : model_wf M) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  exact RuleProofs.correct___eo_prog_contra M x1 x2

/-- Derives the checker facts exposed by the EO program for `contra_impl`. -/
theorem facts___eo_prog_contra_impl
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M x2 true ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true :=
by
  intro hX1True hX2True hProg
  let hX1Bool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hX1True
  let hX2Bool : RuleProofs.eo_has_bool_type x2 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x2 hX2True
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
    typed___eo_prog_contra_impl x1 x2 hX1Bool hX2Bool hProg
  exact correct___eo_prog_contra_impl M hM x1 x2 hX1True hX2True hBool

/-- Packages the properties required for the `contra` checker step. -/
public theorem cmd_step_contra_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.contra args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.contra args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.contra args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons n1 premises =>
          cases premises with
          | nil =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
          | cons n2 premises =>
              cases premises with
              | nil =>
                  let X1 := __eo_state_proven_nth s n1
                  let X2 := __eo_state_proven_nth s n2
                  constructor
                  · intro hEvidence
                    exact facts___eo_prog_contra_impl M hM X1 X2
                      (hEvidence.true_here X1 (by simp [X1, premiseTermList]))
                      (hEvidence.true_here X2 (by simp [X2, premiseTermList]))
                      (by simpa [X1, X2, premiseTermList, __eo_cmd_step_proven] using hProg)
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (typed___eo_prog_contra_impl X1 X2
                        (hPremisesBool X1 (by simp [X1, premiseTermList]))
                        (hPremisesBool X2 (by simp [X2, premiseTermList]))
                        (by simpa [X1, X2, premiseTermList, __eo_cmd_step_proven] using hProg))
              | cons n3 premises =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
