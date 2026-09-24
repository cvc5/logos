module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.RuleSupport.TrueElimSupport
import all Cpc.Proofs.RuleSupport.TrueElimSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_has_bool_type_eq_right (A B : Term) :
  RuleProofs.eo_has_bool_type A ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq A) B) ->
  RuleProofs.eo_has_bool_type B := by
  intro hABool hEqBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type A B hEqBool with
    ⟨hTy, _hNonNone⟩
  exact hTy.symm.trans hABool

private theorem eq_of_requires_eq_true_not_stuck (x1 A B : Term) :
  __eo_requires (__eo_eq x1 A) (Term.Boolean true) B ≠ Term.Stuck ->
  A = x1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  have hReq : __eo_eq x1 A = Term.Boolean true := hProg'.1
  by_cases hx : x1 = Term.Stuck
  · subst hx
    simp [__eo_eq] at hReq
  · by_cases hA : A = Term.Stuck
    · subst hA
      simp [__eo_eq] at hReq
    · have hDec : native_teq A x1 = true := by
        simpa [__eo_eq, hx, hA] using hReq
      simpa [native_teq] using hDec

private theorem prog_eq_resolve_eq_rhs_of_not_stuck (x B : Term) :
  x ≠ Term.Stuck ->
  __eo_prog_eq_resolve (Proof.pf x) (Proof.pf (Term.Apply (Term.Apply Term.eq x) B)) = B := by
  intro hX
  cases x <;> simp [__eo_prog_eq_resolve, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not, SmtEval.native_not] at hX ⊢

/-- Shows that the EO program for `eq_resolve` is well typed. -/
theorem typed___eo_prog_eq_resolve_impl (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2)) := by
  intro hX1Bool hX2Bool hProg
  cases x2 with
  | Apply f B =>
      cases f with
      | Apply g A =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  change __eo_requires (__eo_eq x1 A) (Term.Boolean true) B ≠ Term.Stuck at hProg
                  have hEq : A = x1 := eq_of_requires_eq_true_not_stuck x1 A B hProg
                  subst A
                  have hX1NotStuck : x1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_bool_type x1 hX1Bool
                  rw [prog_eq_resolve_eq_rhs_of_not_stuck x1 B hX1NotStuck]
                  exact eo_has_bool_type_eq_right x1 B hX1Bool hX2Bool
              | _ =>
                  simp [__eo_prog_eq_resolve] at hProg
          | _ =>
              simp [__eo_prog_eq_resolve] at hProg
      | _ =>
          simp [__eo_prog_eq_resolve] at hProg
  | _ =>
      simp [__eo_prog_eq_resolve] at hProg

/-- Derives the checker facts exposed by the EO program for `eq_resolve`. -/
theorem facts___eo_prog_eq_resolve_impl
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M x2 true ->
  __eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2)) true := by
  intro hX1True hX2True hProg
  cases x2 with
  | Apply f B =>
      cases f with
      | Apply g A =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  change __eo_requires (__eo_eq x1 A) (Term.Boolean true) B ≠ Term.Stuck at hProg
                  have hEq : A = x1 := eq_of_requires_eq_true_not_stuck x1 A B hProg
                  subst A
                  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
                    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hX1True
                  have hEqBool :
                      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq x1) B) :=
                    RuleProofs.eo_has_bool_type_of_interprets_true M _ hX2True
                  have hBBool : RuleProofs.eo_has_bool_type B :=
                    eo_has_bool_type_eq_right x1 B hX1Bool hEqBool
                  have hX1NotStuck : x1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_interprets_true M x1 hX1True
                  have hEvalX1 : __smtx_model_eval M (__eo_to_smt x1) = SmtValue.Boolean true := by
                    have hX1True' := hX1True
                    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hX1True'
                    cases hX1True' with
                    | intro_true _ hEval => exact hEval
                  have hRel :=
                    RuleProofs.eo_interprets_eq_rel M x1 B hX2True
                  rw [hEvalX1] at hRel
                  have hBTrans : RuleProofs.eo_has_smt_translation B :=
                    RuleProofs.eo_has_smt_translation_of_has_bool_type B hBBool
                  have hEqBTrueBool :
                      RuleProofs.eo_has_bool_type
                        (Term.Apply (Term.Apply Term.eq B) (Term.Boolean true)) := by
                    have hTyEq :
                        __smtx_typeof (__eo_to_smt B) =
                          __smtx_typeof (__eo_to_smt (Term.Boolean true)) := by
                      have hTrueTy : __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
                        change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
                        rw [__smtx_typeof.eq_1]
                      exact hBBool.trans hTrueTy.symm
                    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                      B (Term.Boolean true) hTyEq hBTrans
                  have hRelBTrue :
                      RuleProofs.smt_value_rel (__smtx_model_eval M (__eo_to_smt B))
                        (__smtx_model_eval M (__eo_to_smt (Term.Boolean true))) := by
                    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by
                      rfl]
                    rw [__smtx_model_eval.eq_1]
                    exact RuleProofs.smt_value_rel_symm _ _ hRel
                  have hEqBTrue :
                      eo_interprets M
                        (Term.Apply (Term.Apply Term.eq B) (Term.Boolean true)) true :=
                    RuleProofs.eo_interprets_eq_of_rel M B (Term.Boolean true)
                      hEqBTrueBool
                      hRelBTrue
                  have hBNotStuck : B ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_bool_type B hBBool
                  have hProgTrueElim :
                      __eo_prog_true_elim
                        (Proof.pf (Term.Apply (Term.Apply Term.eq B) (Term.Boolean true))) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_true_elim] using hBNotStuck
                  have hBTrue : eo_interprets M B true := by
                    simpa [__eo_prog_true_elim] using
                      facts___eo_prog_true_elim_impl M hM
                        (Term.Apply (Term.Apply Term.eq B) (Term.Boolean true))
                        hEqBTrue hProgTrueElim
                  rw [prog_eq_resolve_eq_rhs_of_not_stuck x1 B hX1NotStuck]
                  exact hBTrue
              | _ =>
                  simp [__eo_prog_eq_resolve] at hProg
          | _ =>
              simp [__eo_prog_eq_resolve] at hProg
      | _ =>
          simp [__eo_prog_eq_resolve] at hProg
  | _ =>
      simp [__eo_prog_eq_resolve] at hProg

public theorem cmd_step_eq_resolve_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_resolve args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.eq_resolve args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_resolve args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.eq_resolve args premises ≠ Term.Stuck :=
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
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n2 premises =>
              cases premises with
              | nil =>
                  let X1 := __eo_state_proven_nth s n1
                  let X2 := __eo_state_proven_nth s n2
                  have hProgEqResolve :
                      __eo_prog_eq_resolve (Proof.pf X1) (Proof.pf X2) ≠ Term.Stuck := by
                    change __eo_prog_eq_resolve
                      (Proof.pf (__eo_state_proven_nth s n1))
                      (Proof.pf (__eo_state_proven_nth s n2)) ≠ Term.Stuck at hProg
                    simpa [X1, X2] using hProg
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    change eo_interprets M (__eo_prog_eq_resolve (Proof.pf X1) (Proof.pf X2)) true
                    exact facts___eo_prog_eq_resolve_impl M hM X1 X2
                      (hTrue X1 (by simp [X1, premiseTermList]))
                      (hTrue X2 (by simp [X2, premiseTermList]))
                      hProgEqResolve
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (by
                        change RuleProofs.eo_has_bool_type
                          (__eo_prog_eq_resolve (Proof.pf X1) (Proof.pf X2))
                        exact typed___eo_prog_eq_resolve_impl X1 X2
                          (hPremisesBool X1 (by simp [X1, premiseTermList]))
                          (hPremisesBool X2 (by simp [X2, premiseTermList]))
                          hProgEqResolve)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
