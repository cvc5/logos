module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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

private theorem prog_modus_ponens_eq_rhs_of_not_stuck (x B : Term) :
  x ≠ Term.Stuck ->
  __eo_prog_modus_ponens (Proof.pf x) (Proof.pf (Term.Apply (Term.Apply Term.imp x) B)) = B := by
  intro hX
  cases x <;> simp [__eo_prog_modus_ponens, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not, SmtEval.native_not] at hX ⊢

/-- Shows that the EO program for `modus_ponens` is well typed. -/
theorem typed___eo_prog_modus_ponens_impl (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2)) := by
  intro hX2Bool hProg
  cases x2 with
  | Apply f B =>
      cases f with
      | Apply g A =>
          cases g with
          | UOp op =>
              cases op with
              | imp =>
                  change __eo_requires (__eo_eq x1 A) (Term.Boolean true) B ≠ Term.Stuck at hProg
                  have hEq : A = x1 := eq_of_requires_eq_true_not_stuck x1 A B hProg
                  subst A
                  have hX1Bool : RuleProofs.eo_has_bool_type x1 :=
                    eo_has_bool_type_imp_left x1 B hX2Bool
                  have hX1NotStuck : x1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_has_bool_type x1 hX1Bool
                  rw [prog_modus_ponens_eq_rhs_of_not_stuck x1 B hX1NotStuck]
                  exact eo_has_bool_type_imp_right x1 B hX2Bool
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

/-- Derives the checker facts exposed by the EO program for `modus_ponens`. -/
theorem facts___eo_prog_modus_ponens_impl (M : SmtModel) (x1 x2 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M x2 true ->
  __eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2)) true := by
  intro hX1True hX2True hProg
  cases x2 with
  | Apply f B =>
      cases f with
      | Apply g A =>
          cases g with
          | UOp op =>
              cases op with
              | imp =>
                  change __eo_requires (__eo_eq x1 A) (Term.Boolean true) B ≠ Term.Stuck at hProg
                  have hEq : A = x1 := eq_of_requires_eq_true_not_stuck x1 A B hProg
                  subst A
                  have hX1NotStuck : x1 ≠ Term.Stuck :=
                    RuleProofs.term_ne_stuck_of_interprets_true M x1 hX1True
                  rw [prog_modus_ponens_eq_rhs_of_not_stuck x1 B hX1NotStuck]
                  exact RuleProofs.eo_interprets_imp_elim M x1 B hX2True hX1True
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

public theorem cmd_step_modus_ponens_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.modus_ponens args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.modus_ponens args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.modus_ponens args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.modus_ponens args premises ≠ Term.Stuck :=
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
                  have hProgModusPonens :
                      __eo_prog_modus_ponens (Proof.pf X1) (Proof.pf X2) ≠ Term.Stuck := by
                    change __eo_prog_modus_ponens
                      (Proof.pf (__eo_state_proven_nth s n1))
                      (Proof.pf (__eo_state_proven_nth s n2)) ≠ Term.Stuck at hProg
                    simpa [X1, X2] using hProg
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    change eo_interprets M (__eo_prog_modus_ponens (Proof.pf X1) (Proof.pf X2)) true
                    exact facts___eo_prog_modus_ponens_impl M X1 X2
                      (hTrue X1 (by simp [X1, premiseTermList]))
                      (hTrue X2 (by simp [X2, premiseTermList]))
                      hProgModusPonens
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (by
                        change RuleProofs.eo_has_bool_type
                          (__eo_prog_modus_ponens (Proof.pf X1) (Proof.pf X2))
                        exact typed___eo_prog_modus_ponens_impl X1 X2
                          (hPremisesBool X2 (by simp [X2, premiseTermList]))
                          hProgModusPonens)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
