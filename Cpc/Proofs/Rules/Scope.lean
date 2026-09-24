module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_imp_eq_scope (x1 x2 : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.imp x1) x2) =
      SmtTerm.imp (__eo_to_smt x1) (__eo_to_smt x2) := by
  rfl

/-- Shows that the EO program for `scope_impl` is well typed. -/
theorem typed___eo_prog_scope_of_bool_args (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) := by
  intro hTy1 hTy2 hProg
  have hX1NotStuck : x1 ≠ Term.Stuck := by
    intro hStuck
    exact hProg (by simp [__eo_prog_scope, hStuck])
  have hScopeEq : __eo_prog_scope x1 (Proof.pf x2) = Term.Apply (Term.Apply Term.imp x1) x2 := by
    cases x1 <;> simp [__eo_prog_scope] at hX1NotStuck ⊢
  unfold RuleProofs.eo_has_bool_type at hTy1 hTy2 ⊢
  rw [hScopeEq, eo_to_smt_imp_eq_scope, typeof_imp_eq]
  simp [hTy1, hTy2, native_ite, native_Teq]

/-- Shows that the EO program for `scope_impl` is well typed. -/
theorem typed___eo_prog_scope_impl (M : SmtModel) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation x2 ->
  __eo_typeof x1 = Term.Bool ->
  __eo_typeof x2 = Term.Bool ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) := by
  intro _ hTrans1 hTrans2 hTy1 hTy2 hProg
  have hBool1 : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type x1 hTrans1 hTy1
  have hBool2 : RuleProofs.eo_has_bool_type x2 :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type x2 hTrans2 hTy2
  exact typed___eo_prog_scope_of_bool_args x1 x2 hBool1 hBool2 hProg

namespace RuleProofs

/-- Proves correctness of the EO program for `scope`. -/
theorem correct___eo_prog_scope
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term) :
  (eo_interprets M x1 true -> eo_interprets M x2 true) ->
  eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true := by
  intro hImp hTy
  have hProgNotStuck : __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck :=
    term_ne_stuck_of_has_bool_type _ hTy
  have hX1NotStuck : x1 ≠ Term.Stuck := by
    intro hStuck
    exact hProgNotStuck (by simp [__eo_prog_scope, hStuck])
  have hScopeEq : __eo_prog_scope x1 (Proof.pf x2) = Term.Apply (Term.Apply Term.imp x1) x2 := by
    cases x1 <;> simp [__eo_prog_scope] at hX1NotStuck ⊢
  have hScopeTy : eo_has_bool_type (Term.Apply (Term.Apply Term.imp x1) x2) := by
    simpa [hScopeEq] using hTy
  have hScopeTy' :
      __smtx_typeof (SmtTerm.imp (__eo_to_smt x1) (__eo_to_smt x2)) = SmtType.Bool := by
    simpa [eo_has_bool_type, eo_to_smt_imp_eq_scope, typeof_imp_eq] using hScopeTy
  have hTy1 : eo_has_bool_type x1 := by
    by_cases hBool : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool
    · simpa [eo_has_bool_type] using hBool
    · have : False := by
        rw [typeof_imp_eq] at hScopeTy'
        simp [hBool, native_ite, native_Teq] at hScopeTy'
      exact False.elim this
  have hTy2 : eo_has_bool_type x2 := by
    have hBool1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool := hTy1
    by_cases hBool : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool
    · simpa [eo_has_bool_type] using hBool
    · have : False := by
        rw [typeof_imp_eq] at hScopeTy'
        simp [hBool1, hBool, native_ite, native_Teq] at hScopeTy'
      exact False.elim this
  rw [hScopeEq]
  rcases eo_eval_is_boolean_of_has_bool_type M hM x1 hTy1 with ⟨b1, hEval1⟩
  cases b1 with
  | false =>
      rcases eo_eval_is_boolean_of_has_bool_type M hM x2 hTy2 with ⟨b2, hEval2⟩
      rw [eo_interprets_iff_smt_interprets, eo_to_smt_imp_eq_scope]
      refine smt_interprets.intro_true M
        (SmtTerm.imp (__eo_to_smt x1) (__eo_to_smt x2)) hScopeTy' ?_
      rw [__smtx_model_eval.eq_10, hEval1, hEval2]
      cases b2 <;>
        simp [__smtx_model_eval_imp, __smtx_model_eval_or,
          __smtx_model_eval_not, SmtEval.native_not, SmtEval.native_or]
  | true =>
      have hX1True : eo_interprets M x1 true :=
        eo_interprets_of_bool_eval M x1 true hTy1 hEval1
      have hX2True : eo_interprets M x2 true := hImp hX1True
      exact eo_interprets_imp_intro M x1 x2 hX1True hX2True

end RuleProofs

/-- Proves correctness of the EO program for `scope_impl`. -/
theorem correct___eo_prog_scope_impl
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true := by
  exact RuleProofs.correct___eo_prog_scope M hM x1 x2

/-- Derives the checker facts exposed by the EO program for `scope_impl`. -/
theorem facts___eo_prog_scope_impl
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term) :
  (eo_interprets M x1 true -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation x2 ->
  __eo_typeof x1 = Term.Bool ->
  __eo_typeof x2 = Term.Bool ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true := by
  intro hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
    typed___eo_prog_scope_impl M x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  exact correct___eo_prog_scope_impl M hM x1 x2 hImp hBool

public theorem cmd_step_pop_scope_properties
    (x1 : Term) (s : CState) (args : CArgList) (premises : CIndexList) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof x1 = Term.Bool ->
  AllHaveSmtTranslation (premiseTermList s premises) ->
  AllTypeofBool (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_pop_proven s CRule.scope args x1 premises) = Term.Bool ->
  StepPopRuleProperties x1 (premiseTermList s premises)
    (__eo_cmd_step_pop_proven s CRule.scope args x1 premises) := by
  intro hTrans1 hTy1 hPremisesTrans hPremisesTy hResultTy
  have hProg : __eo_cmd_step_pop_proven s CRule.scope args x1 premises ≠ Term.Stuck :=
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
              let x2 := __eo_state_proven_nth s n1
              have hTrans2 : RuleProofs.eo_has_smt_translation x2 :=
                hPremisesTrans x2 (by simp [x2, premiseTermList])
              have hTy2 : __eo_typeof x2 = Term.Bool :=
                hPremisesTy x2 (by simp [x2, premiseTermList])
              have hBool1 : RuleProofs.eo_has_bool_type x1 :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type x1 hTrans1 hTy1
              have hBool2 : RuleProofs.eo_has_bool_type x2 :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type x2 hTrans2 hTy2
              have hProgScope : __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck := by
                simpa [x2, __eo_cmd_step_pop_proven] using hProg
              refine ⟨x2, ?_, ?_, ?_⟩
              · simp [x2, premiseTermList]
              · intro M hM hImp
                change eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true
                exact facts___eo_prog_scope_impl M hM x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2
                  hProgScope
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2))
                    exact typed___eo_prog_scope_of_bool_args x1 x2 hBool1 hBool2 hProgScope)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
