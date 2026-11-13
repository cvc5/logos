module

public import CpcMini.Proofs.RuleSupport.Support
import all CpcMini.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
The public statement `typed___eo_prog_scope_impl` is checker-facing and asks
for checker-side Bool guards on the antecedent and consequent. The actual
semantic typing fact for `scope` is the stronger rule-local theorem below,
which consumes SMT-side Bool typing.
-/
/-- Shows that the EO program for `scope_of_bool_args` is well typed. -/
theorem typed___eo_prog_scope_of_bool_args (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) := by
  intro hTy1 hTy2 hProg
  cases x1 <;> cases x2 <;>
    simp [RuleProofs.eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
      native_ite, native_Teq] at hTy1 hTy2 ⊢ <;>
    simp [hTy1, hTy2]

/-- Shows that the EO program for `scope_impl` is well typed. -/
theorem typed___eo_prog_scope_impl (M : SmtModel) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_smt_translation x2 ->
  __eo_typeof x1 = Term.Bool ->
  __eo_typeof x2 = Term.Bool ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
by
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
  by_cases hStuck : x1 = Term.Stuck
  · subst hStuck
    simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof] at hTy
  · have hTy1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool := by
      by_cases hx1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool
      · exact hx1
      · simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
          native_ite, native_Teq, hx1] at hTy
    have hTy2 : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool := by
      by_cases hx2 : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool
      · exact hx2
      · simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
          native_ite, native_Teq, hTy1, hx2] at hTy
    have hTy1' : eo_has_bool_type x1 := hTy1
    have hTy2' : eo_has_bool_type x2 := hTy2
    rcases eo_eval_is_boolean_of_has_bool_type M hM x1 hTy1' with ⟨b1, hEval1⟩
    rw [eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M (__eo_to_smt (__eo_prog_scope x1 (Proof.pf x2))) ?_ ?_
    · simpa [eo_has_bool_type, __eo_prog_scope, hStuck, __eo_to_smt] using hTy
    · cases b1 with
      | false =>
          rcases eo_eval_is_boolean_of_has_bool_type M hM x2 hTy2' with ⟨b2, hEval2⟩
          cases b2 <;>
            simp [__eo_prog_scope, __eo_to_smt, __smtx_model_eval, hEval1, hEval2,
              __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
              SmtEval.native_not, SmtEval.native_or]
      | true =>
          have hX1True : eo_interprets M x1 true :=
            eo_interprets_of_bool_eval M x1 true hTy1' hEval1
          have hX2True : eo_interprets M x2 true := hImp hX1True
          rw [eo_interprets_iff_smt_interprets] at hX2True
          cases hX2True with
          | intro_true _ hEval2 =>
              simp [__eo_prog_scope, __eo_to_smt, __smtx_model_eval, hEval1, hEval2,
                __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
                SmtEval.native_not, SmtEval.native_or]

/-- Lemma about `not_eo_interprets_prog_scope_num_true`. -/
theorem not_eo_interprets_prog_scope_num_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_scope (Term.Numeral 0) (Proof.pf (Term.Boolean true))) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_scope, __eo_to_smt, __smtx_typeof, native_ite, native_Teq] at hTy

/-- Lemma about `not_eo_has_bool_type_prog_scope_num_true`. -/
theorem not_eo_has_bool_type_prog_scope_num_true :
  ¬ RuleProofs.eo_has_bool_type
      (__eo_prog_scope (Term.Numeral 0) (Proof.pf (Term.Boolean true))) := by
  simp [RuleProofs.eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
    native_ite, native_Teq]

end RuleProofs

/-- Proves correctness of the EO program for `scope_impl`. -/
theorem correct___eo_prog_scope_impl
    (M : SmtModel) (hM : model_wf M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
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
  eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true :=
by
  intro hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  let hBool : RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
    typed___eo_prog_scope_impl M x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2 hProg
  exact correct___eo_prog_scope_impl M hM x1 x2 hImp hBool

/-- Packages the properties required for the `pop_scope` checker step. -/
public theorem cmd_step_pop_scope_properties
    (x1 : Term) (s : CState) (args : CArgList) (premises : CIndexList) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof x1 = Term.Bool ->
  AllHaveSmtTranslation (premiseTermList s premises) ->
  AllTypeofBool (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_pop_proven s CRule.scope args x1 premises) = Term.Bool ->
  StepPopRuleProperties x1 (premiseTermList s premises)
    (__eo_cmd_step_pop_proven s CRule.scope args x1 premises) :=
by
  intro hTrans1 hTy1 hPremisesTrans hPremisesTy hResultTy
  have hProg : __eo_cmd_step_pop_proven s CRule.scope args x1 premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
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
              refine ⟨x2, ?_, ?_, ?_⟩
              · simp [x2, premiseTermList]
              · intro M hM hImp
                simpa [x2, __eo_cmd_step_pop_proven] using
                  facts___eo_prog_scope_impl M hM x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2
                    (by simpa [x2, __eo_cmd_step_pop_proven] using hProg)
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    simpa [x2, __eo_cmd_step_pop_proven] using
                      typed___eo_prog_scope_of_bool_args x1 x2 hBool1 hBool2
                        (by simpa [x2, __eo_cmd_step_pop_proven] using hProg))
          | cons _ _ =>
              exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
  | cons _ _ =>
      exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
