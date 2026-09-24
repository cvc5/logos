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

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  -- v4.33 `simp` unfolds `__eo_eq` under `decide` and desyncs the
  -- `Decidable` instance, so derive the guard by contradiction instead.
  have hEq : __eo_eq x y = Term.Boolean true := by
    apply Classical.byContradiction
    intro hne
    apply hProg
    simp [__eo_requires, native_ite, native_teq, hne]
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at hEq
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at hEq
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using hEq
      simpa [native_teq] using hDec

private theorem eo_prog_bool_not_false_valid_eq_of_ne_stuck (t1 b : Term) :
    t1 ≠ Term.Stuck ->
    __eo_prog_bool_not_false t1
        (Proof.pf (Term.Apply (Term.Apply Term.eq b) (Term.Boolean true))) =
      __eo_requires (__eo_eq t1 b) (Term.Boolean true)
        (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1)) (Term.Boolean false)) := by
  intro hT1
  cases t1 <;> simp [__eo_prog_bool_not_false] at hT1 ⊢

private theorem eo_has_bool_type_eq_false_of_bool (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq t) (Term.Boolean false)) := by
  intro hBool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type t (Term.Boolean false)
    (hBool.trans eo_has_bool_type_false.symm)
    (by
      rw [hBool]
      decide)

private theorem eo_interprets_eq_false_of_false (M : SmtModel) (t : Term) :
  eo_interprets M t false ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq t) (Term.Boolean false)) true := by
  intro hFalse
  have hBool : RuleProofs.eo_has_bool_type t :=
    RuleProofs.eo_has_bool_type_of_interprets_false M t hFalse
  apply RuleProofs.eo_interprets_eq_of_rel M t (Term.Boolean false)
  · exact eo_has_bool_type_eq_false_of_bool t hBool
  · rw [RuleProofs.eo_interprets_iff_smt_interprets] at hFalse
    cases hFalse with
    | intro_false _ hEval =>
        have hFalseEval :
            __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) =
              SmtValue.Boolean false := by
          change __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false
          rw [__smtx_model_eval.eq_1]
        rw [hEval, hFalseEval]
        exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean false)

private theorem eo_interprets_not_false_of_true (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  eo_interprets M (Term.Apply Term.not t) false := by
  intro hTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hTrue ⊢
  change smt_interprets M (SmtTerm.not (__eo_to_smt t)) false
  cases hTrue with
  | intro_true hTy hEval =>
      refine smt_interprets.intro_false M (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · rw [typeof_not_eq]
        simp [hTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_7]
        rw [hEval]
        simp [__smtx_model_eval_not, SmtEval.native_not]

private theorem eo_interprets_eq_true_implies_true
    (M : SmtModel) (hM : model_wf M) (t : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq t) (Term.Boolean true)) true ->
  eo_interprets M t true := by
  intro hEqTrue
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq t) (Term.Boolean true)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ hEqTrue
  have hTBool : RuleProofs.eo_has_bool_type t :=
    eo_has_bool_type_eq_left t (Term.Boolean true)
      RuleProofs.eo_has_bool_type_true hEqBool
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t hTBool with
    ⟨bv, hEvalT⟩
  have hRel :
      RuleProofs.smt_value_rel (__smtx_model_eval M (__eo_to_smt t))
        (SmtValue.Boolean true) := by
    have hRel' := RuleProofs.eo_interprets_eq_rel M t (Term.Boolean true) hEqTrue
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by
      rfl] at hRel'
    rw [__smtx_model_eval.eq_1] at hRel'
    exact hRel'
  cases bv with
  | false =>
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
      rw [hEvalT] at hRel
      simp [__smtx_model_eval_eq, native_veq] at hRel
  | true =>
      exact RuleProofs.eo_interprets_of_bool_eval M t true hTBool hEvalT

/-- Shows that the EO program for `bool_not_false` is well typed. -/
theorem typed___eo_prog_bool_not_false_impl (t1 x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_bool_not_false t1 (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_bool_not_false t1 (Proof.pf x1)) := by
  intro hX1Bool hProg
  have hT1NotStuck : t1 ≠ Term.Stuck := by
    intro hT1
    subst t1
    simp [__eo_prog_bool_not_false] at hProg
  cases x1 with
  | Apply f a =>
      cases a with
      | Boolean v =>
          cases v with
          | false =>
              cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
          | true =>
              cases f with
              | Apply g b =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          rw [eo_prog_bool_not_false_valid_eq_of_ne_stuck t1 b hT1NotStuck] at hProg ⊢
                          have hBTy : RuleProofs.eo_has_bool_type b :=
                            eo_has_bool_type_eq_left b (Term.Boolean true)
                              RuleProofs.eo_has_bool_type_true hX1Bool
                          have hEq : b = t1 :=
                            eq_of_requires_eq_true_not_stuck t1 b
                              (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1))
                                (Term.Boolean false))
                              hProg
                          subst b
                          have hNotBool : RuleProofs.eo_has_bool_type (Term.Apply Term.not t1) :=
                            RuleProofs.eo_has_bool_type_not_of_bool_arg t1 hBTy
                          have hOutBool :
                              RuleProofs.eo_has_bool_type
                                (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1))
                                  (Term.Boolean false)) :=
                            eo_has_bool_type_eq_false_of_bool (Term.Apply Term.not t1) hNotBool
                          simpa [__eo_prog_bool_not_false, __eo_requires, __eo_eq,
                            native_ite, native_teq, native_not, SmtEval.native_not]
                            using hOutBool
                      | _ =>
                          cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
                  | _ =>
                      cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
              | _ =>
                  cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
      | _ =>
          cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
  | _ =>
      cases t1 <;> simp [__eo_prog_bool_not_false] at hProg

/-- Derives the checker facts exposed by the EO program for `bool_not_false`. -/
theorem facts___eo_prog_bool_not_false_impl
    (M : SmtModel) (hM : model_wf M) (t1 x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_bool_not_false t1 (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_bool_not_false t1 (Proof.pf x1)) true := by
  intro hX1True hProg
  have hT1NotStuck : t1 ≠ Term.Stuck := by
    intro hT1
    subst t1
    simp [__eo_prog_bool_not_false] at hProg
  cases x1 with
  | Apply f a =>
      cases a with
      | Boolean v =>
          cases v with
          | false =>
              cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
          | true =>
              cases f with
              | Apply g b =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          rw [eo_prog_bool_not_false_valid_eq_of_ne_stuck t1 b hT1NotStuck] at hProg ⊢
                          have hEq : b = t1 :=
                            eq_of_requires_eq_true_not_stuck t1 b
                              (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1))
                                (Term.Boolean false))
                              hProg
                          subst b
                          have hTTrue : eo_interprets M t1 true :=
                            eo_interprets_eq_true_implies_true M hM t1 hX1True
                          have hNotFalse : eo_interprets M (Term.Apply Term.not t1) false :=
                            eo_interprets_not_false_of_true M t1 hTTrue
                          have hOutTrue :
                              eo_interprets M
                                (Term.Apply (Term.Apply Term.eq (Term.Apply Term.not t1))
                                  (Term.Boolean false)) true :=
                            eo_interprets_eq_false_of_false M (Term.Apply Term.not t1) hNotFalse
                          simpa [__eo_prog_bool_not_false, __eo_requires, __eo_eq,
                            native_ite, native_teq, native_not, SmtEval.native_not]
                            using hOutTrue
                      | _ =>
                          cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
                  | _ =>
                      cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
              | _ =>
                  cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
      | _ =>
          cases t1 <;> simp [__eo_prog_bool_not_false] at hProg
  | _ =>
      cases t1 <;> simp [__eo_prog_bool_not_false] at hProg

public theorem cmd_step_bool_not_false_properties
    (M : SmtModel) (hM : model_wf M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bool_not_false args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_false args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.bool_not_false args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
                  have hProgNotFalse :
                      __eo_prog_bool_not_false a1 (Proof.pf X1) ≠ Term.Stuck := by
                    change __eo_prog_bool_not_false a1
                        (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                    simpa [X1] using hProg
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    change eo_interprets M (__eo_prog_bool_not_false a1 (Proof.pf X1)) true
                    exact facts___eo_prog_bool_not_false_impl M hM a1 X1
                      (hTrue X1 (by simp [X1, premiseTermList]))
                      hProgNotFalse
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (by
                        change RuleProofs.eo_has_bool_type
                          (__eo_prog_bool_not_false a1 (Proof.pf X1))
                        exact typed___eo_prog_bool_not_false_impl a1 X1
                          (hPremisesBool X1 (by simp [X1, premiseTermList]))
                          hProgNotFalse)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
