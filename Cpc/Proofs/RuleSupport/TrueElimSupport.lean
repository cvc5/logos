module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_has_bool_type_eq_left (A B : Term) :
  RuleProofs.eo_has_bool_type B ->
  RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq A) B) ->
  RuleProofs.eo_has_bool_type A := by
  intro hBBool hEqBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type A B hEqBool with
    ⟨hTy, _hNonNone⟩
  exact hTy.trans hBBool

/-- Shows that the EO program for `true_elim` is well typed. -/
theorem typed___eo_prog_true_elim_impl (x1 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  __eo_prog_true_elim (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_true_elim (Proof.pf x1)) := by
  intro hX1Bool hProg
  cases x1 with
  | Apply f a =>
      cases a with
      | Boolean v =>
          cases v with
          | true =>
              cases f with
              | Apply g b =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          simpa [__eo_prog_true_elim] using
                            (eo_has_bool_type_eq_left b (Term.Boolean true)
                              RuleProofs.eo_has_bool_type_true hX1Bool)
                      | _ =>
                          simp [__eo_prog_true_elim] at hProg
                  | _ =>
                      simp [__eo_prog_true_elim] at hProg
              | _ =>
                  simp [__eo_prog_true_elim] at hProg
          | false =>
              simp [__eo_prog_true_elim] at hProg
      | _ =>
          simp [__eo_prog_true_elim] at hProg
  | _ =>
      simp [__eo_prog_true_elim] at hProg

/-- Derives the checker facts exposed by the EO program for `true_elim`. -/
theorem facts___eo_prog_true_elim_impl
    (M : SmtModel) (hM : model_wf M) (x1 : Term) :
  eo_interprets M x1 true ->
  __eo_prog_true_elim (Proof.pf x1) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_true_elim (Proof.pf x1)) true := by
  intro hX1True hProg
  cases x1 with
  | Apply f a =>
      cases a with
      | Boolean v =>
          cases v with
          | true =>
              cases f with
              | Apply g b =>
                  cases g with
                  | UOp op =>
                      cases op with
                      | eq =>
                          have hEqBool :
                              RuleProofs.eo_has_bool_type
                                (Term.Apply (Term.Apply Term.eq b) (Term.Boolean true)) :=
                            RuleProofs.eo_has_bool_type_of_interprets_true M _ hX1True
                          have hBBool : RuleProofs.eo_has_bool_type b :=
                            eo_has_bool_type_eq_left b (Term.Boolean true)
                              RuleProofs.eo_has_bool_type_true hEqBool
                          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM b hBBool with
                            ⟨bv, hEvalB⟩
                          have hRel :
                              RuleProofs.smt_value_rel (__smtx_model_eval M (__eo_to_smt b))
                                (SmtValue.Boolean true) :=
                            by
                              have hRel' :=
                                RuleProofs.eo_interprets_eq_rel M b (Term.Boolean true) hX1True
                              rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by
                                rfl] at hRel'
                              rw [__smtx_model_eval.eq_1] at hRel'
                              exact hRel'
                          cases bv with
                          | false =>
                              rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hRel
                              rw [hEvalB] at hRel
                              simp [__smtx_model_eval_eq, native_veq] at hRel
                          | true =>
                              simpa [__eo_prog_true_elim] using
                                (RuleProofs.eo_interprets_of_bool_eval M b true hBBool hEvalB)
                      | _ =>
                          simp [__eo_prog_true_elim] at hProg
                  | _ =>
                      simp [__eo_prog_true_elim] at hProg
              | _ =>
                  simp [__eo_prog_true_elim] at hProg
          | false =>
              simp [__eo_prog_true_elim] at hProg
      | _ =>
          simp [__eo_prog_true_elim] at hProg
  | _ =>
      simp [__eo_prog_true_elim] at hProg
