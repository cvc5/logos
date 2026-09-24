module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

namespace RuleProofs

/-- Simplifies EO-to-SMT translation for `or`. -/
theorem eo_to_smt_or_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.or A) B) =
      SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Shows that `false` has translated SMT Boolean type. -/
theorem eo_has_bool_type_false :
    eo_has_bool_type (Term.Boolean false) := by
  unfold eo_has_bool_type
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by rfl]
  rw [__smtx_typeof.eq_1]

/-- Derives `eo_has_bool_type_or` from `bool_args`. -/
theorem eo_has_bool_type_or_of_bool_args (A B : Term) :
    eo_has_bool_type A ->
    eo_has_bool_type B ->
    eo_has_bool_type (Term.Apply (Term.Apply Term.or A) B) := by
  intro hA hB
  unfold eo_has_bool_type at hA hB ⊢
  rw [eo_to_smt_or_eq A B, typeof_or_eq]
  simp [hA, hB, native_ite, native_Teq]

/-- Left-projection lemma for `eo_has_bool_type_or`. -/
theorem eo_has_bool_type_or_left (A B : Term) :
    eo_has_bool_type (Term.Apply (Term.Apply Term.or A) B) ->
    eo_has_bool_type A := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_or_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1

/-- Right-projection lemma for `eo_has_bool_type_or`. -/
theorem eo_has_bool_type_or_right (A B : Term) :
    eo_has_bool_type (Term.Apply (Term.Apply Term.or A) B) ->
    eo_has_bool_type B := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_or_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2

/-- Introduces the left side of a Boolean `or`. -/
theorem eo_interprets_or_left_intro
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_interprets M A true ->
    eo_has_bool_type B ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true := by
  intro hATrue hBBool
  have hABool : eo_has_bool_type A :=
    eo_has_bool_type_of_interprets_true M A hATrue
  rw [eo_interprets_iff_smt_interprets] at hATrue ⊢
  rw [eo_to_smt_or_eq A B]
  cases hATrue with
  | intro_true hTyA hEvalA =>
      refine smt_interprets.intro_true M _ ?_ ?_
      · simpa [eo_has_bool_type, eo_to_smt_or_eq] using
          eo_has_bool_type_or_of_bool_args A B hABool hBBool
      · rw [__smtx_model_eval.eq_8]
        rcases eo_eval_is_boolean_of_has_bool_type M hM B hBBool with ⟨b, hEvalB⟩
        rw [hEvalA, hEvalB]
        cases b <;> simp [__smtx_model_eval_or, SmtEval.native_or]

/-- Introduces the right side of a Boolean `or`. -/
theorem eo_interprets_or_right_intro
    (M : SmtModel) (hM : model_wf M) (A B : Term) :
    eo_has_bool_type A ->
    eo_interprets M B true ->
    eo_interprets M (Term.Apply (Term.Apply Term.or A) B) true := by
  intro hABool hBTrue
  have hBBool : eo_has_bool_type B :=
    eo_has_bool_type_of_interprets_true M B hBTrue
  rw [eo_interprets_iff_smt_interprets] at hBTrue ⊢
  rw [eo_to_smt_or_eq A B]
  cases hBTrue with
  | intro_true hTyB hEvalB =>
      refine smt_interprets.intro_true M _ ?_ ?_
      · simpa [eo_has_bool_type, eo_to_smt_or_eq] using
          eo_has_bool_type_or_of_bool_args A B hABool hBBool
      · rw [__smtx_model_eval.eq_8]
        rcases eo_eval_is_boolean_of_has_bool_type M hM A hABool with ⟨a, hEvalA⟩
        rw [hEvalA, hEvalB]
        cases a <;> simp [__smtx_model_eval_or, SmtEval.native_or]

end RuleProofs
