module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support
public import Cpc.Proofs.Canonical
import all Cpc.Proofs.Canonical
public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.Proofs.TypePreservation.Helpers

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply Term.not t) = SmtTerm.not (__eo_to_smt t) := by
  rfl

theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem model_eval_eo_to_smt_canonical
    (M : SmtModel) (hM : model_wf M) (t : Term)
    (hTrans : eo_has_smt_translation t) :
    value_canonical (__smtx_model_eval M (__eo_to_smt t)) := by
  exact Smtm.model_eval_canonical M hM (__eo_to_smt t) (by
    simpa [eo_has_smt_translation, term_has_non_none_type] using hTrans)

theorem eo_typeof_eq_bool_operands_not_stuck (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · exact ⟨hA, hB⟩

theorem eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

/-- EO equality recognizes every non-stuck term as equal to itself. -/
theorem eo_eq_self_of_ne_stuck (t : Term) (h : t ≠ Term.Stuck) :
    __eo_eq t t = Term.Boolean true := by
  cases t <;> simp [__eo_eq, native_teq] at h ⊢

theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  have hProg' := hProg
  -- Leaving `__eo_eq` folded keeps the `Decidable` instance in the `native_teq`
  -- application in sync with the proposition `simp` rewrites underneath it.
  simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  exact eq_of_eo_eq_true x y hProg'.1

theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧ __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

/-- A Boolean conjunction evaluates to true only when both operands are true.

The proof follows the two result-producing shapes of `__eo_and` rather than
splitting the Cartesian product of all `Term` constructors. -/
theorem eo_and_eq_true_args (x y : Term)
    (h : __eo_and x y = Term.Boolean true) :
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  cases x <;> try simp [__eo_and] at h
  case Boolean bx =>
    cases y <;> try simp at h
    case Boolean bY =>
      cases bx <;> cases bY <;> simp [native_and] at h ⊢
  case Binary wx nx =>
    cases y <;> try simp at h
    case Binary wy ny =>
      by_cases hW : wx = wy
      · subst wy
        have hReq :
            __eo_requires (Term.Numeral wx) (Term.Numeral wx)
                (Term.Binary wx
                  (native_mod_total (native_binary_and wx nx ny)
                    (native_int_pow2 wx))) =
              Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)) := by
          simp [__eo_requires, native_ite, native_teq, native_not]
        rw [hReq] at h
        cases h
      · simp [__eo_requires, native_ite, native_teq, hW] at h

theorem model_eval_eq_false_of_eo_eq_false
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) false ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

theorem native_veq_false_of_model_eval_eq_false
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false) :
    native_veq v1 v2 = false := by
  by_cases hEq : native_veq v1 v2 = false
  · exact hEq
  · have hEqTrue : native_veq v1 v2 = true := by
      cases hV : native_veq v1 v2 with
      | false =>
          exfalso
          exact hEq hV
      | true =>
          rfl
    have hv : v1 = v2 := by
      simpa [native_veq] using hEqTrue
    subst hv
    rw [smtx_model_eval_eq_refl] at h
    cases h

private theorem model_eval_eq_is_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b :=
  bool_value_canonical (typeof_value_model_eval_eq_value v1 v2)

theorem model_eval_eq_false_of_eq_false_eq_true
    (M : SmtModel) (x y : Term) :
  eo_interprets M
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x) y))
          (Term.Boolean false)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h
  rw [eo_to_smt_eq_eq, eo_to_smt_eq_eq, eo_to_smt_false_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      have hEqEval :
          __smtx_model_eval M ((__eo_to_smt x).eq (__eo_to_smt y)) =
            __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt y)) := by
        rw [smtx_eval_eq_term_eq]
      have hFalseEval :
          __smtx_model_eval M (SmtTerm.Boolean false) =
            SmtValue.Boolean false := by
        rw [__smtx_model_eval.eq_1]
      rw [hEqEval, hFalseEval] at hEval
      rcases model_eval_eq_is_boolean
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) with
        ⟨b, hInner⟩
      rw [hInner] at hEval
      cases b
      · exact hInner
      · simp [__smtx_model_eval_eq, native_veq] at hEval

theorem model_eval_eq_false_of_not_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  exact model_eval_eq_false_of_eo_eq_false M x y
    (eo_interprets_not_true_implies_false M _ h)

end RuleProofs
