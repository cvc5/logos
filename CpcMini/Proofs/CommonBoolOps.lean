module

public import CpcMini.Proofs.Common
import all CpcMini.Proofs.Common

/-!
# `not` and `eq` helper lemmas

Translation, typing and interpretation lemmas for the SMT-LIB symbols `not`
and `=`.  They are used only by rule proofs, never by the checker, so they live
here rather than in `Proofs/Common.lean`: that keeps `not` and `=` out of the
checker layer's transitive imports, and a calculus whose signature declares
neither can drop this module without touching anything else.
-/

public section

open Eo
open SmtEval
open Smtm



namespace RuleProofs

/-- Simplifies EO-to-SMT translation for `not`. -/
private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.not) t) =
      SmtTerm.not (__eo_to_smt t) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `eq`. -/
private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rw [__eo_to_smt.eq_def]

/-- Derives `eo_has_bool_type_not` from `bool_arg`. -/
theorem eo_has_bool_type_not_of_bool_arg (t : Term) :
  eo_has_bool_type t ->
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_not_eq t]
  simp [Smtm.__smtx_typeof.eq_6, hTy, native_ite, native_Teq]

/-- Lemma about `eo_has_bool_type_not_arg`. -/
theorem eo_has_bool_type_not_arg (t : Term) :
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) ->
  eo_has_bool_type t := by
  intro hTy
  by_cases hT : __smtx_typeof (__eo_to_smt t) = SmtType.Bool
  · simpa [eo_has_bool_type] using hT
  · have : False := by
      unfold eo_has_bool_type at hTy
      rw [eo_to_smt_not_eq t] at hTy
      rw [Smtm.__smtx_typeof.eq_6] at hTy
      simp [hT, native_ite, native_Teq] at hTy
    exact False.elim this

/-- Computes `__smtx_typeof` for `eq_bool_iff`. -/
theorem smtx_typeof_eq_bool_iff (T U : SmtType) :
  __smtx_typeof_eq T U = SmtType.Bool ↔ T = U ∧ T ≠ SmtType.None := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · subst hT
    simp [native_ite, native_Teq]
  · by_cases hEq : T = U
    · subst hEq
      simp [native_ite, native_Teq, hT]
    · simp [native_ite, native_Teq, hEq, hT]

/-- Derives `eo_eq_operands_same_smt_type` from `has_bool_type`. -/
theorem eo_eq_operands_same_smt_type_of_has_bool_type (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTy
  unfold eo_has_bool_type at hTy
  rw [eo_to_smt_eq_eq x y] at hTy
  rw [Smtm.__smtx_typeof.eq_10] at hTy
  exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `same_smt_type`. -/
theorem eo_has_bool_type_eq_of_same_smt_type (x y : Term) :
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ->
  __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  intro hTy hNonNone
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x))
      (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTy, hNonNone⟩
  rw [eo_to_smt_eq_eq x y]
  rw [Smtm.__smtx_typeof.eq_10]
  exact hEqTy

/-- Symmetry lemma for `eo_has_bool_type_eq`. -/
theorem eo_has_bool_type_eq_symm (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) := by
  intro hTy
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hTy with ⟨hEq, hNonNone⟩
  have hNonNone' : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    simpa [hEq] using hNonNone
  exact eo_has_bool_type_eq_of_same_smt_type y x hEq.symm hNonNone'

/-- Derives `eo_has_bool_type_eq` from `bool_chain`. -/
theorem eo_has_bool_type_eq_of_bool_chain (x y z : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type_of_has_bool_type y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  exact eo_has_bool_type_eq_of_same_smt_type x z hTyXZ hNonNone

/-- Establishes an equality relating `eo` and `operands_same_smt_type`. -/
theorem eo_eq_operands_same_smt_type (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true hTy _ =>
      rw [Smtm.__smtx_typeof.eq_10] at hTy
      exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_eq_operands_same_smt_type` from `false`. -/
theorem eo_eq_operands_same_smt_type_of_false (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) false ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_false hTy _ =>
      rw [Smtm.__smtx_typeof.eq_10] at hTy
      exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `true_chain`. -/
theorem eo_has_bool_type_eq_of_true_chain (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type M y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt z)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt z))).mpr ⟨hTyXZ, hNonNone⟩
  rw [eo_to_smt_eq_eq x z]
  rw [Smtm.__smtx_typeof.eq_10]
  exact hEqTy

/-- Derives `eo_has_bool_type_eq` from `true`. -/
theorem eo_has_bool_type_eq_of_true (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  intro hXY
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTyXY, hNonNone⟩
  unfold eo_has_bool_type
  rw [eo_to_smt_eq_eq x y]
  rw [Smtm.__smtx_typeof.eq_10]
  exact hEqTy

/-- Establishes an equality relating `eo_interprets` and `rel`. -/
theorem eo_interprets_eq_rel (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  smt_value_rel M (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  rw [smt_value_rel_iff_model_eval_eq_true M]
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true _ hEval =>
      rw [Smtm.__smtx_model_eval.eq_10] at hEval
      exact hEval

/-- Derives `eo_interprets_eq` from `rel`. -/
theorem eo_interprets_eq_of_rel (M : SmtModel) (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  smt_value_rel M (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true := by
  intro hTy hRel
  rw [eo_interprets_iff_smt_interprets]
  rw [eo_to_smt_eq_eq x y]
  refine smt_interprets.intro_true M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) ?_ ?_
  · simpa [eo_has_bool_type, eo_to_smt_eq_eq x y] using hTy
  · have hEvalEq :
        __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true :=
      (smt_value_rel_iff_model_eval_eq_true M
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))).mp hRel
    simpa [Smtm.__smtx_model_eval.eq_10] using hEvalEq

/-- Transitivity lemma for `eo_interprets_eq`. -/
theorem eo_interprets_eq_trans (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) true := by
  intro hXY hYZ
  apply eo_interprets_eq_of_rel M x z
  · exact eo_has_bool_type_eq_of_true_chain M x y z hXY hYZ
  · exact smt_value_rel_trans M
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))
      (eo_interprets_eq_rel M x y hXY)
      (eo_interprets_eq_rel M y z hYZ)

/-- Derives `eo_interprets_not` from `false`. -/
theorem eo_interprets_not_of_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true := by
  intro hFalse
  rw [eo_interprets_iff_smt_interprets] at hFalse ⊢
  rw [eo_to_smt_not_eq t]
  cases hFalse with
  | intro_false hTy hEval =>
      refine smt_interprets.intro_true M
          (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · simp [Smtm.__smtx_typeof.eq_6, hTy, native_Teq, native_ite]
      · simp [Smtm.__smtx_model_eval.eq_6, __smtx_model_eval_not, SmtEval.native_not, hEval]

set_option linter.unusedSimpArgs false in
/-- Shows that `eo_interprets_not_true` implies `false`. -/
theorem eo_interprets_not_true_implies_false (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true -> eo_interprets M t false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_not_eq t] at h
  cases h with
  | intro_true hty hEval =>
      have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
        rw [Smtm.__smtx_typeof.eq_6] at hty
        simpa [native_Teq, native_ite] using hty
      rw [Smtm.__smtx_model_eval.eq_6] at hEval
      cases ht : __smtx_model_eval M (__eo_to_smt t) with
      | NotValue =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Boolean b =>
          cases b with
          | false =>
              exact smt_interprets.intro_false M (__eo_to_smt t) htyt ht
          | true =>
              exfalso
              simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Numeral n =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Rational q =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Binary w n =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Map m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Fun fid A B =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Set m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Seq s =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Char c =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | UValue s i =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | RegLan r =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | DtCons s d i =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Apply f x =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval

end RuleProofs
