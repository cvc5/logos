module

public import Cpc.Proofs.Common
import all Cpc.Proofs.Common

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
  rfl

/-- Simplifies EO-to-SMT translation for `eq`. -/
private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

/-- Derives `eo_has_bool_type_not` from `bool_arg`. -/
theorem eo_has_bool_type_not_of_bool_arg (t : Term) :
  eo_has_bool_type t ->
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_not_eq t, typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

/-- Shows that a translated `not` term can only be Boolean when its argument is Boolean. -/
theorem eo_has_bool_type_not_arg (t : Term) :
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) ->
  eo_has_bool_type t := by
  intro hTy
  by_cases hT : __smtx_typeof (__eo_to_smt t) = SmtType.Bool
  · simpa [eo_has_bool_type] using hT
  · have : False := by
      unfold eo_has_bool_type at hTy
      rw [eo_to_smt_not_eq t, typeof_not_eq] at hTy
      simp [hT, native_ite, native_Teq] at hTy
    exact False.elim this

/-- Establishes an equality relating `smtx_typeof` and `bool_iff`. -/
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
  rw [typeof_eq_eq] at hTy
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
  rw [eo_to_smt_eq_eq x y, typeof_eq_eq]
  exact hEqTy

/-- Establishes an equality relating `eo_has_bool_type` and `symm`. -/
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
      rw [typeof_eq_eq] at hTy
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
      rw [typeof_eq_eq] at hTy
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
  rw [eo_to_smt_eq_eq x z, typeof_eq_eq]
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
  rw [eo_to_smt_eq_eq x y, typeof_eq_eq]
  exact hEqTy

/-- Establishes an equality relating `eo_interprets` and `rel`. -/
theorem eo_interprets_eq_rel (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  rw [smt_value_rel_iff_model_eval_eq_true]
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true _ hEval =>
      rw [smtx_model_eval_eq_term_eq] at hEval
      exact hEval

/-- Derives `eo_interprets_eq` from `rel`. -/
theorem eo_interprets_eq_of_rel (M : SmtModel) (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true := by
  intro hTy hRel
  rw [eo_interprets_iff_smt_interprets]
  rw [eo_to_smt_eq_eq x y]
  have hTyEq :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    rw [eo_has_bool_type, eo_to_smt_eq_eq x y, typeof_eq_eq] at hTy
    exact hTy
  have hTy' :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    exact hTyEq
  refine smt_interprets.intro_true M
      (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) ?_ ?_
  · exact hTy'
  · have hEvalEq :
        __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true :=
      (smt_value_rel_iff_model_eval_eq_true
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))).mp hRel
    rw [smtx_model_eval_eq_term_eq]
    exact hEvalEq

/-- Establishes an equality relating `eo_interprets` and `trans`. -/
theorem eo_interprets_eq_trans (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) true := by
  intro hXY hYZ
  apply eo_interprets_eq_of_rel M x z
  · exact eo_has_bool_type_eq_of_true_chain M x y z hXY hYZ
  · exact smt_value_rel_trans
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
      · rw [typeof_not_eq]
        simp [hTy, native_Teq, native_ite]
      · rw [__smtx_model_eval.eq_7]
        rw [hEval]
        simp [__smtx_model_eval_not, SmtEval.native_not]

/-- Shows that `eo_interprets_not_true` implies `false`. -/
theorem eo_interprets_not_true_implies_false (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true -> eo_interprets M t false := by
  intro h
  have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
    exact eo_has_bool_type_not_arg t
      (eo_has_bool_type_of_interprets_true M (Term.Apply (Term.UOp UserOp.not) t) h)
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_not_eq t] at h
  cases h with
  | intro_true hty hEval =>
      rw [__smtx_model_eval.eq_7] at hEval
      cases ht : __smtx_model_eval M (__eo_to_smt t) with
      | NotValue =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Boolean b =>
          cases b with
          | false =>
              exact smt_interprets.intro_false M (__eo_to_smt t) htyt ht
          | true =>
              exfalso
              simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Numeral n =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Rational q =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Binary w n =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Map m =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Fun fid T U =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Set m =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Seq s =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Char c =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | UValue s i =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | RegLan r =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | DtCons s d i =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval
      | Apply f x =>
          exfalso
          simp [__smtx_model_eval_not, ht] at hEval


/-! ## `imp` -/

/-- Simplifies EO-to-SMT translation for `imp`. -/
private theorem eo_to_smt_imp_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Elimination lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_elim (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true ->
  eo_interprets M A true ->
  eo_interprets M B true := by
  intro hImp hA
  rw [eo_interprets_iff_smt_interprets] at hImp hA ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_true htyImp hEvalImp =>
      cases hA with
      | intro_true htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            have hNN : term_has_non_none_type
                (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
              unfold term_has_non_none_type
              rw [htyImp]
              simp
            exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
              (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            rw [__smtx_model_eval.eq_10] at hEvalImp
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [hEvalA, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
                __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
            case Boolean a =>
              cases a <;> simp at hEvalImp
              simp
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_imp_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · rw [typeof_imp_eq]
            simp [htyA, htyB, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_10]
            rw [hEvalA, hEvalB]
            simp [__smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]

/-- Left-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false ->
  eo_interprets M A true := by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [htyImp]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
          (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [__smtx_model_eval.eq_10] at hEvalImp
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false ->
  eo_interprets M B false := by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [htyImp]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
          (typeof_imp_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean false := by
        rw [__smtx_model_eval.eq_10] at hEvalImp
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp
      exact smt_interprets.intro_false M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B false ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_imp_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_false htyB hEvalB =>
          apply smt_interprets.intro_false
          · rw [typeof_imp_eq]
            simp [htyA, htyB, native_Teq, native_ite]
          · rw [__smtx_model_eval.eq_10]
            rw [hEvalA, hEvalB]
            simp [__smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not]
end RuleProofs
