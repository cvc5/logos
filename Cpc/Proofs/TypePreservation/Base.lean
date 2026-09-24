module

import Lean
public import Cpc.Proofs.TypePreservation.Model
import all Cpc.SmtModel
import all Cpc.Proofs.TypePreservation.Common

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

theorem smtx_model_eval_choice_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm) :
  __smtx_model_eval M (SmtTerm.choice s T body) =
    native_eval_choice M s T body :=
by
  rw [__smtx_model_eval.eq_def]

theorem smtx_model_eval_bind_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (x1 x2 : SmtTerm) :
  __smtx_model_eval M (SmtTerm.bind s T x1 x2) =
    __smtx_model_eval (native_model_push M s T (__smtx_model_eval M x1)) x2 :=
by
  rw [__smtx_model_eval.eq_def]

/-- Shows that evaluating `boolean` terms produces values of the expected type. -/
theorem typeof_value_model_eval_boolean
    (M : SmtModel)
    (b : native_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `numeral` terms produces values of the expected type. -/
theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : native_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `rational` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `binary` terms produces values of the expected type. -/
theorem typeof_value_model_eval_binary
    (M : SmtModel)
    (w n : native_Int)
    (ht : term_has_non_none_type (SmtTerm.Binary w n)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Binary w n)) =
      __smtx_typeof (SmtTerm.Binary w n) := by
  unfold term_has_non_none_type at ht
  let g :=
    native_and (native_zleq 0 w)
      (native_zeq n (native_mod_total n (native_int_pow2 w)))
  have hg : g = true := by
    cases h : g with
    | false =>
        exfalso
        apply ht
        unfold __smtx_typeof
        simp [g, native_ite, h]
    | true =>
        rfl
  have hWidth : native_zleq 0 w = true := by
    cases h1 : native_zleq 0 w
    · simp [g, SmtEval.native_and, h1] at hg
    · rfl
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases h2 : native_zeq n (native_mod_total n (native_int_pow2 w))
    · simp [g, SmtEval.native_and, hWidth, h2] at hg
    · rfl
  have hType :
      __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
    have hAnd :
        native_and (native_zleq 0 w)
          (native_zeq n (native_mod_total n (native_int_pow2 w))) = true := by
      simp [SmtEval.native_and, hWidth, hMod]
    unfold __smtx_typeof
    simp [hAnd, native_ite]
  rw [hType]
  unfold __smtx_model_eval __smtx_typeof_value
  simp [native_ite, SmtEval.native_and, hWidth, hMod]

/-- Shows that evaluating `var` terms produces values of the expected type. -/
theorem typeof_value_model_eval_var
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Var s T)) =
      __smtx_typeof (SmtTerm.Var s T) := by
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    unfold __smtx_typeof at ht
    exact ht
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T hGuardNN
  unfold __smtx_model_eval __smtx_typeof
  rw [model_total_typed_var_lookup hM s T hWF]
  exact hGuard.symm

/-- Shows that evaluating `uconst` terms produces values of the expected type. -/
theorem typeof_value_model_eval_uconst
    (M : SmtModel)
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.UConst s T)) =
      __smtx_typeof (SmtTerm.UConst s T) := by
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    unfold __smtx_typeof at ht
    exact ht
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T hGuardNN
  unfold __smtx_model_eval __smtx_typeof
  rw [model_total_typed_lookup hM s T hWF]
  exact hGuard.symm

/-- If a variable has sequence type `Seq A`, then `A` is non-`None`. -/
theorem var_type_eq_seq_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_seq_component_non_none h

/-- If a variable has set type `Set A`, then `A` is non-`None`. -/
theorem var_type_eq_set_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.Set A) :
    A ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_set_component_non_none h

/-- If a variable has map type `Map A B`, then both components are non-`None`. -/
theorem var_type_eq_map_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_map_components_non_none h

/-- If a variable has function type `FunType A B`, then both components are non-`None`. -/
theorem var_type_eq_fun_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.Var s T) = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_fun_components_non_none h

/-- If a uconst has sequence type `Seq A`, then `A` is non-`None`. -/
theorem uconst_type_eq_seq_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_seq_component_non_none h

/-- If a uconst has set type `Set A`, then `A` is non-`None`. -/
theorem uconst_type_eq_set_component_non_none
    {s : native_String}
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Set A) :
    A ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_set_component_non_none h

/-- If a uconst has map type `Map A B`, then both components are non-`None`. -/
theorem uconst_type_eq_map_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_map_components_non_none h

/-- If a uconst has function type `FunType A B`, then both components are non-`None`. -/
theorem uconst_type_eq_fun_components_non_none
    {s : native_String}
    {T A B : SmtType}
    (h : __smtx_typeof (SmtTerm.UConst s T) = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  exact smtx_typeof_guard_wf_self_eq_fun_components_non_none h

/-- If `seq_empty` has type `Seq A`, then `A` is non-`None`. -/
theorem seq_empty_type_eq_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.seq_empty T) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [__smtx_typeof] using hNN
  have hGuardEq :
      __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) = SmtType.Seq A := by
    simpa [__smtx_typeof] using h
  have hGuard : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) = SmtType.Seq T :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN
  have hEq : T = A := by
    have hSeq : SmtType.Seq T = SmtType.Seq A := hGuard.symm.trans hGuardEq
    injection hSeq with hEq
  cases hEq
  exact type_wf_non_none
    (seq_type_wf_component_of_wf
      (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) hGuardNN))

/-- If `set_empty` has type `Set A`, then `A` is non-`None`. -/
theorem set_empty_type_eq_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof (SmtTerm.set_empty T) = SmtType.Set A) :
    A ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.set_empty T) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuardNN : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at hNN
    simpa [__smtx_typeof] using hNN
  have hGuardEq :
      __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) = SmtType.Set A := by
    simpa [__smtx_typeof] using h
  have hGuard : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) = SmtType.Set T :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN
  have hEq : T = A := by
    have hSet : SmtType.Set T = SmtType.Set A := hGuard.symm.trans hGuardEq
    injection hSet with hEq
  cases hEq
  exact type_wf_non_none
    (set_type_wf_component_of_wf
      (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set T) (SmtType.Set T) hGuardNN))

/-- If `seq_unit t` has type `Seq A`, then `t` has type `A` and `A` is non-`None`. -/
theorem seq_unit_type_eq_arg_of_eq
    {t : SmtTerm}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.seq_unit t) = SmtType.Seq A) :
    __smtx_typeof t = A ∧ A ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  have hGuardNN :
      __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) =
        SmtType.Seq (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
      (SmtType.Seq (__smtx_typeof t)) hGuardNN
  have hSeq : SmtType.Seq (__smtx_typeof t) = SmtType.Seq A :=
    hGuard.symm.trans h
  injection hSeq with hEq
  subst hEq
  exact ⟨rfl,
    type_wf_non_none
      (seq_type_wf_component_of_wf
        (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) hGuardNN))⟩

/-- If `set_singleton t` has type `Set A`, then `t` has type `A` and `A` is non-`None`. -/
theorem set_singleton_type_eq_arg_of_eq
    {t : SmtTerm}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.set_singleton t) = SmtType.Set A) :
    __smtx_typeof t = A ∧ A ≠ SmtType.None := by
  simp [__smtx_typeof] at h
  have hGuardNN :
      __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) =
        SmtType.Set (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Set (__smtx_typeof t))
      (SmtType.Set (__smtx_typeof t)) hGuardNN
  have hSet : SmtType.Set (__smtx_typeof t) = SmtType.Set A :=
    hGuard.symm.trans h
  injection hSet with hEq
  subst hEq
  exact ⟨rfl,
    type_wf_non_none
      (set_type_wf_component_of_wf
        (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) hGuardNN))⟩

/-- Shows that evaluating `re_allchar` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_allchar
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_allchar) =
      __smtx_typeof SmtTerm.re_allchar := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `re_none` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_none
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_none) =
      __smtx_typeof SmtTerm.re_none := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `re_all` terms produces values of the expected type. -/
theorem typeof_value_model_eval_re_all
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_all) =
      __smtx_typeof SmtTerm.re_all := by
  unfold __smtx_model_eval __smtx_typeof __smtx_typeof_value
  rfl

/-- Shows that evaluating `seq_empty` terms produces values of the expected type. -/
theorem typeof_value_model_eval_seq_empty
    (M : SmtModel)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.seq_empty T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_empty T)) =
      __smtx_typeof (SmtTerm.seq_empty T) := by
  have hGuard : __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) = SmtType.Seq T :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) (by
      unfold term_has_non_none_type at ht
      unfold __smtx_typeof at ht
      exact ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, hGuard]

/-- Shows that evaluating `set_empty` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_empty
    (M : SmtModel)
    (T : SmtType)
    (hT : type_inhabited T)
    (ht : term_has_non_none_type (SmtTerm.set_empty T)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_empty T)) =
      __smtx_typeof (SmtTerm.set_empty T) := by
  have hGuard : __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) = SmtType.Set T :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Set T) (SmtType.Set T) (by
      unfold term_has_non_none_type at ht
      unfold __smtx_typeof at ht
      exact ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type,
    hGuard]

/-- Shows that evaluating `seq_unit` terms produces values of the expected type. -/
theorem typeof_value_model_eval_seq_unit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_unit t)) =
      __smtx_typeof (SmtTerm.seq_unit t) := by
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
          (SmtType.Seq (__smtx_typeof t)) =
        SmtType.Seq (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Seq (__smtx_typeof t))
      (SmtType.Seq (__smtx_typeof t)) (by
        unfold term_has_non_none_type at ht
        simpa [__smtx_typeof] using ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, hpres, hGuard,
    native_Teq, native_ite]

/-- Shows that evaluating `set_singleton` terms produces values of the expected type. -/
theorem typeof_value_model_eval_set_singleton
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_singleton t)) =
      __smtx_typeof (SmtTerm.set_singleton t) := by
  have hGuard :
      __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
          (SmtType.Set (__smtx_typeof t)) =
        SmtType.Set (__smtx_typeof t) :=
    smtx_typeof_guard_wf_of_non_none (SmtType.Set (__smtx_typeof t))
      (SmtType.Set (__smtx_typeof t)) (by
        unfold term_has_non_none_type at ht
        simpa [__smtx_typeof] using ht)
  unfold __smtx_model_eval __smtx_typeof
  simp [__smtx_model_eval_set_singleton, __smtx_typeof_value, __smtx_typeof_map_value,
    __smtx_map_to_set_type, hpres, hGuard, native_Teq, native_ite]

/-- Derives `exists_body_bool` from `non_none`. -/
theorem exists_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  simpa [native_Teq] using hEq

/-- Derives `exists_term_typeof` from `non_none`. -/
theorem exists_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool := by
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    simpa [native_Teq] using exists_body_bool_of_non_none ht
  have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
    smtx_typeof_guard_wf_of_non_none T SmtType.Bool (by
      intro hNone
      unfold term_has_non_none_type at ht
      apply ht
      unfold __smtx_typeof
      simp [hEq, native_ite, hNone])
  unfold __smtx_typeof
  simp [hEq, native_ite, hGuard]

/-- Shows that evaluating `exists` terms produces values of the expected type. -/
theorem typeof_value_model_eval_exists
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.exists s T body)) =
      __smtx_typeof (SmtTerm.exists s T body) := by
  classical
  rw [exists_term_typeof_of_non_none ht]
  unfold __smtx_model_eval
  by_cases h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · simp [h, __smtx_typeof_value]
  · simp [h, __smtx_typeof_value]

/-- Derives `forall_body_bool` from `non_none`. -/
theorem forall_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  simpa [native_Teq] using hEq

/-- Derives `forall_term_typeof` from `non_none`. -/
theorem forall_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof (SmtTerm.forall s T body) = SmtType.Bool := by
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    simpa [native_Teq] using forall_body_bool_of_non_none ht
  have hGuard : __smtx_typeof_guard_wf T SmtType.Bool = SmtType.Bool :=
    smtx_typeof_guard_wf_of_non_none T SmtType.Bool (by
      intro hNone
      unfold term_has_non_none_type at ht
      apply ht
      unfold __smtx_typeof
      simp [hEq, native_ite, hNone])
  unfold __smtx_typeof
  simp [hEq, native_ite, hGuard]

/-- Shows that evaluating `forall` terms produces values of the expected type. -/
theorem typeof_value_model_eval_forall
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.forall s T body)) =
      __smtx_typeof (SmtTerm.forall s T body) := by
  classical
  rw [forall_term_typeof_of_non_none ht]
  unfold __smtx_model_eval
  by_cases h :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical v = true ->
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · simp [dif_pos h, __smtx_typeof_value]
  · simp [dif_neg h, __smtx_typeof_value]

/-- Provides a witness for a `choice` term whose typing is non-`None`. -/
theorem choice_term_has_witness
    (Mw : SmtModel)
    (hMw : model_wf Mw)
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ value_canonical v := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold __smtx_typeof at ht
    simpa [hEq, native_ite] using ht
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  exact ⟨native_model_lookup Mw s T,
    model_total_typed_lookup hMw s T hWF,
    model_total_typed_lookup_canonical hMw s T hWF⟩

/-- Derives the `choice` type as the self-guarded choice type from `non_none`. -/
theorem choice_term_guard_type_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    __smtx_typeof (SmtTerm.choice s T body) = __smtx_typeof_guard_wf T T := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true := by
    by_cases hEq : native_Teq (__smtx_typeof body) SmtType.Bool = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof body) SmtType.Bool = false := by
        cases hTest : native_Teq (__smtx_typeof body) SmtType.Bool <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  unfold __smtx_typeof
  simp [hEq, native_ite]

/-- Derives `choice_term_typeof` from `non_none`. -/
theorem choice_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    __smtx_typeof (SmtTerm.choice s T body) = T := by
  have hGuard : __smtx_typeof (SmtTerm.choice s T body) = __smtx_typeof_guard_wf T T :=
    choice_term_guard_type_of_non_none ht
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at ht
    apply ht
    rw [hGuard, hNone]
  exact hGuard.trans (smtx_typeof_guard_wf_of_non_none T T hGuardNN)

/-- If a `choice` term has sequence type `Seq A`, then `A` is non-`None`. -/
theorem choice_term_seq_component_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.choice s T body) = SmtType.Seq A) :
    A ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.choice s T body) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard : __smtx_typeof_guard_wf T T = SmtType.Seq A := by
    calc
      __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice s T body) := by
        symm
        exact choice_term_guard_type_of_non_none hNN
      _ = SmtType.Seq A := h
  exact smtx_typeof_guard_wf_self_eq_seq_component_non_none hGuard

/-- If a `choice` term has set type `Set A`, then `A` is non-`None`. -/
theorem choice_term_set_component_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {A : SmtType}
    (h : __smtx_typeof (SmtTerm.choice s T body) = SmtType.Set A) :
    A ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.choice s T body) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard : __smtx_typeof_guard_wf T T = SmtType.Set A := by
    calc
      __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice s T body) := by
        symm
        exact choice_term_guard_type_of_non_none hNN
      _ = SmtType.Set A := h
  exact smtx_typeof_guard_wf_self_eq_set_component_non_none hGuard

/-- If a `choice` term has map type `Map A B`, then both components are non-`None`. -/
theorem choice_term_map_components_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {A B : SmtType}
    (h : __smtx_typeof (SmtTerm.choice s T body) = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.choice s T body) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard : __smtx_typeof_guard_wf T T = SmtType.Map A B := by
    calc
      __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice s T body) := by
        symm
        exact choice_term_guard_type_of_non_none hNN
      _ = SmtType.Map A B := h
  exact smtx_typeof_guard_wf_self_eq_map_components_non_none hGuard

/-- If a `choice` term has function type `FunType A B`, then both components are non-`None`. -/
theorem choice_term_fun_components_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {A B : SmtType}
    (h : __smtx_typeof (SmtTerm.choice s T body) = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : term_has_non_none_type (SmtTerm.choice s T body) := by
    unfold term_has_non_none_type
    intro hNone
    rw [hNone] at h
    simp at h
  have hGuard : __smtx_typeof_guard_wf T T = SmtType.FunType A B := by
    calc
      __smtx_typeof_guard_wf T T = __smtx_typeof (SmtTerm.choice s T body) := by
        symm
        exact choice_term_guard_type_of_non_none hNN
      _ = SmtType.FunType A B := h
  exact smtx_typeof_guard_wf_self_eq_fun_components_non_none hGuard

/-- Shows that evaluating `choice` terms produces values of the expected type. -/
theorem typeof_value_model_eval_choice
    (Mw : SmtModel)
    (hMw : model_wf Mw)
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.choice s T body)) =
      __smtx_typeof (SmtTerm.choice s T body) := by
  classical
  have hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
      __smtx_value_canonical v = true := by
    rcases choice_term_has_witness Mw hMw ht with ⟨v, hvTy, hvCanon⟩
    exact ⟨v, hvTy, by simpa [value_canonical] using hvCanon⟩
  have hTyIf : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
      __smtx_value_canonical v := by
    rcases hTy with ⟨v, hvTy, hvCanon⟩
    exact ⟨v, hvTy, by simp [hvCanon]⟩
  rw [choice_term_typeof_of_non_none ht]
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · rw [smtx_model_eval_choice_eq]
    simp [hSat]
    exact (Classical.choose_spec hSat).1
  · rw [smtx_model_eval_choice_eq]
    simp [hSat, hTyIf]
    exact (Classical.choose_spec hTy).1

/-- Extracts inhabitation of the computed `choice` type from a non-`None` typing judgment. -/
theorem choice_term_inhabited_of_non_none
    (Mw : SmtModel)
    (hMw : model_wf Mw)
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.choice s T body)) :
    type_inhabited (__smtx_typeof (SmtTerm.choice s T body)) := by
  refine ⟨__smtx_model_eval Mw (SmtTerm.choice s T body), ?_⟩
  simpa using typeof_value_model_eval_choice Mw hMw Mw s T body ht

/-- Type of a `bind` term equals the (guarded) type of its body when well-typed. -/
theorem bind_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {x1 x2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2)) :
    __smtx_typeof (SmtTerm.bind s T x1 x2) = __smtx_typeof x2 := by
  unfold term_has_non_none_type at ht
  have hEq : native_Teq (__smtx_typeof x1) T = true := by
    by_cases hEq : native_Teq (__smtx_typeof x1) T = true
    · exact hEq
    · exfalso
      have hEqFalse : native_Teq (__smtx_typeof x1) T = false := by
        cases hTest : native_Teq (__smtx_typeof x1) T <;> simp [hTest] at hEq ⊢
      apply ht
      unfold __smtx_typeof
      simp [hEqFalse, native_ite]
  have hGuardNN : __smtx_typeof_guard_wf T (__smtx_typeof x2) ≠ SmtType.None := by
    unfold __smtx_typeof at ht
    simpa [hEq, native_ite] using ht
  have hGuard : __smtx_typeof_guard_wf T (__smtx_typeof x2) = __smtx_typeof x2 :=
    smtx_typeof_guard_wf_of_non_none T (__smtx_typeof x2) hGuardNN
  have hLHS : __smtx_typeof (SmtTerm.bind s T x1 x2)
      = __smtx_typeof_guard_wf T (__smtx_typeof x2) := by
    rw [__smtx_typeof.eq_def]
    simp [hEq, native_ite]
  rw [hLHS]
  exact hGuard

/-- The bound value of a well-typed `bind` has the binder type. -/
theorem bind_arg1_type_of_non_none
    {s : native_String} {T : SmtType} {x1 x2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2)) :
    __smtx_typeof x1 = T := by
  unfold term_has_non_none_type at ht
  by_cases hEq : native_Teq (__smtx_typeof x1) T = true
  · exact of_decide_eq_true (by simpa [native_Teq] using hEq)
  · exfalso
    have hEqFalse : native_Teq (__smtx_typeof x1) T = false := by
      cases hTest : native_Teq (__smtx_typeof x1) T <;> simp [hTest] at hEq ⊢
    apply ht
    unfold __smtx_typeof
    simp [hEqFalse, native_ite]

/-- The binder type of a well-typed `bind` is well formed. -/
theorem bind_binder_type_wf_of_non_none
    {s : native_String} {T : SmtType} {x1 x2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2)) :
    __smtx_type_wf T = true := by
  have hEq : native_Teq (__smtx_typeof x1) T = true := by
    simp [native_Teq, bind_arg1_type_of_non_none ht]
  unfold term_has_non_none_type at ht
  have hGuardNN : __smtx_typeof_guard_wf T (__smtx_typeof x2) ≠ SmtType.None := by
    unfold __smtx_typeof at ht
    simpa [hEq, native_ite] using ht
  exact smtx_typeof_guard_wf_wf_of_non_none T (__smtx_typeof x2) hGuardNN

/-- The bound value of a well-typed `bind` has non-`None` type. -/
theorem bind_arg1_non_none_of_non_none
    {s : native_String} {T : SmtType} {x1 x2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2)) :
    term_has_non_none_type x1 := by
  unfold term_has_non_none_type
  rw [bind_arg1_type_of_non_none ht]
  intro hNone
  have hWf := bind_binder_type_wf_of_non_none ht
  rw [hNone] at hWf
  exact absurd hWf (by native_decide)

/-- The body of a well-typed `bind` has non-`None` type. -/
theorem bind_arg2_non_none_of_non_none
    {s : native_String} {T : SmtType} {x1 x2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2)) :
    term_has_non_none_type x2 := by
  have hEq := bind_term_typeof_of_non_none ht
  unfold term_has_non_none_type at ht ⊢
  rw [hEq] at ht
  exact ht

/-- Shows that evaluating a `bind` (let) term produces a value of the expected
type, given type preservation for the body `x2` under the pushed model.  The
caller supplies `hx2` (via canonicity preservation of `x1` so that the pushed
model stays `model_wf`); `bind` is the only construct whose result type
is the body's type under a pushed binding, so it needs this extra input. -/
theorem typeof_value_model_eval_bind
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (x1 x2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.bind s T x1 x2))
    (hx2 :
      __smtx_typeof_value
          (__smtx_model_eval (native_model_push M s T (__smtx_model_eval M x1)) x2) =
        __smtx_typeof x2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.bind s T x1 x2)) =
      __smtx_typeof (SmtTerm.bind s T x1 x2) := by
  rw [smtx_model_eval_bind_eq, bind_term_typeof_of_non_none ht]
  exact hx2


end Smtm
