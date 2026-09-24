module

import Lean
public import CpcMini.Proofs.TypePreservation.Model
import all CpcMini.Proofs.TypePreservation.Model

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
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `numeral` terms produces values of the expected type. -/
theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : native_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

/-- Shows that evaluating `rational` terms produces values of the expected type. -/
theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := by
  simp [__smtx_model_eval, __smtx_typeof, __smtx_typeof_value]

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
    by_cases h : g = true
    · exact h
    · exfalso
      apply ht
      simp [__smtx_typeof, g, native_ite, h]
  have hWidth : native_zleq 0 w = true := by
    cases h1 : native_zleq 0 w
    · simp [g, SmtEval.native_and, h1] at hg
    · rfl
  have hMod :
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases h2 : native_zeq n (native_mod_total n (native_int_pow2 w))
    · simp [g, SmtEval.native_and, hWidth, h2] at hg
    · rfl
  simp [__smtx_model_eval, __smtx_typeof_value, __smtx_typeof, native_ite, SmtEval.native_and, hWidth, hMod]

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
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  simpa [__smtx_model_eval, __smtx_typeof] using
    (Eq.trans (model_total_typed_var_lookup hM s T hWF) hGuard.symm)

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
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  have hWF : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T (by
      simpa [term_has_non_none_type, __smtx_typeof] using ht)
  simpa [__smtx_model_eval, __smtx_typeof] using
    (Eq.trans (model_total_typed_lookup hM s T hWF) hGuard.symm)

/-- Derives `exists_body_bool` from `non_none`. -/
theorem exists_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht ⊢

/-- Derives `exists_term_typeof` from `non_none`. -/
theorem exists_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool := by
  have hBody : __smtx_typeof body = SmtType.Bool :=
    exists_body_bool_of_non_none ht
  have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof, native_ite, native_Teq, hBody] using ht
  simp [__smtx_typeof, native_ite, native_Teq, hBody,
    smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN]

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
  by_cases h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical v = true ∧
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · unfold __smtx_model_eval
    simp [h, __smtx_typeof_value]
  · unfold __smtx_model_eval
    simp [h, __smtx_typeof_value]

/-- Derives `forall_body_bool` from `non_none`. -/
theorem forall_body_bool_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, native_ite, native_Teq, h] at ht ⊢

/-- Derives `forall_term_typeof` from `non_none`. -/
theorem forall_term_typeof_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    __smtx_typeof (SmtTerm.forall s T body) = SmtType.Bool := by
  have hBody : __smtx_typeof body = SmtType.Bool :=
    forall_body_bool_of_non_none ht
  have hGuardNN : __smtx_typeof_guard_wf T SmtType.Bool ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof, native_ite, native_Teq, hBody] using ht
  simp [__smtx_typeof, native_ite, native_Teq, hBody,
    smtx_typeof_guard_wf_of_non_none T SmtType.Bool hGuardNN]

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
  by_cases h :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical v = true ->
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · unfold __smtx_model_eval
    simp [dif_pos h, __smtx_typeof_value]
  · unfold __smtx_model_eval
    simp [dif_neg h, __smtx_typeof_value]

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
