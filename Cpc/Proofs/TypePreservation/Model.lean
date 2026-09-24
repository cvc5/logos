module

public import Cpc.Proofs.TypePreservation.Support
import all Cpc.Proofs.TypePreservation.Support

public section

open SmtEval
open Smtm

namespace Smtm

private theorem model_total_typed_lookup_canonical_bool
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical (native_model_lookup M s T) = true := by
  simpa [native_model_lookup, model_key] using
    hM.2.1 false s T hT

/-- Describes how `model_wf` behaves under lookup for well-formed types. -/
theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_model_lookup M s T) = T :=
  by
    simpa [native_model_lookup, model_key] using
      hM.1 false s T hT

/-- Describes how `model_wf` preserves canonical lookup values for well-formed types. -/
theorem model_total_typed_lookup_canonical
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    value_canonical (native_model_lookup M s T) :=
  by
    simpa [value_canonical]
      using model_total_typed_lookup_canonical_bool hM s T hT

/-- Describes how `model_wf` constrains native functions. -/
theorem model_total_typed_native_fun_typed
    {M : SmtModel}
    (hM : model_wf M) :
    model_fun_wf M :=
  hM.2.2

private theorem model_total_typed_var_lookup_canonical_bool
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical (native_model_var_lookup M s T) = true := by
  simpa [native_model_var_lookup] using
    hM.2.1 true s T hT

theorem model_total_typed_var_lookup
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (native_model_var_lookup M s T) = T := by
  simpa [native_model_var_lookup] using
    hM.1 true s T hT

theorem model_total_typed_var_lookup_canonical
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    value_canonical (native_model_var_lookup M s T) := by
  simpa [value_canonical]
    using model_total_typed_var_lookup_canonical_bool hM s T hT

/-- Describes how `model_typed_at` behaves under `push`. -/
theorem model_typed_at_push
    {M : SmtModel}
    {s : native_String}
    {T : SmtType}
    {v : SmtValue}
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (native_model_push M s T v) s T := by
  constructor
  · intro hT
    simp [native_model_var_lookup, native_model_push, hv]
  · intro hT
    rw [hWF] at hT
    cases hT

/-- Describes how `model_wf` behaves under `push`. -/
theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_wf M)
    (s : native_String)
    (T : SmtType)
    (v : SmtValue)
    (_hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T)
    (hvCanon : value_canonical v) :
    model_wf (native_model_push M s T v) := by
  constructor
  · intro isVar s' T' hT'
    by_cases hKey :
        ({ isVar := isVar, name := s', ty := T' } : SmtModelKey) =
          { isVar := true, name := s, ty := T }
    · cases hKey
      simp [native_model_push, hv]
    · simp [native_model_push, hKey]
      exact hM.1 isVar s' T' hT'
  · constructor
    · intro isVar s' T' hT'
      by_cases hKey :
          ({ isVar := isVar, name := s', ty := T' } : SmtModelKey) =
            { isVar := true, name := s, ty := T }
      · cases hKey
        simpa [native_model_push, value_canonical] using hvCanon
      · simp [native_model_push, hKey]
        exact hM.2.1 isVar s' T' hT'
    · intro fid A B i hFunWF hi
      simpa [model_fun_wf, native_eval_fun_apply, model_fun_lookup,
        native_model_push]
        using model_total_typed_native_fun_typed hM fid A B i hFunWF hi

/--
Datatype-default canonicity for the generated model.

The `native_inhabited_type` witness uniformly carries exactly this canonical
default witness for datatype types.
-/
theorem datatype_type_default_typed_canonical_of_inhabited
    (s : native_String)
    (d : SmtDatatypeDecl)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      value_canonical (__smtx_type_default (SmtType.Datatype s d)) :=
  type_default_typed_canonical_of_native_inhabited_type
    (SmtType.Datatype s d) _hInh _hRec

private theorem type_default_typed_canonical_of_wf_rec
    (T : SmtType) (hInh : native_inhabited_type T = true)
    (_hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      value_canonical (__smtx_type_default T) :=
  type_default_typed_canonical_of_native_inhabited_type T hInh _hRec

/-- The syntactic default is typed and canonical for every well-formed SMT
type, including curried function types. -/
theorem type_default_typed_canonical_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      value_canonical (__smtx_type_default T) := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    simp [__smtx_type_default, __smtx_typeof_value, value_canonical,
      __smtx_value_canonical]
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      simp [__smtx_type_default, __smtx_typeof_value, value_canonical,
        __smtx_value_canonical]
    · have hParts :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T = true := by
        cases T <;>
          simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
            native_and] at hWF hReg hFun ⊢ <;>
          first | exact hWF | exact hWF.1
      have hDef :=
        type_default_typed_canonical_of_wf_rec T hParts.1 hParts.2
      exact hDef

/-- Every well-formed SMT type has a canonical inhabitant. -/
theorem canonical_type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ value_canonical v := by
  exact ⟨__smtx_type_default T, type_default_typed_canonical_of_type_wf T hWF⟩

/-- The syntactic default is well-typed and canonical for recursively well-formed inhabited types. -/
theorem type_default_typed_canonical_of_inhabited_wf_rec
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      value_canonical (__smtx_type_default T) :=
  type_default_typed_canonical_of_wf_rec T hInh hRec

/-- The syntactic default is well-typed for types whose recursive well-formedness is known. -/
theorem type_default_typed_of_inhabited_wf_rec
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T :=
  (type_default_typed_canonical_of_inhabited_wf_rec T hInh hRec).1

end Smtm
