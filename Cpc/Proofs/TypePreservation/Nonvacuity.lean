module

public import Cpc.Proofs.TypePreservation.Model
import all Cpc.Proofs.TypePreservation.Model

public section

open SmtEval
open Smtm

namespace Smtm

/-- Choice-based model from canonical witnesses for every well-formed SMT type. -/
noncomputable def default_typed_model_of
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ value_canonical v) :
    SmtModel := by
  classical
  exact
    { values := fun k =>
        if hWF : __smtx_type_wf k.ty = true then
          Classical.choose (hCan k.ty hWF)
        else
          SmtValue.NotValue
      nativeFuns := fun k =>
        match k.ty with
        | SmtType.FunType _ U => fun _ => __smtx_type_default U
        | _ => fun _ => SmtValue.NotValue }

private theorem default_typed_model_of_native_fun_typed
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ value_canonical v) :
    model_fun_wf (default_typed_model_of hCan) := by
  intro fid A B i hFunWF hi
  have hBWF : __smtx_type_wf B = true :=
    (fun_type_wf_components_of_wf hFunWF).2
  have hDefault :=
    type_default_typed_canonical_of_type_wf B hBWF
  have hDefaultCan :
      __smtx_value_canonical (__smtx_type_default B) = true := by
    simpa [value_canonical] using hDefault.2
  by_cases hDefaultId : fid = native_default_fun_id
  · simp [native_eval_fun_apply, hDefaultId, hDefault.1, hDefaultCan]
  · simp [native_eval_fun_apply, model_fun_lookup,
      default_typed_model_of, model_key, hDefaultId, hDefault.1, hDefaultCan]

/--
Reduces nonvacuity of total typed models to the canonical-inhabitant theorem
for well-formed SMT types.
-/
theorem exists_total_typed_model_of_canonical_type_inhabited
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ value_canonical v) :
    ∃ M : SmtModel, model_wf M := by
  classical
  refine ⟨default_typed_model_of hCan, ?_⟩
  constructor
  · intro isVar s T hT
    simp [default_typed_model_of, hT,
      (Classical.choose_spec (hCan T hT)).1]
  · constructor
    · intro isVar s T hT
      have hSpec := Classical.choose_spec (hCan T hT)
      simpa [default_typed_model_of, hT, value_canonical]
        using hSpec.2
    · exact default_typed_model_of_native_fun_typed hCan

/-- Choice-based model that returns a canonical inhabitant for every well-formed SMT type. -/
noncomputable def default_typed_model : SmtModel :=
  default_typed_model_of canonical_type_inhabited_of_type_wf

/-- Shows that `default_typed_model` is total and type-correct on every well-formed SMT type. -/
theorem default_typed_model_total_typed :
    model_wf default_typed_model := by
  classical
  unfold default_typed_model
  constructor
  · intro isVar s T hT
    simp [default_typed_model_of, hT,
      (Classical.choose_spec (canonical_type_inhabited_of_type_wf T hT)).1]
  · constructor
    · intro isVar s T hT
      have hSpec := Classical.choose_spec (canonical_type_inhabited_of_type_wf T hT)
      simpa [default_typed_model_of, hT, value_canonical]
        using hSpec.2
    · exact default_typed_model_of_native_fun_typed canonical_type_inhabited_of_type_wf

/-- Constructs a total typed SMT model. -/
theorem exists_total_typed_model :
    ∃ M : SmtModel, model_wf M :=
  ⟨default_typed_model, default_typed_model_total_typed⟩

/-- Shows that total typed SMT models exist. -/
theorem model_wf_nonvacuous :
    ∃ M : SmtModel, model_wf M :=
  exists_total_typed_model

end Smtm
