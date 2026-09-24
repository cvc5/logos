module

public import Cpc.SmtModel
import all Cpc.SmtModel

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm

/-!
Basic facts about the declaration-based default generator.

Constructor defaults are assembled from canonical field defaults.  After the
result-type guard was removed from `__smtx_datatype_default`, this invariant is
valid for recursively well-formed types rather than for arbitrary malformed
declaration lists.  That is exactly the condition under which generated
defaults are used by the model.
-/

private theorem type_default_canonical_kernel : ∀ T : SmtType,
    native_inhabited_type T = true →
    __smtx_type_wf_rec T = true →
    __smtx_value_canonical (__smtx_type_default T) = true := by
  refine __smtx_type_default.induct
    (motive1 := fun T =>
      native_inhabited_type T = true →
      __smtx_type_wf_rec T = true →
      __smtx_value_canonical (__smtx_type_default T) = true)
    (motive2 := fun s dd ddF =>
      __smtx_decl_wf_rec dd ddF = true →
      __smtx_value_canonical
        (__smtx_datatype_decl_default s dd ddF) = true)
    (motive3 := fun s dd n dF ddF =>
      __smtx_dt_wf_rec dd dF = true →
      __smtx_decl_wf_rec dd ddF = true →
      __smtx_value_canonical
        (__smtx_datatype_default s dd n dF ddF) = true)
    (motive4 := fun v dd c ddF =>
      __smtx_dt_cons_wf_rec dd c = true →
      __smtx_decl_wf_rec dd ddF = true →
      __smtx_value_canonical v = true →
      __smtx_value_canonical
        (__smtx_datatype_cons_default v dd c ddF) = true)
    (motive5 := fun dd T ddF =>
      __smtx_decl_wf_rec dd ddF = true →
      ((∃ s, T = SmtType.TypeRef s) ∨
        (native_inhabited_type T = true ∧
         __smtx_type_wf_rec T = true)) →
      __smtx_value_canonical
        (__smtx_field_type_default dd T ddF) = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros
    simp [__smtx_type_default, __smtx_value_canonical]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical,
      __smtx_re_canonical, native_re_none]
  · intro w _hInh _hRec
    simp [__smtx_type_default, __smtx_value_canonical,
      native_nat_to_int, native_and, native_zleq, native_zeq, native_mod_total,
      native_int_to_nat, native_ite]
  · intro T U ih _hInh hRec
    have hRaw :
        (native_inhabited_type T = true ∧
         __smtx_type_wf_rec T = true) ∧
        (native_inhabited_type U = true ∧
         __smtx_type_wf_rec U = true) := by
      simpa [__smtx_type_wf_rec, native_and] using hRec
    have hParts :
        native_inhabited_type T = true ∧
        __smtx_type_wf_rec T = true ∧
        native_inhabited_type U = true ∧
        __smtx_type_wf_rec U = true :=
      ⟨hRaw.1.1, hRaw.1.2, hRaw.2.1, hRaw.2.2⟩
    have hFieldCan :
        __smtx_value_canonical (__smtx_type_default U) = true :=
      ih hParts.2.2.1 hParts.2.2.2
    have hFieldTy :
        __smtx_typeof_value (__smtx_type_default U) = U := by
      have h := hParts.2.2.1
      simp [native_inhabited_type, native_and, native_not, native_Teq] at h
      exact h.2
    rw [__smtx_type_default]
    by_cases hv :
        native_veq (__smtx_type_default U) SmtValue.NotValue = true
    · rw [native_ite, if_pos hv]
      simp [__smtx_value_canonical]
    · rw [native_ite, if_neg hv]
      simp [__smtx_value_canonical, __smtx_map_canonical,
        __smtx_map_default_canonical, hFieldTy, hFieldCan, native_ite,
        native_veq, native_and]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical,
      __smtx_map_canonical, __smtx_map_default_canonical,
      __smtx_map_get_default, native_and, native_veq, native_ite,
      __smtx_typeof_value]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical,
      __smtx_seq_canonical]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical,
      native_char_valid, native_ite]
  · intro s dd ih _hInh hRec
    have hDecl : __smtx_decl_wf_rec dd dd = true := by
      have h := hRec
      simp [__smtx_type_wf_rec, native_and] at h
      exact h.2
    simpa [__smtx_type_default] using ih hDecl
  · intros
    simp [__smtx_type_default, __smtx_value_canonical]
  · intros
    simp [__smtx_type_default, __smtx_value_canonical]
  · intro T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _hInh hRec
    cases T <;> simp_all [__smtx_type_default, __smtx_type_wf_rec,
      __smtx_value_canonical]
  · intro s dd sF dF ddF ihDt ihDecl hWf
    have hParts :
        __smtx_dt_wf_rec dd dF = true ∧
        native_inhabited_type (SmtType.Datatype sF dd) = true ∧
        __smtx_decl_wf_rec dd ddF = true ∧
        native_not (__smtx_dd_has_dt sF ddF) = true := by
      simpa [__smtx_decl_wf_rec, native_and] using hWf
    rw [__smtx_datatype_decl_default]
    by_cases hs : native_streq s sF = true
    · simpa [native_ite, hs] using ihDt hParts.1 hParts.2.2.1
    · simpa [native_ite, hs] using ihDecl hParts.2.2.1
  · intro s dd ddF hnone hWf
    cases ddF with
    | nil => simp [__smtx_datatype_decl_default, __smtx_value_canonical]
    | cons sF dF tail => exact (hnone sF dF tail rfl).elim
  · intro s dd n cF dF ddF ihCons ihTail hDtWf hDeclWf
    have hParts :
        __smtx_dt_cons_wf_rec dd cF = true ∧
        __smtx_dt_wf_rec dd dF = true := by
      simpa [__smtx_dt_wf_rec, native_and] using hDtWf
    rw [__smtx_datatype_default]
    let result :=
      __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF
    by_cases hv : native_veq result SmtValue.NotValue = true
    · have hTailCan := ihTail hParts.2 hDeclWf
      simpa [result, native_ite, native_not, hv] using hTailCan
    · have hResultCan := ihCons hParts.1 hDeclWf (by
        simp [__smtx_value_canonical])
      simpa [result, native_ite, native_not, hv] using hResultCan
  · intro s dd n dF ddF hnone _hDtWf _hDeclWf
    cases dF with
    | null =>
        simp [__smtx_datatype_default, __smtx_value_canonical]
    | sum c tail => exact (hnone c tail rfl).elim
  · intro v dd ddF _hCons _hDecl hCan
    simpa [__smtx_datatype_cons_default] using hCan
  · intro v dd T c ddF field ihField ihTail hCons hDecl hCan
    have hFieldPrem :
        (∃ s, T = SmtType.TypeRef s) ∨
          (native_inhabited_type T = true ∧
           __smtx_type_wf_rec T = true) := by
      by_cases hRef : ∃ s, T = SmtType.TypeRef s
      · exact Or.inl hRef
      · right
        cases T <;>
          simp_all [__smtx_dt_cons_wf_rec, native_and]
    have hTailWf : __smtx_dt_cons_wf_rec dd c = true := by
      cases T <;>
        simp_all [__smtx_dt_cons_wf_rec, native_and]
    have hFieldCan :
        __smtx_value_canonical field = true := by
      simpa only [field] using ihField hDecl hFieldPrem
    rw [__smtx_datatype_cons_default.eq_def]
    change __smtx_value_canonical
      (native_ite (native_veq field SmtValue.NotValue)
        SmtValue.NotValue
        (__smtx_datatype_cons_default (SmtValue.Apply v field) dd c ddF)) = true
    by_cases hv : native_veq field SmtValue.NotValue = true
    · rw [native_ite, if_pos hv]
      simp [__smtx_value_canonical]
    · rw [native_ite, if_neg hv]
      apply ihTail hTailWf hDecl
      simp [__smtx_value_canonical, hCan, hFieldCan, native_and]
  · intro dd s ddF ih hDecl _hField
    simpa [__smtx_field_type_default] using ih hDecl
  · intro dd T ddF hnotref ih hDecl hField
    rcases hField with hRef | ⟨hInh, hRec⟩
    · rcases hRef with ⟨s, hs⟩
      exact absurd hs (hnotref s)
    · simpa [__smtx_field_type_default, hnotref] using ih hInh hRec

/-- A recursively well-formed inhabited type has a typed, canonical default. -/
theorem type_default_kernel (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
    __smtx_value_canonical (__smtx_type_default T) = true := by
  have hTyped :
      native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true := by
    have h := hInh
    simp [native_inhabited_type, native_and] at h
    exact h.2
  exact ⟨by simpa [native_Teq] using hTyped,
    type_default_canonical_kernel T hInh hRec⟩

/-- The inhabitation check supplies the requested default type. -/
theorem type_default_typed_of_inhabited (T : SmtType)
    (hInh : native_inhabited_type T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T := by
  have hTyped :
      native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true := by
    have h := hInh
    simp [native_inhabited_type, native_and] at h
    exact h.2
  simpa [native_Teq] using hTyped

/-- A recursively well-formed inhabited default value is canonical. -/
theorem type_default_canonical_of_inhabited_wf_rec (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_value_canonical (__smtx_type_default T) = true :=
  type_default_canonical_kernel T hInh hRec

end Smtm
