module

public import Cpc.SmtModel
import all Cpc.SmtModel

public section

open SmtEval

set_option linter.unusedSimpArgs false

namespace Smtm

/-!
# Inhabitation and the default generator

The checker decides inhabitation structurally, with `native_inhabited_type`,
and never constructs a value. This file connects that check to the semantic
default generator `__smtx_type_default`:

* `native_inhabited_type_iff`: the check succeeds exactly when the generator
  constructs a value. This holds for every type, malformed declarations
  included.
* `type_default_typed`: on a recursively well-formed type, that value has the
  requested type.
-/

/-- The type a constructor field has once a reference to a datatype of the
declaration `dd` is resolved, as `__smtx_dtc_resolve` resolves it. -/
private def fieldType (dd : SmtDatatypeDecl) : SmtType -> SmtType
  | SmtType.TypeRef s => SmtType.Datatype s dd
  | T => T

/-- Inhabitation of one constructor field, as `__smtx_dt_cons_inhabited` checks it. -/
private def fieldInhabited (ddF : SmtDatatypeDecl) : SmtType -> native_Bool
  | SmtType.TypeRef s => __smtx_decl_inhabited s ddF
  | T => native_inhabited_type T

private theorem dt_cons_inhabited_cons (T : SmtType) (c : SmtDatatypeCons)
    (ddF : SmtDatatypeDecl) :
    __smtx_dt_cons_inhabited (SmtDatatypeCons.cons T c) ddF =
      native_and (fieldInhabited ddF T) (__smtx_dt_cons_inhabited c ddF) := by
  cases T <;> simp [__smtx_dt_cons_inhabited, fieldInhabited]

private theorem dtc_resolve_cons (T : SmtType) (c : SmtDatatypeCons)
    (dd : SmtDatatypeDecl) :
    __smtx_dtc_resolve (SmtDatatypeCons.cons T c) dd =
      SmtDatatypeCons.cons (fieldType dd T) (__smtx_dtc_resolve c dd) := by
  cases T <;> simp [__smtx_dtc_resolve, fieldType]

theorem native_inhabited_type_ne_none {T : SmtType}
    (h : native_inhabited_type T = true) : T ≠ SmtType.None := by
  rintro rfl
  simp [native_inhabited_type] at h

/-- The structural check succeeds exactly when the generator constructs a value. -/
theorem native_inhabited_type_iff : ∀ T : SmtType,
    native_inhabited_type T = true ↔ __smtx_type_default T ≠ SmtValue.NotValue := by
  refine __smtx_type_default.induct
    (motive1 := fun T =>
      native_inhabited_type T = true ↔ __smtx_type_default T ≠ SmtValue.NotValue)
    (motive2 := fun s dd ddF =>
      __smtx_decl_inhabited s ddF = true ↔
        __smtx_datatype_decl_default s dd ddF ≠ SmtValue.NotValue)
    (motive3 := fun s dd n dF ddF =>
      __smtx_dt_inhabited dF ddF = true ↔
        __smtx_datatype_default s dd n dF ddF ≠ SmtValue.NotValue)
    (motive4 := fun v dd c ddF =>
      v ≠ SmtValue.NotValue →
        (__smtx_dt_cons_inhabited c ddF = true ↔
          __smtx_datatype_cons_default v dd c ddF ≠ SmtValue.NotValue))
    (motive5 := fun dd T ddF =>
      fieldInhabited ddF T = true ↔
        __smtx_field_type_default dd T ddF ≠ SmtValue.NotValue)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  any_goals simp [native_inhabited_type, __smtx_type_default]; done
  case refine_6 T U ih =>
    by_cases h : __smtx_type_default U = SmtValue.NotValue <;>
      simp_all [native_inhabited_type, __smtx_type_default, native_ite, native_veq]
  case refine_10 s dd ih =>
    simpa [native_inhabited_type, __smtx_type_default] using ih
  case refine_13 T _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases T <;> simp_all [native_inhabited_type, __smtx_type_default]
  case refine_14 s dd sF dF ddF ihDt ihDecl =>
    by_cases h : native_streq s sF = true <;>
      simp_all [__smtx_decl_inhabited, __smtx_datatype_decl_default, native_ite]
  case refine_15 s dd ddF hnone =>
    cases ddF with
    | nil => simp [__smtx_decl_inhabited, __smtx_datatype_decl_default]
    | cons sF dF tail => exact (hnone sF dF tail rfl).elim
  case refine_16 s dd n cF dF ddF ihCons ihTail =>
    have hCons := ihCons (by simp)
    by_cases h : __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF =
        SmtValue.NotValue <;>
      simp_all [__smtx_dt_inhabited, __smtx_datatype_default, native_ite,
        native_not, native_veq, native_or]
  case refine_17 s dd n dF ddF hnone =>
    cases dF with
    | null => simp [__smtx_dt_inhabited, __smtx_datatype_default]
    | sum c tail => exact (hnone c tail rfl).elim
  case refine_18 v dd ddF hv =>
    simp [__smtx_dt_cons_inhabited, __smtx_datatype_cons_default, hv]
  case refine_19 v dd T c ddF f ihField ihTail hv =>
    have hTail := ihTail (by simp)
    dsimp only [f] at hTail
    rw [dt_cons_inhabited_cons, __smtx_datatype_cons_default]
    by_cases h : __smtx_field_type_default dd T ddF = SmtValue.NotValue <;>
      simp_all [native_ite, native_veq, native_and]
  case refine_20 dd s ddF ih =>
    simpa [fieldInhabited, __smtx_field_type_default] using ih
  case refine_21 dd T ddF hnotref ih =>
    cases T <;> simp_all [fieldInhabited, __smtx_field_type_default]

/-- Every datatype named in `ddF` is looked up in `dd` as it is in `ddF`. This
holds for `ddF = dd`, and for each suffix of a declaration with distinct names. -/
private def LookupAgrees (dd ddF : SmtDatatypeDecl) : Prop :=
  ∀ s, __smtx_dd_has_dt s ddF = true → __smtx_dd_lookup s dd = __smtx_dd_lookup s ddF

private theorem lookupAgrees_tail {dd : SmtDatatypeDecl} {sF : native_String}
    {dF : SmtDatatype} {ddF : SmtDatatypeDecl}
    (h : LookupAgrees dd (SmtDatatypeDecl.cons sF dF ddF))
    (hFresh : __smtx_dd_has_dt sF ddF = false) :
    LookupAgrees dd ddF := by
  intro s hs
  have hne : native_streq s sF = false := by
    cases hEq : native_streq s sF
    · rfl
    · simp [native_streq] at hEq
      subst hEq
      simp [hFresh] at hs
  have := h s (by simp [__smtx_dd_has_dt, native_or, hs])
  simpa [__smtx_dd_lookup, native_ite, hne] using this

/-- On a recursively well-formed type, the generated default has the requested type. -/
theorem type_default_typed : ∀ T : SmtType,
    native_inhabited_type T = true →
    __smtx_type_wf_rec T = true →
    __smtx_typeof_value (__smtx_type_default T) = T := by
  refine __smtx_type_default.induct
    (motive1 := fun T =>
      native_inhabited_type T = true →
      __smtx_type_wf_rec T = true →
      __smtx_typeof_value (__smtx_type_default T) = T)
    (motive2 := fun s dd ddF =>
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      __smtx_datatype_decl_default s dd ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_datatype_decl_default s dd ddF) =
        SmtType.Datatype s dd)
    (motive3 := fun s dd n dF ddF =>
      __smtx_dt_wf_rec dd dF = true →
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      (∀ m, __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd)
          (__smtx_dt_resolve (__smtx_dd_lookup s dd) dd) (n + m) =
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s dd)
          (__smtx_dt_resolve dF dd) m) →
      __smtx_datatype_default s dd n dF ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_datatype_default s dd n dF ddF) =
        SmtType.Datatype s dd)
    (motive4 := fun v dd c ddF =>
      __smtx_dt_cons_wf_rec dd c = true →
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      ∀ R d, __smtx_typeof_value v =
          __smtx_typeof_dt_cons_value_rec R
            (SmtDatatype.sum (__smtx_dtc_resolve c dd) d) 0 →
      __smtx_datatype_cons_default v dd c ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_datatype_cons_default v dd c ddF) = R)
    (motive5 := fun dd T ddF =>
      __smtx_decl_wf_rec dd ddF = true →
      LookupAgrees dd ddF →
      ((∃ s, T = SmtType.TypeRef s) ∨
        (native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true)) →
      __smtx_field_type_default dd T ddF ≠ SmtValue.NotValue →
      __smtx_typeof_value (__smtx_field_type_default dd T ddF) = fieldType dd T)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals intros
  any_goals
    simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
      __smtx_typeof_seq_value, __smtx_map_to_set_type, native_ite, native_and,
      native_nat_to_int, native_zleq, native_zeq, native_mod_total,
      native_int_to_nat, native_char_valid]; done
  case refine_6 T U ih hInh hRec =>
    have hU : native_inhabited_type U = true ∧ __smtx_type_wf_rec U = true := by
      simp_all [__smtx_type_wf_rec, native_and, native_inhabited_type]
    have hne := (native_inhabited_type_iff U).1 hU.1
    simp [__smtx_type_default, native_ite, native_veq, hne, __smtx_typeof_value,
      __smtx_typeof_map_value, ih hU.1 hU.2]
  case refine_10 s dd ih hInh hRec =>
    have hDecl : __smtx_decl_wf_rec dd dd = true := by
      simp_all [__smtx_type_wf_rec, native_and]
    have hne := (native_inhabited_type_iff (SmtType.Datatype s dd)).1 hInh
    simp only [__smtx_type_default] at hne ⊢
    exact ih hDecl (fun _ _ => rfl) hne
  case refine_13 T _ _ _ _ _ _ _ _ _ _ _ _ hInh _ =>
    cases T <;> simp_all [native_inhabited_type]
  case refine_14 s dd sF dF ddF ihDt ihDecl hWf hAgree hne =>
    have hParts :
        __smtx_dt_wf_rec dd dF = true ∧
        native_inhabited_type (SmtType.Datatype sF dd) = true ∧
        __smtx_decl_wf_rec dd ddF = true ∧
        __smtx_dd_has_dt sF ddF = false := by
      simpa [__smtx_decl_wf_rec, native_and, native_not] using hWf
    have hTail := lookupAgrees_tail hAgree hParts.2.2.2
    by_cases hs : native_streq s sF = true
    · have hsF : s = sF := by simpa [native_streq] using hs
      subst hsF
      have hLookup : __smtx_dd_lookup s dd = dF := by
        rw [hAgree s (by simp [__smtx_dd_has_dt, native_or, native_streq])]
        simp [__smtx_dd_lookup, native_ite, native_streq]
      simp only [__smtx_datatype_decl_default, native_ite, hs, ite_true] at hne ⊢
      exact ihDt hParts.1 hParts.2.2.1 hTail (by simp [hLookup]) hne
    · simp only [__smtx_datatype_decl_default, native_ite, hs] at hne ⊢
      simp only [Bool.false_eq_true, ite_false] at hne ⊢
      exact ihDecl hParts.2.2.1 hTail hne
  case refine_15 s dd ddF hnone _ _ hne =>
    cases ddF with
    | nil => simp [__smtx_datatype_decl_default] at hne
    | cons sF dF tail => exact (hnone sF dF tail rfl).elim
  case refine_16 s dd n cF dF ddF ihCons ihTail hDt hDecl hAgree hIdx hne =>
    have hParts :
        __smtx_dt_cons_wf_rec dd cF = true ∧ __smtx_dt_wf_rec dd dF = true := by
      simpa [__smtx_dt_wf_rec, native_and] using hDt
    rw [__smtx_datatype_default] at hne ⊢
    by_cases hv : __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF =
        SmtValue.NotValue
    · simp only [hv, native_ite, native_not, native_veq, decide_true,
        Bool.not_true, Bool.false_eq_true, ite_false] at hne ⊢
      refine ihTail hParts.2 hDecl hAgree (fun m => ?_) hne
      have := hIdx (m + 1)
      rw [show n + (m + 1) = Nat.succ n + m from (Nat.succ_add n m).symm] at this
      simpa [__smtx_dt_resolve, __smtx_typeof_dt_cons_value_rec] using this
    · simp only [native_ite, native_not, native_veq, hv, decide_false,
        Bool.not_false, ite_true]
      refine ihCons hParts.1 hDecl hAgree _ (__smtx_dt_resolve dF dd) ?_ hv
      have := hIdx 0
      simpa [__smtx_typeof_value, __smtx_dt_resolve] using this
  case refine_17 s dd n dF ddF hnone _ _ _ _ hne =>
    cases dF with
    | null => simp [__smtx_datatype_default] at hne
    | sum c tail => exact (hnone c tail rfl).elim
  case refine_18 v dd ddF _ _ _ R d hv _ =>
    simpa [__smtx_datatype_cons_default, __smtx_dtc_resolve,
      __smtx_typeof_dt_cons_value_rec] using hv
  case refine_19 v dd T c ddF f ihField ihTail hCons hDecl hAgree R d hv hne =>
    dsimp only [f] at ihTail
    have hField :
        ((∃ s, T = SmtType.TypeRef s) ∨
          (native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true)) ∧
        __smtx_dt_cons_wf_rec dd c = true := by
      cases T <;> simp_all [__smtx_dt_cons_wf_rec, native_and]
    have hFieldNe : fieldType dd T ≠ SmtType.None := by
      rcases hField.1 with ⟨s, rfl⟩ | ⟨hInh, _⟩
      · simp [fieldType]
      · have := native_inhabited_type_ne_none hInh
        cases T <;> simp_all [fieldType]
    rw [__smtx_datatype_cons_default] at hne ⊢
    by_cases hf : __smtx_field_type_default dd T ddF = SmtValue.NotValue
    · simp [hf, native_ite, native_veq] at hne
    · simp only [native_ite, native_veq, hf, decide_false, Bool.false_eq_true,
        ite_false] at hne ⊢
      refine ihTail hField.2 hDecl hAgree R d ?_ hne
      rw [dtc_resolve_cons] at hv
      simp [__smtx_typeof_value, hv, ihField hDecl hAgree hField.1 hf,
        __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
        __smtx_typeof_guard, native_ite, native_Teq, hFieldNe]
  case refine_20 dd s ddF ih hDecl hAgree _ hne =>
    simp only [__smtx_field_type_default] at hne
    simpa [__smtx_field_type_default, fieldType] using ih hDecl hAgree hne
  case refine_21 dd T ddF hnotref ih hDecl hAgree hField hne =>
    rcases hField with ⟨s, hs⟩ | ⟨hInh, hRec⟩
    · exact absurd hs (hnotref s)
    · have h := ih hInh hRec
      cases T <;> simp_all [__smtx_field_type_default, fieldType]

end Smtm
