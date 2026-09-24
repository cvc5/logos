module

public meta import Cpc.Proofs.Translation.Base
import all Cpc.Spec
import all Cpc.Logos

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- The datatype names a translation has already entered, which the recursive
well-formedness predicates below carry along. This stood beside the model
until native trimming dropped it: nothing the checker runs reaches it, so it
lives here, where it is used. -/
abbrev RefList := List native_String

@[expose] def native_reflist_nil : RefList := []

@[expose] def native_reflist_insert (xs : RefList) (s : native_String) := (s :: xs)

@[expose] def native_reflist_contains (xs : RefList) (s : native_String) :=
  decide (s ∈ xs)

end Smtm

namespace TranslationProofs

attribute [local simp] native_ite
attribute [local simp] native_streq
attribute [local simp] native_and

@[simp] private theorem guarded_datatype_type_ne_bool
    (s : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Bool := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_bool
    (s : native_String) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Bool := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_int
    (s : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Int := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_int
    (s : native_String) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Int := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_real
    (s : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Real := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_real
    (s : native_String) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Real := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_reglan
    (s : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.RegLan := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_reglan
    (s : native_String) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.RegLan := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_char
    (s : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Char := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_char
    (s : native_String) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Char := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_bitvec
    (s : native_String) (d : SmtDatatypeDecl) (w : native_Nat) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.BitVec w := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_bitvec
    (s : native_String) (w : native_Nat) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.BitVec w := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_seq
    (s : native_String) (d : SmtDatatypeDecl) (A : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Seq A := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_seq
    (s : native_String) (A : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Seq A := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_set
    (s : native_String) (d : SmtDatatypeDecl) (A : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Set A := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_set
    (s : native_String) (A : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Set A := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_map
    (s : native_String) (d : SmtDatatypeDecl) (A B : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Map A B := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_map
    (s : native_String) (A B : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Map A B := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_fun
    (s : native_String) (d : SmtDatatypeDecl) (A B : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.FunType A B := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_fun
    (s : native_String) (A B : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.FunType A B := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_dtc_app
    (s : native_String) (d : SmtDatatypeDecl) (A B : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.DtcAppType A B := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_dtc_app
    (s : native_String) (A B : SmtType) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.DtcAppType A B := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_typeref
    (s r : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.TypeRef r := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_datatype
    (s r : native_String) (d : SmtDatatypeDecl) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Datatype r d := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_usort
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.USort i := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_usort
    (s : native_String) (i : native_Nat) :
    (if __eo_to_smt_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.USort i := by
  by_cases h : __eo_to_smt_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem smt_fun_choice_if_ne_none
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.None := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_bool
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Bool := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_int
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Int := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_real
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Real := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_reglan
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.RegLan := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_char
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Char := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_bitvec
    (T U : SmtType) (w : native_Nat) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.BitVec w := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_seq
    (T U A : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Seq A := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_set
    (T U A : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Set A := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_map
    (T U A B : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Map A B := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_typeref
    (T U : SmtType) (s : native_String) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.TypeRef s := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatypeDecl) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Datatype s d := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_dtc_app
    (T U A B : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.DtcAppType A B := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_usort
    (T U : SmtType) (i : native_Nat) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.USort i := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

/-- Well-formedness of a type occurring at a *field* position (a datatype-constructor field,
function argument, sequence/set/map element, …). Under the new algorithm this is exactly the
diagonal self-check `__smtx_type_wf_rec T T`; the ambient `refs` parameter is now vestigial
(kept only so existing call sites, many of which threaded a `RefList` that no longer carries any
scoping information, continue to type-check). -/
@[expose] def smtx_type_field_wf_rec (T : SmtType) (_refs : RefList) : Prop :=
  __smtx_type_wf_rec T = true

theorem smtx_type_field_wf_rec_of_type_wf_rec
    {T : SmtType} {refs : RefList}
    (h : __smtx_type_wf_rec T = true) :
    smtx_type_field_wf_rec T refs :=
  h

/-- Field well-formedness excludes `RegLan` at field/function-argument positions. -/
theorem smtx_type_field_wf_rec_ne_reglan
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) :
    T ≠ SmtType.RegLan := by
  intro hReg
  subst hReg
  simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h

/-- Extracts field well-formedness for a non-`TypeRef` head field from a well-formed constructor
whose full (substituted) side agrees with the raw head field (i.e. substitution was a no-op on it,
as it always is at non-`TypeRef` field positions since `__smtx_type_substitute` only ever rewrites a
bare `TypeRef` matching the substituted name). -/
theorem smtx_type_field_wf_rec_of_cons_wf
    {T : SmtType} {c : SmtDatatypeCons} {dd : SmtDatatypeDecl} {refs : RefList}
    (hNotRef : ∀ s, T ≠ SmtType.TypeRef s)
    (h : __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons T c) = true) :
    smtx_type_field_wf_rec T refs := by
  cases T with
  | TypeRef s => exact absurd rfl (hNotRef s)
  | _ =>
      simp [__smtx_dt_cons_wf_rec,
        native_and] at h
      exact h.1.2

theorem smtx_type_wf_rec_guard_of_true
    (T U : SmtType)
    (h : __smtx_type_wf_rec (__smtx_typeof_guard T U) = true) :
    __smtx_type_wf_rec U = true := by
  by_cases hNone : T = SmtType.None
  · exfalso
    simp [__smtx_typeof_guard, hNone, native_ite, native_Teq, __smtx_type_wf_rec] at h
  · have hGuard : __smtx_typeof_guard T U = U := by
      simp [__smtx_typeof_guard, native_ite, native_Teq, hNone]
    simpa [hGuard] using h

theorem seq_type_wf_rec_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Seq A) = true) :
    __smtx_type_wf_rec A = true := by
  have h' :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact h'.2

theorem seq_type_field_wf_rec_component_of_wf
    {A : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Seq A) refs) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  exact smtx_type_field_wf_rec_of_type_wf_rec
    (seq_type_wf_rec_component_of_wf (by
      simpa [smtx_type_field_wf_rec] using h))

theorem set_type_wf_rec_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Set A) = true) :
    __smtx_type_wf_rec A = true := by
  have h' :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact h'.2

theorem set_type_field_wf_rec_component_of_wf
    {A : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Set A) refs) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  exact smtx_type_field_wf_rec_of_type_wf_rec
    (set_type_wf_rec_component_of_wf (by
      simpa [smtx_type_field_wf_rec] using h))

theorem map_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Map A B) = true) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf_rec B = true := by
  have h' :
      (native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true) ∧
        (native_inhabited_type B = true ∧ __smtx_type_wf_rec B = true) := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact ⟨h'.1.2, h'.2.2⟩

theorem map_type_field_wf_rec_components_of_wf
    {A B : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Map A B) refs) :
    smtx_type_field_wf_rec A native_reflist_nil ∧
      smtx_type_field_wf_rec B native_reflist_nil := by
  rcases map_type_wf_rec_components_of_wf (by
    simpa [smtx_type_field_wf_rec] using h) with ⟨hA, hB⟩
  exact ⟨smtx_type_field_wf_rec_of_type_wf_rec hA,
    smtx_type_field_wf_rec_of_type_wf_rec hB⟩

theorem fun_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf B = true := by
  have h' := h
  simp [__smtx_type_wf, __smtx_type_wf_component, native_and] at h'
  exact ⟨h'.1.2, h'.2⟩

theorem fun_type_field_wf_rec_components_of_wf
    {A B : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.FunType A B) refs) :
    smtx_type_field_wf_rec A native_reflist_nil ∧
      smtx_type_field_wf_rec B native_reflist_nil := by
  simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h

theorem smtx_dt_cons_wf_rec_tail_of_true
    {T : SmtType} {c : SmtDatatypeCons} {dd : SmtDatatypeDecl}
    (h : __smtx_dt_cons_wf_rec dd (SmtDatatypeCons.cons T c) = true) :
    __smtx_dt_cons_wf_rec dd c = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_and] at h <;>
    exact h.2

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_bool
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Bool := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_int
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Int := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_real
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Real := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_reglan
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.RegLan := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_char
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Char := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_seq
    (n : native_Int) (A : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Seq A := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_set
    (n : native_Int) (A : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Set A := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_map
    (n : native_Int) (A B : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Map A B := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_fun
    (n : native_Int) (A B : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.FunType A B := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_usort
    (n : native_Int) (i : native_Nat) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.USort i := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_typeref
    (n : native_Int) (s : native_String) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.TypeRef s := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_bool`. -/
private theorem eo_to_smt_type_tuple_eq_none_or_datatype
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V = SmtType.None ∨
      ∃ dd : SmtDatatypeDecl,
        __eo_to_smt_type_tuple U V =
          SmtType.Datatype (native_string_lit "@Tuple") dd := by
  cases V <;> simp [__eo_to_smt_type_tuple]
  case Datatype s dd =>
    cases dd with
    | nil => simp
    | cons s2 d rest =>
      cases d with
      | null => simp
      | sum c dTail =>
        cases dTail with
        | sum c2 d2 => simp
        | null =>
          cases rest with
          | cons s3 d3 rest3 => simp
          | nil =>
            by_cases hs : s = native_string_lit "@Tuple"
            · by_cases hs2 : s2 = native_string_lit "@Tuple"
              · by_cases hU : __smtx_type_wf_component U = true <;>
                  simp [hs, hs2, hU]
              · simp [hs, hs2]
            · simp [hs]

theorem eo_to_smt_type_tuple_ne_bool
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Bool := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_int`. -/
theorem eo_to_smt_type_tuple_ne_int
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Int := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_real`. -/
theorem eo_to_smt_type_tuple_ne_real
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Real := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_reglan`. -/
theorem eo_to_smt_type_tuple_ne_reglan
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.RegLan := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_bitvec`. -/
theorem eo_to_smt_type_tuple_ne_bitvec
    (U V : SmtType) (w : native_Nat) :
    __eo_to_smt_type_tuple U V ≠ SmtType.BitVec w := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_char`. -/
theorem eo_to_smt_type_tuple_ne_char
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Char := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_seq`. -/
theorem eo_to_smt_type_tuple_ne_seq
    (U V W : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Seq W := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_set`. -/
theorem eo_to_smt_type_tuple_ne_set
    (U V W : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Set W := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_map`. -/
theorem eo_to_smt_type_tuple_ne_map
    (U V W X : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Map W X := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_fun`. -/
theorem eo_to_smt_type_tuple_ne_fun
    (U V A B : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.FunType A B := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

theorem eo_to_smt_type_tuple_ne_usort
    (U V : SmtType) (i : native_Nat) :
    __eo_to_smt_type_tuple U V ≠ SmtType.USort i := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_typeref`. -/
theorem eo_to_smt_type_tuple_ne_typeref
    (U V : SmtType) (s' : native_String) :
    __eo_to_smt_type_tuple U V ≠ SmtType.TypeRef s' := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_dtc_app`. -/
theorem eo_to_smt_type_tuple_ne_dtc_app
    (U V A B : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.DtcAppType A B := by
  rcases eo_to_smt_type_tuple_eq_none_or_datatype U V with h | ⟨dd, h⟩ <;>
    simp [h]

private theorem eo_to_smt_type_guarded_tuple_ne_bool
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Bool := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_bool U V]

private theorem eo_to_smt_type_guarded_tuple_ne_int
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Int := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_int U V]

private theorem eo_to_smt_type_guarded_tuple_ne_real
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Real := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_real U V]

private theorem eo_to_smt_type_guarded_tuple_ne_reglan
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.RegLan := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_reglan U V]

private theorem eo_to_smt_type_guarded_tuple_ne_bitvec
    (U V : SmtType) (w : native_Nat) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.BitVec w := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_bitvec U V w]

private theorem eo_to_smt_type_guarded_tuple_ne_char
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Char := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_char U V]

private theorem eo_to_smt_type_guarded_tuple_ne_seq
    (U V W : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Seq W := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_seq U V W]

private theorem eo_to_smt_type_guarded_tuple_ne_set
    (U V W : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Set W := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_set U V W]

private theorem eo_to_smt_type_guarded_tuple_ne_map
    (U V W X : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Map W X := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_map U V W X]

private theorem eo_to_smt_type_guarded_tuple_ne_fun
    (U V A B : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.FunType A B := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_fun U V A B]

private theorem eo_to_smt_type_guarded_tuple_ne_usort
    (U V : SmtType) (i : native_Nat) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.USort i := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_usort U V i]

private theorem eo_to_smt_type_guarded_tuple_ne_typeref
    (U V : SmtType) (s : native_String) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.TypeRef s := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_typeref U V s]

private theorem eo_to_smt_type_guarded_tuple_ne_dtc_app
    (U V A B : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.DtcAppType A B := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_dtc_app U V A B]

/-- Simplifies EO-to-SMT type translation for `fun_ne_bool`. -/
private theorem eo_to_smt_type_fun_ne_bool
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Bool := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_int`. -/
private theorem eo_to_smt_type_fun_ne_int
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Int := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_real`. -/
private theorem eo_to_smt_type_fun_ne_real
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Real := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_reglan`. -/
private theorem eo_to_smt_type_fun_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.RegLan := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_char`. -/
private theorem eo_to_smt_type_fun_ne_char
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Char := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_bitvec`. -/
private theorem eo_to_smt_type_fun_ne_bitvec
    (T U : Term) (w : native_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.BitVec w := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_seq`. -/
private theorem eo_to_smt_type_fun_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Seq V := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_set`. -/
private theorem eo_to_smt_type_fun_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Set V := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_map`. -/
private theorem eo_to_smt_type_fun_ne_map
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Map V W := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_dtc_app`. -/
private theorem eo_to_smt_type_fun_ne_dtc_app
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.DtcAppType V W := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_usort`. -/
private theorem eo_to_smt_type_fun_ne_usort
    (T U : Term) (i : native_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.USort i := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_typeref`. -/
private theorem eo_to_smt_type_fun_ne_typeref
    (T U : Term) (s : native_String) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.TypeRef s := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_bitvec
    (T U : Term) (w : native_Nat) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.BitVec w := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Seq V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Set V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_map
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Map V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_fun
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.FunType V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

private theorem eo_to_smt_type_dtc_app_ne_usort
    (T U : Term) (i : native_Nat) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.USort i := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_typeref
    (T U : Term) (s : native_String) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.TypeRef s := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `seq_inner`. -/
private theorem eo_to_smt_type_seq_inner
    (T : Term) {U : SmtType}
    (h : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) = SmtType.Seq U) :
    __eo_to_smt_type T = U := by
  cases hT : __eo_to_smt_type T <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hT] at h
  all_goals exact h

/-- Simplifies EO-to-SMT type translation for `set_inner`. -/
private theorem eo_to_smt_type_set_inner
    (T : Term) {U : SmtType}
    (h : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) = SmtType.Set U) :
    __eo_to_smt_type T = U := by
  cases hT : __eo_to_smt_type T <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hT] at h
  all_goals exact h

/-- Simplifies EO-to-SMT type translation for `array_inners`. -/
private theorem eo_to_smt_type_array_inners
    (T U : Term) {A B : SmtType}
    (h : __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U) = SmtType.Map A B) :
    __eo_to_smt_type T = A ∧ __eo_to_smt_type U = B := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hT, hU] at h
  all_goals exact h

/-- Simplifies EO-to-SMT type translation for `eq_bool`. -/
theorem eo_to_smt_type_eq_bool
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Bool) :
    T = Term.Bool := by
  cases T with
  | Bool =>
      rfl
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_bool y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_bool (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_int`. -/
theorem eo_to_smt_type_eq_int
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Int) :
    T = (Term.UOp UserOp.Int) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case Int =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_int y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_int (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_real`. -/
theorem eo_to_smt_type_eq_real
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Real) :
    T = (Term.UOp UserOp.Real) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case Real =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_real y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_real (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_reglan`. -/
theorem eo_to_smt_type_eq_reglan
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.RegLan) :
    T = (Term.UOp UserOp.RegLan) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case RegLan =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_reglan y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_reglan (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_char`. -/
theorem eo_to_smt_type_eq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Char) :
    T = (Term.UOp UserOp.Char) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case Char =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_char y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_char (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_bitvec`. -/
theorem eo_to_smt_type_eq_bitvec
    {T : Term} {w : native_Nat}
    (h : __eo_to_smt_type T = SmtType.BitVec w) :
    T = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_bitvec T U w h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hn : native_zleq 0 n = true
                  · simp [native_ite, hn] at h
                    cases h
                    have hnNonneg : 0 <= n := by
                      simpa [native_zleq, SmtEval.native_zleq] using hn
                    simp [native_nat_to_int, native_int_to_nat,
                      Smtm.native_nat_to_int, SmtEval.native_int_to_nat,
                      Int.toNat_of_nonneg hnNonneg]
                  · simp [native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_bitvec y x w h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_bitvec (__eo_to_smt_type y) (__eo_to_smt_type x) w h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_seq`. -/
theorem eo_to_smt_type_eq_seq
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Seq U) :
    ∃ V, T = Term.Apply (Term.UOp UserOp.Seq) V ∧ __eo_to_smt_type V = U := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_seq T U _ h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              exact ⟨x, rfl, eo_to_smt_type_seq_inner x h⟩
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_seq y x U h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_seq (__eo_to_smt_type y) (__eo_to_smt_type x) U h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_seq_char`. -/
theorem eo_to_smt_type_eq_seq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Seq SmtType.Char) :
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  rcases eo_to_smt_type_eq_seq h with ⟨V, rfl, hV⟩
  rw [eo_to_smt_type_eq_char hV]

/-- Simplifies EO-to-SMT type translation for `eq_set`. -/
theorem eo_to_smt_type_eq_set
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Set U) :
    ∃ V, T = Term.Apply (Term.UOp UserOp.Set) V ∧ __eo_to_smt_type V = U := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U' =>
      exact (eo_to_smt_type_dtc_app_ne_set T U' U h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              exact ⟨x, rfl, eo_to_smt_type_set_inner x h⟩
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_set y x U h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_set (__eo_to_smt_type y) (__eo_to_smt_type x) U h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_map`. -/
theorem eo_to_smt_type_eq_map
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.Map A B) :
    ∃ U V, T = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_map T U A B h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_map y x A B h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_map (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  exact ⟨y, x, rfl, (eo_to_smt_type_array_inners y x h).1,
                    (eo_to_smt_type_array_inners y x h).2⟩
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_fun`. -/
theorem eo_to_smt_type_eq_fun
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.FunType A B) :
    ∃ U V, T = Term.Apply (Term.Apply Term.FunType U) V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_fun T U A B h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              have hParts : __eo_to_smt_type y = A ∧ __eo_to_smt_type x = B := by
                by_cases hy : __eo_to_smt_type y = SmtType.None
                · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                    hy] at h
                · by_cases hx : __eo_to_smt_type x = SmtType.None
                  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                      hy, hx] at h
                  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite,
                      native_Teq, hy, hx] at h
                    exact h
              exact ⟨y, x, rfl, hParts.1, hParts.2⟩
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_fun (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

theorem eo_to_smt_type_eq_dtc_app
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.DtcAppType A B) :
    ∃ U V, T = Term.DtcAppType U V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType U V =>
      have hParts : __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
        cases hU : __eo_to_smt_type U <;> cases hV : __eo_to_smt_type V <;>
          simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
            hU, hV] at h
        all_goals exact h
      exact ⟨U, V, rfl, hParts.1, hParts.2⟩
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x <;> try simp [__eo_to_smt_type] at h
              case Numeral n =>
                  by_cases hn : native_zleq 0 n = true
                  · simp [hn] at h
                  · simp [hn] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_dtc_app y x A B h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_dtc_app (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_usort`. -/
theorem eo_to_smt_type_eq_usort
    {T : Term} {i : native_Nat}
    (h : __eo_to_smt_type T = SmtType.USort i) :
    T = Term.USort i := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DatatypeType s d =>
      by_cases hReserved : __eo_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DatatypeTypeRef s =>
      by_cases hReserved : __eo_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_usort T U i h).elim
  | USort j =>
      simp [__eo_to_smt_type] at h
      cases h
      rfl
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_usort y x i h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_usort (__eo_to_smt_type y) (__eo_to_smt_type x) i h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_typeref`. -/
theorem eo_to_smt_type_eq_typeref
    {T : Term} {s : native_String}
    (h : __eo_to_smt_type T = SmtType.TypeRef s) :
    T = Term.DatatypeTypeRef s := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DatatypeType s' d =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DatatypeTypeRef s' =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
        cases h
        rfl
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_typeref T U s h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_typeref y x s h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_typeref (__eo_to_smt_type y) (__eo_to_smt_type x) s h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

theorem eo_reserved_datatype_name_tuple :
    __eo_reserved_datatype_name (native_string_lit "@Tuple") = true := by
  native_decide

theorem eo_unreserved_datatype_name_ne_tuple
    {s : native_String}
    (hReserved : __eo_reserved_datatype_name s = false) :
    s ≠ (native_string_lit "@Tuple") := by
  intro h
  subst s
  rw [eo_reserved_datatype_name_tuple] at hReserved
  contradiction

/--
Inverts translated user datatype types.

The `@Tuple` datatype is generated by the EO tuple encoding, so excluding it
keeps user datatypes disjoint from tuple types.
-/
theorem eo_to_smt_type_eq_datatype_non_tuple
    {T : Term} {s : native_String} {d : SmtDatatypeDecl}
    (hName : s ≠ (native_string_lit "@Tuple"))
    (h : __eo_to_smt_type T = SmtType.Datatype s d) :
    ∃ d0, T = Term.DatatypeType s d0 ∧ __eo_to_smt_datatype_decl d0 = d := by
  cases T with
  | DatatypeType s' d' =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
        rcases h with ⟨hs, hd⟩
        subst s'
        exact ⟨d', rfl, hd⟩
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
      case UnitTuple =>
        rcases h with ⟨hs, _⟩
        exact False.elim (hName hs.symm)
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Array =>
                cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                  simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
              case Tuple =>
                have hRaw :
                    __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) =
                      SmtType.Datatype s d := by
                  cases hwf :
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                    simp [hwf] at h ⊢
                  exact h
                rcases eo_to_smt_type_tuple_eq_none_or_datatype
                    (__eo_to_smt_type y) (__eo_to_smt_type x) with hNone | ⟨dd, hTuple⟩
                · rw [hRaw] at hNone
                  simp at hNone
                · rw [hRaw] at hTuple
                  have hs : s = native_string_lit "@Tuple" := by
                    injection hTuple
                  exact False.elim (hName hs)
          | FunType =>
              cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ => simp [__eo_to_smt_type] at h
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
            cases x with
            | Numeral n =>
                cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
            | _ =>
                simp [__eo_to_smt_type] at h
      | _ => simp [__eo_to_smt_type] at h
  | DatatypeTypeRef s' =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, ha, hb] at h
  | _ =>
      simp [__eo_to_smt_type] at h

private theorem eo_to_smt_type_tuple_eq_datatype_inv
    {A B : SmtType} {dd : SmtDatatypeDecl}
    (h : __eo_to_smt_type_tuple A B =
      SmtType.Datatype (native_string_lit "@Tuple") dd) :
    ∃ c : SmtDatatypeCons,
      B = SmtType.Datatype (native_string_lit "@Tuple")
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) ∧
      dd = __eo_to_smt_tuple_decl
          (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null) := by
  cases B <;> try simp [__eo_to_smt_type_tuple] at h
  case Datatype s decl =>
    cases decl with
    | nil => simp at h
    | cons s2 body rest =>
      cases body with
      | null => simp at h
      | sum c tail =>
        cases tail with
        | sum c2 tail2 => simp at h
        | null =>
          cases rest with
          | cons s3 body3 rest3 => simp at h
          | nil =>
            by_cases hs : s = native_string_lit "@Tuple"
            · by_cases hs2 : s2 = native_string_lit "@Tuple"
              · by_cases hA : __smtx_type_wf_component A = true
                · subst s
                  subst s2
                  simp [hA] at h
                  subst dd
                  exact ⟨c, rfl, rfl⟩
                · simp [hs, hs2, hA] at h
              · simp [hs, hs2] at h
            · simp [hs] at h

/-- Inverts translated EO tuple types. -/
theorem eo_to_smt_type_eq_tuple_datatype
    {T : Term} {d : SmtDatatypeDecl}
    (h : __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple") d) :
    (T = Term.UOp UserOp.UnitTuple ∧
      d = __eo_to_smt_tuple_decl
        (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) ∨
    (∃ y x c,
      T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x ∧
      __eo_to_smt_type x = SmtType.Datatype (native_string_lit "@Tuple")
        (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) ∧
      d = __eo_to_smt_tuple_decl
        (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
          SmtDatatype.null)) := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
      case UnitTuple =>
        cases h
        exact Or.inl ⟨rfl, rfl⟩
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Array =>
                cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                  simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
              case Tuple =>
                have hRaw :
                    __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) =
                      SmtType.Datatype (native_string_lit "@Tuple") d := by
                  cases hWf :
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                    simp [hWf] at h ⊢
                  exact h
                rcases eo_to_smt_type_tuple_eq_datatype_inv hRaw with
                  ⟨c, hx, hd⟩
                exact Or.inr ⟨y, x, c, rfl, hx, hd⟩
          | FunType =>
              cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard,
                  native_ite, native_Teq, hy, hx] at h
          | _ => simp [__eo_to_smt_type] at h
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
            cases x with
            | Numeral n =>
                cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
            | _ =>
                simp [__eo_to_smt_type] at h
      | FunType =>
          simp [__eo_to_smt_type] at h
      | _ => simp [__eo_to_smt_type] at h
  | DatatypeType s d0 =>
      by_cases hr : __eo_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, native_ite, hr] at h
      rcases h with ⟨hs, _⟩
      subst s
      rw [eo_reserved_datatype_name_tuple] at hr
      contradiction
  | DatatypeTypeRef s =>
      by_cases hr : __eo_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, native_ite, hr] at h
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, ha, hb] at h
  | _ => simp [__eo_to_smt_type] at h



/- BEGIN obsolete body-substitution and two-sided-WF development.
The declaration-based model resolves datatype references through a shared
declaration environment. Declaration-aware injectivity and component lemmas
follow this block.
/-! ## Reserved-name substitution no-op (used by the tuple cases below)
Substituting a *reserved* datatype name (e.g. the synthetic `"@Tuple"`) is a no-op on any
translated type, because translation never emits a `TypeRef` bearing a reserved name at a
substitution-reachable position. This discharges the "substitution is a no-op on tuple field
positions" obligations in the injectivity/well-formedness inversions below.

The block runs with the file's `native_ite`/`native_streq`/`native_and` local-simp lemmas
disabled so the `native_ite`-based no-op proofs stay in their explicit `rw` form. -/
section ReservedNoop
attribute [-simp] native_ite native_streq native_and

/- `noResRefTy T`: no `TypeRef s` with `s` a *reserved* datatype name occurs anywhere in `T`
(recursing unconditionally through datatype bodies AND composite type components). Purely syntactic.
Stronger than the substitution-reachability needed for the no-op, but that extra strength is what
lets tuple-body facts be read directly off `noResRefTy (tr tuple)`. -/
mutual
def noResRefTy : SmtType → Bool
  | SmtType.Datatype _ d => noResRefDt d
  | SmtType.TypeRef s => native_not (__eo_to_smt_reserved_datatype_name s)
  | SmtType.Seq a => noResRefTy a
  | SmtType.Set a => noResRefTy a
  | SmtType.Map a b => native_and (noResRefTy a) (noResRefTy b)
  | SmtType.FunType a b => native_and (noResRefTy a) (noResRefTy b)
  | SmtType.DtcAppType a b => native_and (noResRefTy a) (noResRefTy b)
  | _ => true
def noResRefDt : SmtDatatype → Bool
  | SmtDatatype.sum c d => native_and (noResRefDtc c) (noResRefDt d)
  | SmtDatatype.null => true
def noResRefDtc : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons T c => native_and (noResRefTy T) (noResRefDtc c)
  | SmtDatatypeCons.unit => true
end

/- Substituting a reserved name is a no-op on any `noResRef` structure. -/
mutual
theorem subst_noResRef_ty (r : native_String) (hRes : __eo_to_smt_reserved_datatype_name r = true) :
    (T : SmtType) → (X : SmtDatatype) → noResRefTy T = true → __smtx_type_substitute r X T = T
  | SmtType.Datatype s d, X, h => by
      simp only [noResRefTy] at h
      simp only [__smtx_type_substitute]
      by_cases hrs : native_streq r s = true
      · rw [native_ite, if_pos hrs]
      · rw [native_ite, if_neg (by simp [hrs])]
        rw [subst_noResRef_dt r hRes d (__smtx_dt_lift s d X) h]
  | SmtType.TypeRef s, X, h => by
      simp only [noResRefTy, native_not, Bool.not_eq_true'] at h
      have hrs : native_streq r s = false := by
        simp only [native_streq, decide_eq_false_iff_not]
        intro he; rw [he] at hRes; rw [h] at hRes; exact absurd hRes (by decide)
      simp only [__smtx_type_substitute]
      rw [native_ite, if_neg (by simp [hrs])]
  | SmtType.Seq a, X, h => by simp [__smtx_type_substitute]
  | SmtType.Set a, X, h => by simp [__smtx_type_substitute]
  | SmtType.Map a b, X, h => by simp [__smtx_type_substitute]
  | SmtType.FunType a b, X, h => by simp [__smtx_type_substitute]
  | SmtType.DtcAppType a b, X, h => by simp [__smtx_type_substitute]
  | SmtType.None, X, h => by simp [__smtx_type_substitute]
  | SmtType.RegLan, X, h => by simp [__smtx_type_substitute]
  | SmtType.Bool, X, h => by simp [__smtx_type_substitute]
  | SmtType.Int, X, h => by simp [__smtx_type_substitute]
  | SmtType.Real, X, h => by simp [__smtx_type_substitute]
  | SmtType.BitVec n, X, h => by simp [__smtx_type_substitute]
  | SmtType.Char, X, h => by simp [__smtx_type_substitute]
  | SmtType.USort n, X, h => by simp [__smtx_type_substitute]

theorem subst_noResRef_dt (r : native_String) (hRes : __eo_to_smt_reserved_datatype_name r = true) :
    (W : SmtDatatype) → (X : SmtDatatype) → noResRefDt W = true → __smtx_dt_substitute r X W = W
  | SmtDatatype.null, X, h => by simp [__smtx_dt_substitute]
  | SmtDatatype.sum c d, X, h => by
      simp only [noResRefDt, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dt_substitute]
      rw [subst_noResRef_dtc r hRes c X h.1, subst_noResRef_dt r hRes d X h.2]

theorem subst_noResRef_dtc (r : native_String) (hRes : __eo_to_smt_reserved_datatype_name r = true) :
    (c : SmtDatatypeCons) → (X : SmtDatatype) → noResRefDtc c = true → __smtx_dtc_substitute r X c = c
  | SmtDatatypeCons.unit, X, h => by simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, X, h => by
      simp only [noResRefDtc, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dtc_substitute]
      rw [subst_noResRef_ty r hRes T X h.1, subst_noResRef_dtc r hRes c X h.2]
end

/- Helper: `__smtx_typeof_guard A B` is either `None` or `B`. -/
theorem eoTy_guard_cases_res (A B : SmtType) :
    __smtx_typeof_guard A B = SmtType.None ∨ __smtx_typeof_guard A B = B := by
  simp only [__smtx_typeof_guard]
  by_cases h : native_Teq A SmtType.None = true
  · left; simp [native_ite, h]
  · right; simp [native_ite, h]

/- The tuple encoding preserves `noResRef`. -/
theorem noResRef_tuple (A B : SmtType)
    (hA : noResRefTy A = true) (hB : noResRefTy B = true) :
    noResRefTy (__eo_to_smt_type_tuple A B) = true := by
  cases B with
  | Datatype s body =>
      cases body with
      | sum c tail =>
          cases tail with
          | null =>
              simp only [__eo_to_smt_type_tuple]
              by_cases hcond :
                  native_and (native_streq s (native_string_lit "@Tuple"))
                    (__smtx_type_wf_component A) = true
              · rw [native_ite, if_pos hcond]
                simp only [noResRefTy, noResRefDt, native_and, Bool.and_eq_true, noResRefDtc] at hB ⊢
                exact ⟨⟨hA, hB.1⟩, hB.2⟩
              · rw [native_ite, if_neg (by simp [hcond])]; simp [noResRefTy]
          | sum _ _ => simp [__eo_to_smt_type_tuple, noResRefTy]
      | null => simp [__eo_to_smt_type_tuple, noResRefTy]
  | _ => simp [__eo_to_smt_type_tuple, noResRefTy]

/- Translation of any term satisfies `noResRef`. -/
mutual
theorem noResRef_translate_ty : (T : Term) → noResRefTy (__eo_to_smt_type T) = true
  | Term.Bool => by simp [__eo_to_smt_type, noResRefTy]
  | Term.USort i => by simp [__eo_to_smt_type, noResRefTy]
  | Term.DatatypeType s d => by
      by_cases hs : __eo_to_smt_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hs, noResRefTy]
      · have hsF : __eo_to_smt_reserved_datatype_name s = false := by
          cases h : __eo_to_smt_reserved_datatype_name s <;> simp [h] at hs ⊢
        simp only [__eo_to_smt_type, native_ite, hsF, Bool.false_eq_true, if_false, noResRefTy]
        exact noResRef_translate_dt d
  | Term.DatatypeTypeRef s => by
      by_cases hs : __eo_to_smt_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hs, noResRefTy]
      · have hsF : __eo_to_smt_reserved_datatype_name s = false := by
          cases h : __eo_to_smt_reserved_datatype_name s <;> simp [h] at hs ⊢
        simp [__eo_to_smt_type, native_ite, noResRefTy, native_not, hsF]
  | Term.DtcAppType T U => by
      simp only [__eo_to_smt_type]
      rcases eoTy_guard_cases_res (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U) (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U))) with h | h
        <;> rw [h]
      · simp [noResRefTy]
      · rcases eoTy_guard_cases_res (__eo_to_smt_type U) (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)) with h2 | h2
          <;> rw [h2]
        · simp [noResRefTy]
        · simp only [noResRefTy, native_and, Bool.and_eq_true]
          exact ⟨noResRef_translate_ty T, noResRef_translate_ty U⟩
  | Term.UOp op => by
      cases op with
      | Int => simp [__eo_to_smt_type, noResRefTy]
      | Real => simp [__eo_to_smt_type, noResRefTy]
      | Char => simp [__eo_to_smt_type, noResRefTy]
      | UnitTuple => simp [__eo_to_smt_type, noResRefTy, noResRefDt, noResRefDtc, native_and]
      | _ => simp [__eo_to_smt_type, noResRefTy]
  | Term.Apply (Term.Apply Term.FunType T1) T2 => by
      simp only [__eo_to_smt_type]
      rcases eoTy_guard_cases_res (__eo_to_smt_type T1)
          (__smtx_typeof_guard (__eo_to_smt_type T2) (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2))) with h | h
        <;> rw [h]
      · simp [noResRefTy]
      · rcases eoTy_guard_cases_res (__eo_to_smt_type T2) (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) with h2 | h2
          <;> rw [h2]
        · simp [noResRefTy]
        · simp only [noResRefTy, native_and, Bool.and_eq_true]
          exact ⟨noResRef_translate_ty T1, noResRef_translate_ty T2⟩
  | Term.Apply f x => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  simp only [__eo_to_smt_type]
                  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn, noResRefTy]
              | _ => simp [__eo_to_smt_type, noResRefTy]
          | Seq =>
              simp only [__eo_to_smt_type]
              rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.Seq (__eo_to_smt_type x)) with h | h
                <;> rw [h]
              · simp [noResRefTy]
              · simp only [noResRefTy]; exact noResRef_translate_ty x
          | Set =>
              simp only [__eo_to_smt_type]
              rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.Set (__eo_to_smt_type x)) with h | h
                <;> rw [h]
              · simp [noResRefTy]
              · simp only [noResRefTy]; exact noResRef_translate_ty x
          | _ => simp [__eo_to_smt_type, noResRefTy]
      | Apply g y =>
          cases g with
          | FunType =>
              simp only [__eo_to_smt_type]
              rcases eoTy_guard_cases_res (__eo_to_smt_type y)
                  (__smtx_typeof_guard (__eo_to_smt_type x) (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))) with h | h
                <;> rw [h]
              · simp [noResRefTy]
              · rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) with h2 | h2
                  <;> rw [h2]
                · simp [noResRefTy]
                · simp only [noResRefTy, native_and, Bool.and_eq_true]
                  exact ⟨noResRef_translate_ty y, noResRef_translate_ty x⟩
          | UOp op =>
              cases op with
              | Array =>
                  simp only [__eo_to_smt_type]
                  rcases eoTy_guard_cases_res (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x) (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) with h | h
                    <;> rw [h]
                  · simp [noResRefTy]
                  · rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) with h2 | h2
                      <;> rw [h2]
                    · simp [noResRefTy]
                    · simp only [noResRefTy, native_and, Bool.and_eq_true]
                      exact ⟨noResRef_translate_ty y, noResRef_translate_ty x⟩
              | Tuple =>
                  simp only [__eo_to_smt_type]
                  by_cases hWf :
                      __smtx_type_wf (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) = true
                  · rw [native_ite, if_pos hWf]
                    exact noResRef_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
                      (noResRef_translate_ty y) (noResRef_translate_ty x)
                  · rw [native_ite, if_neg (by simp [hWf])]; simp [noResRefTy]
              | _ => simp [__eo_to_smt_type, noResRefTy]
          | _ => simp [__eo_to_smt_type, noResRefTy]
      | _ => simp [__eo_to_smt_type, noResRefTy]
  | Term.__eo_List => by simp [__eo_to_smt_type, noResRefTy]
  | Term.__eo_List_nil => by simp [__eo_to_smt_type, noResRefTy]
  | Term.__eo_List_cons => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Boolean b => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Numeral n => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Rational q => by simp [__eo_to_smt_type, noResRefTy]
  | Term.String s => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Binary w n => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Type => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Stuck => by simp [__eo_to_smt_type, noResRefTy]
  | Term.FunType => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Var name T => by simp [__eo_to_smt_type, noResRefTy]
  | Term.DtCons s d i => by simp [__eo_to_smt_type, noResRefTy]
  | Term.DtSel s d i j => by simp [__eo_to_smt_type, noResRefTy]
  | Term.UConst i T => by simp [__eo_to_smt_type, noResRefTy]
  | Term.UOp1 op x => by cases op <;> simp [__eo_to_smt_type, noResRefTy]
  | Term.UOp2 op x y => by cases op <;> simp [__eo_to_smt_type, noResRefTy]
  | Term.UOp3 op x y z => by cases op <;> simp [__eo_to_smt_type, noResRefTy]

theorem noResRef_translate_dt : (d : Datatype) → noResRefDt (__eo_to_smt_datatype d) = true
  | Datatype.null => by simp [__eo_to_smt_datatype, noResRefDt]
  | Datatype.sum c d => by
      simp only [__eo_to_smt_datatype, noResRefDt, native_and, Bool.and_eq_true]
      exact ⟨noResRef_translate_dtc c, noResRef_translate_dt d⟩

theorem noResRef_translate_dtc : (c : DatatypeCons) → noResRefDtc (__eo_to_smt_datatype_cons c) = true
  | DatatypeCons.unit => by simp [__eo_to_smt_datatype_cons, noResRefDtc]
  | DatatypeCons.cons T c => by
      simp only [__eo_to_smt_datatype_cons, noResRefDtc, native_and, Bool.and_eq_true]
      exact ⟨noResRef_translate_ty T, noResRef_translate_dtc c⟩
end

/- Substituting a reserved name is a no-op on translated content. -/
theorem subst_reserved_noop_ty (r : native_String) (hRes : __eo_to_smt_reserved_datatype_name r = true)
    (T : Term) (X : SmtDatatype) :
    __smtx_type_substitute r X (__eo_to_smt_type T) = __eo_to_smt_type T :=
  subst_noResRef_ty r hRes (__eo_to_smt_type T) X (noResRef_translate_ty T)

theorem subst_reserved_noop_dt (r : native_String) (hRes : __eo_to_smt_reserved_datatype_name r = true)
    (d : Datatype) (X : SmtDatatype) :
    __smtx_dt_substitute r X (__eo_to_smt_datatype d) = __eo_to_smt_datatype d :=
  subst_noResRef_dt r hRes (__eo_to_smt_datatype d) X (noResRef_translate_dt d)

end ReservedNoop

section TupleDiagWf
attribute [-simp] native_ite native_streq native_and
/-- Component well-formedness of a (non-`None`) tuple type: from the diagonal well-formedness
of `__eo_to_smt_type_tuple (tr y) (tr x)`, both `tr y` and `tr x` are themselves diagonally
well-formed. Uses the reserved-name substitution no-op to collapse the tuple's self-substitution. -/
theorem tuple_diag_wf_components (y x : Term)
    (hWf : __smtx_type_wf_rec (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) = true)
    (hNN : __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) ≠ SmtType.None) :
    __smtx_type_wf_rec (__eo_to_smt_type y) (__eo_to_smt_type y) = true ∧
    __smtx_type_wf_rec (__eo_to_smt_type x) (__eo_to_smt_type x) = true := by
  have hResTuple : __eo_to_smt_reserved_datatype_name (native_string_lit "@Tuple") = true := by
    native_decide
  cases hxShape : __eo_to_smt_type x with
  | Datatype sx bx =>
    cases bx with
    | sum cx tx =>
      cases tx with
      | null =>
        by_cases hsx : native_streq sx (native_string_lit "@Tuple") = true
        · by_cases hyc : __smtx_type_wf_component (__eo_to_smt_type y) = true
          · have hsxeq : sx = native_string_lit "@Tuple" := by simpa [native_streq] using hsx
            subst hsxeq
            have hEq :
                __eo_to_smt_type_tuple (__eo_to_smt_type y)
                    (SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum cx SmtDatatype.null)) =
                  SmtType.Datatype (native_string_lit "@Tuple")
                    (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null) := by
              simp [__eo_to_smt_type_tuple, native_ite, native_and, hsx, hyc]
            rw [hxShape, hEq] at hWf
            have hcxNoRes : noResRefDtc cx = true := by
              have hnr := noResRef_translate_ty x
              rw [hxShape] at hnr
              simpa [noResRefTy, noResRefDt, noResRefDtc, native_and] using hnr
            have hbodyNoRes :
                noResRefDt (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx)
                    SmtDatatype.null) = true := by
              simp [noResRefDt, noResRefDtc, native_and, noResRef_translate_ty y, hcxNoRes]
            have hAwf :
                __smtx_dt_wf_rec
                    (__smtx_dt_substitute (native_string_lit "@Tuple")
                      (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null)
                      (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null))
                    (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null) = true := by
              simpa [__smtx_type_wf_rec] using hWf
            rw [subst_noResRef_dt (native_string_lit "@Tuple") hResTuple _ _ hbodyNoRes] at hAwf
            have hConsWF :
                __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type y) cx)
                    (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) = true := by
              simp only [__smtx_dt_wf_rec, native_ite] at hAwf
              by_cases hc :
                  __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type y) cx)
                    (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) = true
              · exact hc
              · rw [if_neg (by simpa using hc)] at hAwf; simp at hAwf
            have hyNotRef : ∀ s, __eo_to_smt_type y ≠ SmtType.TypeRef s := by
              intro s he
              rw [he] at hConsWF
              simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] at hConsWF
            have hyWF : __smtx_type_wf_rec (__eo_to_smt_type y) (__eo_to_smt_type y) = true :=
              smtx_type_field_wf_rec_of_cons_wf (refs := native_reflist_nil) hyNotRef hConsWF
            have hcxWF : __smtx_dt_cons_wf_rec cx cx = true :=
              smtx_dt_cons_wf_rec_tail_of_true hConsWF
            have hxWF :
                __smtx_type_wf_rec
                    (SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum cx SmtDatatype.null))
                    (SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum cx SmtDatatype.null)) = true := by
              have h2 :
                  __smtx_dt_wf_rec (SmtDatatype.sum cx SmtDatatype.null)
                    (SmtDatatype.sum cx SmtDatatype.null) = true := by
                simp only [__smtx_dt_wf_rec, hcxWF]; decide
              simp only [__smtx_type_wf_rec]
              rw [subst_noResRef_dt (native_string_lit "@Tuple") hResTuple
                (SmtDatatype.sum cx SmtDatatype.null) (SmtDatatype.sum cx SmtDatatype.null)
                (by simp [noResRefDt, hcxNoRes, native_and])]
              exact h2
            exact ⟨hyWF, hxWF⟩
          · exfalso; apply hNN
            have hyc' : __smtx_type_wf_component (__eo_to_smt_type y) = false := by
              cases hh : __smtx_type_wf_component (__eo_to_smt_type y) <;> simp_all
            simp [__eo_to_smt_type_tuple, hxShape, native_ite, native_and, hyc']
        · exfalso; apply hNN
          have hsxF : native_streq sx (native_string_lit "@Tuple") = false := by
            cases hh : native_streq sx (native_string_lit "@Tuple")
            · rfl
            · exact absurd hh hsx
          simp [__eo_to_smt_type_tuple, hxShape, native_ite, native_and, hsxF]
      | sum _ _ => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
    | null => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Bool => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Int => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Real => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | RegLan => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | BitVec n => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Map a b => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Set a => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Seq a => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Char => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | TypeRef s3 => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | USort i => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | FunType a b => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | DtcAppType a b => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | None => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
end TupleDiagWf



/-! ## Alignment + `noNone`: the sound basis for translation-injectivity.
`__smtx_type_wf_rec`'s catch-all `wf_rec (non-datatype) (Datatype …) = true` makes the raw
full/unfold well-formedness too weak to certify injectivity (an arbitrary full side can hide a
`None` under a datatype). `alignTy DF D` records that the full side genuinely unfolds `D` (has a
`Datatype` wherever `D` does); substitution images are aligned, and `dt_wf_rec DF D ∧ alignDt DF D`
then rules out `None` everywhere (`noNone…`). Injectivity is proved directly on `noNone`. -/
section AlignNoNone
attribute [-simp] native_ite native_streq native_and
mutual
@[expose] def alignTy : SmtType → SmtType → Bool
  | SmtType.Datatype _ dF, SmtType.Datatype _ dU => alignDt dF dU
  | _, SmtType.Datatype _ _ => false
  | _, _ => true
@[expose] def alignDt : SmtDatatype → SmtDatatype → Bool
  | SmtDatatype.sum cF dF, SmtDatatype.sum cU dU => native_and (alignDtc cF cU) (alignDt dF dU)
  | SmtDatatype.null, SmtDatatype.null => true
  | _, _ => false
@[expose] def alignDtc : SmtDatatypeCons → SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU =>
      native_and (alignTy TF TU) (alignDtc cF cU)
  | SmtDatatypeCons.unit, SmtDatatypeCons.unit => true
  | _, _ => false
end

/- Any substitution image is aligned with its argument: `__smtx_*_substitute` maps `Datatype`→
`Datatype` (recursing into the body), `TypeRef`→`Datatype`/`TypeRef`, and leaves everything else
untouched — so it never turns a `Datatype`-position of the argument into a non-`Datatype`. -/
mutual
theorem alignTy_subst (s : native_String) (d0 : SmtDatatype) :
    (U : SmtType) → alignTy (__smtx_type_substitute s d0 U) U = true
  | SmtType.Datatype s2 d2 => by
      simp only [__smtx_type_substitute]
      by_cases hst : native_streq s s2 = true
      · simp only [native_ite, if_pos hst, alignTy]; exact alignDt_refl d2
      · simp only [native_ite, if_neg hst, alignTy]
        exact alignDt_subst s (__smtx_dt_lift s2 d2 d0) d2
  | SmtType.TypeRef s2 => by
      simp only [__smtx_type_substitute]
      by_cases hst : native_streq s s2 = true
      · simp [native_ite, if_pos hst, alignTy]
      · simp [native_ite, if_neg hst, alignTy]
  | SmtType.Seq a => by simp [__smtx_type_substitute, alignTy]
  | SmtType.Set a => by simp [__smtx_type_substitute, alignTy]
  | SmtType.Map a b => by simp [__smtx_type_substitute, alignTy]
  | SmtType.FunType a b => by simp [__smtx_type_substitute, alignTy]
  | SmtType.DtcAppType a b => by simp [__smtx_type_substitute, alignTy]
  | SmtType.None => by simp [__smtx_type_substitute, alignTy]
  | SmtType.RegLan => by simp [__smtx_type_substitute, alignTy]
  | SmtType.Bool => by simp [__smtx_type_substitute, alignTy]
  | SmtType.Int => by simp [__smtx_type_substitute, alignTy]
  | SmtType.Real => by simp [__smtx_type_substitute, alignTy]
  | SmtType.BitVec n => by simp [__smtx_type_substitute, alignTy]
  | SmtType.Char => by simp [__smtx_type_substitute, alignTy]
  | SmtType.USort i => by simp [__smtx_type_substitute, alignTy]

theorem alignDt_subst (s : native_String) (d0 : SmtDatatype) :
    (D : SmtDatatype) → alignDt (__smtx_dt_substitute s d0 D) D = true
  | SmtDatatype.null => by simp [__smtx_dt_substitute, alignDt]
  | SmtDatatype.sum c d => by
      simp only [__smtx_dt_substitute, alignDt, native_and, Bool.and_eq_true]
      exact ⟨alignDtc_subst s d0 c, alignDt_subst s d0 d⟩

theorem alignDtc_subst (s : native_String) (d0 : SmtDatatype) :
    (C : SmtDatatypeCons) → alignDtc (__smtx_dtc_substitute s d0 C) C = true
  | SmtDatatypeCons.unit => by simp [__smtx_dtc_substitute, alignDtc]
  | SmtDatatypeCons.cons U c => by
      simp only [__smtx_dtc_substitute, alignDtc, native_and, Bool.and_eq_true]
      exact ⟨alignTy_subst s d0 U, alignDtc_subst s d0 c⟩

-- reflexivity: everything aligns itself
theorem alignTy_refl : (A : SmtType) → alignTy A A = true
  | SmtType.Datatype s d => by simp only [alignTy]; exact alignDt_refl d
  | SmtType.Seq a => by simp [alignTy]
  | SmtType.Set a => by simp [alignTy]
  | SmtType.Map a b => by simp [alignTy]
  | SmtType.FunType a b => by simp [alignTy]
  | SmtType.DtcAppType a b => by simp [alignTy]
  | SmtType.None => by simp [alignTy]
  | SmtType.TypeRef s => by simp [alignTy]
  | SmtType.RegLan => by simp [alignTy]
  | SmtType.Bool => by simp [alignTy]
  | SmtType.Int => by simp [alignTy]
  | SmtType.Real => by simp [alignTy]
  | SmtType.BitVec n => by simp [alignTy]
  | SmtType.Char => by simp [alignTy]
  | SmtType.USort i => by simp [alignTy]

theorem alignDt_refl : (D : SmtDatatype) → alignDt D D = true
  | SmtDatatype.null => by simp [alignDt]
  | SmtDatatype.sum c d => by
      simp only [alignDt, native_and, Bool.and_eq_true]; exact ⟨alignDtc_refl c, alignDt_refl d⟩

theorem alignDtc_refl : (C : SmtDatatypeCons) → alignDtc C C = true
  | SmtDatatypeCons.unit => by simp [alignDtc]
  | SmtDatatypeCons.cons U c => by
      simp only [alignDtc, native_and, Bool.and_eq_true]; exact ⟨alignTy_refl U, alignDtc_refl c⟩
end

/- Transitivity — needed to keep the field-body alignment as the substituting datatype is re-lifted
inside `__smtx_type_wf_rec`'s datatype clause. -/
mutual
theorem alignTy_trans :
    (A B C : SmtType) → alignTy A B = true → alignTy B C = true → alignTy A C = true
  | A, B, SmtType.Datatype sc dc, hAB, hBC => by
      cases B with
      | Datatype sb db =>
          cases A with
          | Datatype sa da =>
              simp only [alignTy] at hAB hBC ⊢
              exact alignDt_trans da db dc hAB hBC
          | _ => simp [alignTy] at hAB
      | _ => simp [alignTy] at hBC
  | A, B, SmtType.Seq _, _, _ => by simp [alignTy]
  | A, B, SmtType.Set _, _, _ => by simp [alignTy]
  | A, B, SmtType.Map _ _, _, _ => by simp [alignTy]
  | A, B, SmtType.FunType _ _, _, _ => by simp [alignTy]
  | A, B, SmtType.DtcAppType _ _, _, _ => by simp [alignTy]
  | A, B, SmtType.None, _, _ => by simp [alignTy]
  | A, B, SmtType.TypeRef _, _, _ => by simp [alignTy]
  | A, B, SmtType.RegLan, _, _ => by simp [alignTy]
  | A, B, SmtType.Bool, _, _ => by simp [alignTy]
  | A, B, SmtType.Int, _, _ => by simp [alignTy]
  | A, B, SmtType.Real, _, _ => by simp [alignTy]
  | A, B, SmtType.BitVec _, _, _ => by simp [alignTy]
  | A, B, SmtType.Char, _, _ => by simp [alignTy]
  | A, B, SmtType.USort _, _, _ => by simp [alignTy]

theorem alignDt_trans :
    (A B C : SmtDatatype) → alignDt A B = true → alignDt B C = true → alignDt A C = true
  | SmtDatatype.null, SmtDatatype.null, SmtDatatype.null, _, _ => by simp [alignDt]
  | SmtDatatype.sum ca da, SmtDatatype.sum cb db, SmtDatatype.sum cc dc, hAB, hBC => by
      simp only [alignDt, native_and, Bool.and_eq_true] at hAB hBC ⊢
      exact ⟨alignDtc_trans ca cb cc hAB.1 hBC.1, alignDt_trans da db dc hAB.2 hBC.2⟩
  | SmtDatatype.null, SmtDatatype.sum _ _, _, hAB, _ => by simp [alignDt] at hAB
  | SmtDatatype.sum _ _, SmtDatatype.null, _, hAB, _ => by simp [alignDt] at hAB
  | SmtDatatype.null, SmtDatatype.null, SmtDatatype.sum _ _, _, hBC => by simp [alignDt] at hBC
  | SmtDatatype.sum _ _, SmtDatatype.sum _ _, SmtDatatype.null, _, hBC => by simp [alignDt] at hBC

theorem alignDtc_trans :
    (A B C : SmtDatatypeCons) → alignDtc A B = true → alignDtc B C = true → alignDtc A C = true
  | SmtDatatypeCons.unit, SmtDatatypeCons.unit, SmtDatatypeCons.unit, _, _ => by simp [alignDtc]
  | SmtDatatypeCons.cons Ta ca, SmtDatatypeCons.cons Tb cb, SmtDatatypeCons.cons Tc cc, hAB, hBC => by
      simp only [alignDtc, native_and, Bool.and_eq_true] at hAB hBC ⊢
      exact ⟨alignTy_trans Ta Tb Tc hAB.1 hBC.1, alignDtc_trans ca cb cc hAB.2 hBC.2⟩
  | SmtDatatypeCons.unit, SmtDatatypeCons.cons _ _, _, hAB, _ => by simp [alignDtc] at hAB
  | SmtDatatypeCons.cons _ _, SmtDatatypeCons.unit, _, hAB, _ => by simp [alignDtc] at hAB
  | SmtDatatypeCons.unit, SmtDatatypeCons.unit, SmtDatatypeCons.cons _ _, _, hBC => by simp [alignDtc] at hBC
  | SmtDatatypeCons.cons _ _, SmtDatatypeCons.cons _ _, SmtDatatypeCons.unit, _, hBC => by simp [alignDtc] at hBC
end

/- noNone predicate (None not reachable). -/
mutual
def noNoneTy : SmtType → Bool
  | SmtType.None => false
  | SmtType.Datatype _ d => noNoneDt d
  | SmtType.Seq a => noNoneTy a
  | SmtType.Set a => noNoneTy a
  | SmtType.Map a b => native_and (noNoneTy a) (noNoneTy b)
  | SmtType.FunType a b => native_and (noNoneTy a) (noNoneTy b)
  | SmtType.DtcAppType a b => native_and (noNoneTy a) (noNoneTy b)
  | _ => true
def noNoneDt : SmtDatatype → Bool
  | SmtDatatype.sum c d => native_and (noNoneDtc c) (noNoneDt d)
  | SmtDatatype.null => true
def noNoneDtc : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons T c => native_and (noNoneTy T) (noNoneDtc c)
  | SmtDatatypeCons.unit => true
end

/-- Head extractor for the non-`TypeRef` (second) clause of `__smtx_dt_cons_wf_rec`. -/
private theorem nn_cons_head (UF U : SmtType) (cFtl c : SmtDatatypeCons)
    (hNotRef : ∀ s, U ≠ SmtType.TypeRef s)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons UF cFtl) (SmtDatatypeCons.cons U c) = true) :
    __smtx_type_wf_rec UF U = true := by
  have hgen :
      __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons UF cFtl) (SmtDatatypeCons.cons U c) =
        native_ite (native_and (native_inhabited_type UF) (__smtx_type_wf_rec UF U))
          (__smtx_dt_cons_wf_rec cFtl c) false := by
    cases U with
    | TypeRef s => exact absurd rfl (hNotRef s)
    | _ => cases UF <;> rfl
  rw [hgen] at h
  by_cases hcond : native_and (native_inhabited_type UF) (__smtx_type_wf_rec UF U) = true
  · simp only [native_and, Bool.and_eq_true] at hcond; exact hcond.2
  · rw [native_ite, if_neg (by simpa using hcond)] at h
    exact absurd h (by simp)

/- THE BRIDGE: `dt_wf_rec DF D` together with `alignDt DF D` (the full side is a genuine unfold, so
its datatype fields align `D`'s) rules out `None` anywhere in `D`. -/
mutual
theorem noNoneTy_of_field (TF U : SmtType) :
    __smtx_type_wf_rec TF U = true → alignTy TF U = true → noNoneTy U
  | h, hAl => by
      cases U with
      | None => simp [__smtx_type_wf_rec] at h
      | Datatype s2 d2 =>
          cases TF with
          | Datatype s3 dTF =>
              simp only [alignTy] at hAl
              have hDt : __smtx_dt_wf_rec (__smtx_dt_substitute s3 dTF dTF) d2 = true := by
                simpa [__smtx_type_wf_rec] using h
              have hAlign : alignDt (__smtx_dt_substitute s3 dTF dTF) d2 = true :=
                alignDt_trans (__smtx_dt_substitute s3 dTF dTF) dTF d2 (alignDt_subst s3 dTF dTF) hAl
              simpa [noNoneTy] using noNoneDt_of_align (__smtx_dt_substitute s3 dTF dTF) d2 hDt hAlign
          | _ => simp [alignTy] at hAl
      | Seq a =>
          have ha : (native_inhabited_type a = true ∧ __smtx_type_wf_rec a a = true) ∧
              __smtx_type_no_alias_rec native_reflist_nil a = true := by
            simpa [__smtx_type_wf_rec, native_and] using h
          simpa [noNoneTy] using noNoneTy_of_field a a ha.1.2 (alignTy_refl a)
      | Set a =>
          have ha : (native_inhabited_type a = true ∧ __smtx_type_wf_rec a a = true) ∧
              __smtx_type_no_alias_rec native_reflist_nil a = true := by
            simpa [__smtx_type_wf_rec, native_and] using h
          simpa [noNoneTy] using noNoneTy_of_field a a ha.1.2 (alignTy_refl a)
      | Map a b =>
          have hab :
              ((native_inhabited_type a = true ∧ __smtx_type_wf_rec a a = true) ∧
                __smtx_type_no_alias_rec native_reflist_nil a = true) ∧
                (native_inhabited_type b = true ∧ __smtx_type_wf_rec b b = true) ∧
                  __smtx_type_no_alias_rec native_reflist_nil b = true := by
            simpa [__smtx_type_wf_rec, native_and] using h
          simp only [noNoneTy, native_and, Bool.and_eq_true]
          exact ⟨noNoneTy_of_field a a hab.1.1.2 (alignTy_refl a),
                 noNoneTy_of_field b b hab.2.1.2 (alignTy_refl b)⟩
      | FunType a b => simp [__smtx_type_wf_rec] at h
      | DtcAppType a b => simp [__smtx_type_wf_rec] at h
      | TypeRef s => simp [noNoneTy]
      | RegLan => simp [__smtx_type_wf_rec] at h
      | Bool => simp [noNoneTy]
      | Int => simp [noNoneTy]
      | Real => simp [noNoneTy]
      | BitVec n => simp [noNoneTy]
      | Char => simp [noNoneTy]
      | USort i => simp [noNoneTy]

theorem noNoneDt_of_align :
    (DF D : SmtDatatype) → __smtx_dt_wf_rec DF D = true → alignDt DF D = true → noNoneDt D
  | DF, SmtDatatype.null, h, hAl => by simp [noNoneDt]
  | DF, SmtDatatype.sum c d, h, hAl => by
      cases DF with
      | null => simp [alignDt] at hAl
      | sum cF dF =>
          have hParts :
              __smtx_dt_cons_wf_rec cF c = true ∧ __smtx_dt_wf_rec dF d = true := by
            by_cases hc : __smtx_dt_cons_wf_rec cF c = true
            · refine ⟨hc, ?_⟩
              simp only [__smtx_dt_wf_rec, native_ite, if_pos hc] at h; exact h
            · rw [__smtx_dt_wf_rec, native_ite, if_neg (by simpa using hc)] at h
              exact absurd h (by simp)
          have hAlParts :
              alignDtc cF c = true ∧ alignDt dF d = true := by
            simpa [alignDt, native_and] using hAl
          simp only [noNoneDt, native_and, Bool.and_eq_true]
          exact ⟨noNoneDtc_of_align cF c hParts.1 hAlParts.1,
                 noNoneDt_of_align dF d hParts.2 hAlParts.2⟩

theorem noNoneDtc_of_align :
    (CF C : SmtDatatypeCons) → __smtx_dt_cons_wf_rec CF C = true → alignDtc CF C = true → noNoneDtc C
  | CF, SmtDatatypeCons.unit, h, hAl => by simp [noNoneDtc]
  | CF, SmtDatatypeCons.cons U c, h, hAl => by
      cases CF with
      | unit => simp [alignDtc] at hAl
      | cons TF cFtl =>
          simp only [noNoneDtc, native_and, Bool.and_eq_true]
          have hAlParts : alignTy TF U = true ∧ alignDtc cFtl c = true := by
            simpa [alignDtc, native_and] using hAl
          have hTail : __smtx_dt_cons_wf_rec cFtl c = true :=
            smtx_dt_cons_wf_rec_tail_of_true h
          refine ⟨?_, noNoneDtc_of_align cFtl c hTail hAlParts.2⟩
          by_cases hRef : ∃ sU, U = SmtType.TypeRef sU
          · obtain ⟨sU, rfl⟩ := hRef; simp [noNoneTy]
          · have hNotRef : ∀ sU, U ≠ SmtType.TypeRef sU := fun sU he => hRef ⟨sU, he⟩
            have hHead : __smtx_type_wf_rec TF U = true :=
              nn_cons_head TF U cFtl c hNotRef h
            exact noNoneTy_of_field TF U hHead hAlParts.1
end

/-- The clean consequence: diagonal well-formedness excludes `None` everywhere. -/
theorem noNoneTy_of_diag_wf (A : SmtType) (h : __smtx_type_wf_rec A A = true) : noNoneTy A = true :=
  noNoneTy_of_field A A h (alignTy_refl A)

/- Injectivity of `__eo_to_smt_type`, phrased on `noNone` — the ONLY obstruction to injectivity is
two distinct EO terms both translating to `None`. No well-formedness / full-unfold reasoning, hence
no `hDiag` gap: at a datatype-constructor field the field's `noNone` comes straight from the
enclosing `noNoneDtc`. -/
mutual
theorem inj_ty_noNone :
    (T U : Term) → (A : SmtType) → noNoneTy A = true →
      __eo_to_smt_type T = A → __eo_to_smt_type U = A → T = U
  | T, U, A, hN, hT, hU => by
      cases A with
      | None => simp [noNoneTy] at hN
      | Bool => rw [eo_to_smt_type_eq_bool hT, eo_to_smt_type_eq_bool hU]
      | Int => rw [eo_to_smt_type_eq_int hT, eo_to_smt_type_eq_int hU]
      | Real => rw [eo_to_smt_type_eq_real hT, eo_to_smt_type_eq_real hU]
      | RegLan => rw [eo_to_smt_type_eq_reglan hT, eo_to_smt_type_eq_reglan hU]
      | BitVec w => rw [eo_to_smt_type_eq_bitvec hT, eo_to_smt_type_eq_bitvec hU]
      | Char => rw [eo_to_smt_type_eq_char hT, eo_to_smt_type_eq_char hU]
      | USort i => rw [eo_to_smt_type_eq_usort hT, eo_to_smt_type_eq_usort hU]
      | TypeRef s => rw [eo_to_smt_type_eq_typeref hT, eo_to_smt_type_eq_typeref hU]
      | Map A B =>
          rcases eo_to_smt_type_eq_map hT with ⟨T1, T2, rfl, hT1, hT2⟩
          rcases eo_to_smt_type_eq_map hU with ⟨U1, U2, rfl, hU1, hU2⟩
          have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
            simpa [noNoneTy, native_and] using hN
          rw [inj_ty_noNone T1 U1 A hParts.1 hT1 hU1, inj_ty_noNone T2 U2 B hParts.2 hT2 hU2]
      | Set A =>
          rcases eo_to_smt_type_eq_set hT with ⟨T0, rfl, hT0⟩
          rcases eo_to_smt_type_eq_set hU with ⟨U0, rfl, hU0⟩
          rw [inj_ty_noNone T0 U0 A (by simpa [noNoneTy] using hN) hT0 hU0]
      | Seq A =>
          rcases eo_to_smt_type_eq_seq hT with ⟨T0, rfl, hT0⟩
          rcases eo_to_smt_type_eq_seq hU with ⟨U0, rfl, hU0⟩
          rw [inj_ty_noNone T0 U0 A (by simpa [noNoneTy] using hN) hT0 hU0]
      | FunType A B =>
          rcases eo_to_smt_type_eq_fun hT with ⟨T1, T2, rfl, hT1, hT2⟩
          rcases eo_to_smt_type_eq_fun hU with ⟨U1, U2, rfl, hU1, hU2⟩
          have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
            simpa [noNoneTy, native_and] using hN
          rw [inj_ty_noNone T1 U1 A hParts.1 hT1 hU1, inj_ty_noNone T2 U2 B hParts.2 hT2 hU2]
      | DtcAppType A B =>
          rcases eo_to_smt_type_eq_dtc_app hT with ⟨T1, T2, rfl, hT1, hT2⟩
          rcases eo_to_smt_type_eq_dtc_app hU with ⟨U1, U2, rfl, hU1, hU2⟩
          have hParts : noNoneTy A = true ∧ noNoneTy B = true := by
            simpa [noNoneTy, native_and] using hN
          rw [inj_ty_noNone T1 U1 A hParts.1 hT1 hU1, inj_ty_noNone T2 U2 B hParts.2 hT2 hU2]
      | Datatype s d =>
          by_cases hs : s = native_string_lit "@Tuple"
          · subst s
            have hBody : noNoneDt d = true := by simpa [noNoneTy] using hN
            rcases eo_to_smt_type_eq_tuple_datatype hT with hUnitT | hTupleT
            · rcases hUnitT with ⟨rfl, hDT⟩
              rcases eo_to_smt_type_eq_tuple_datatype hU with hUnitU | hTupleU
              · rcases hUnitU with ⟨rfl, _⟩; rfl
              · rcases hTupleU with ⟨y, x, c, hUShape, hxU, hDU⟩; subst U; simp [hDT] at hDU
            · rcases hTupleT with ⟨yT, xT, cT, rfl, hxT, hDT⟩
              rcases eo_to_smt_type_eq_tuple_datatype hU with hUnitU | hTupleU
              · rcases hUnitU with ⟨hUShape, hDU⟩; subst U; simp [hDU] at hDT
              · rcases hTupleU with ⟨yU, xU, cU, hUShape, hxU, hDU⟩; subst U
                have hDsum :
                    SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT) SmtDatatype.null =
                      SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type yU) cU) SmtDatatype.null :=
                  hDT.symm.trans hDU
                injection hDsum with hCons _
                injection hCons with hY hC
                subst cU
                have hbParts : noNoneTy (__eo_to_smt_type yT) = true ∧ noNoneDtc cT = true := by
                  rw [hDT] at hBody
                  simpa [noNoneDt, noNoneDtc, native_and] using hBody
                have hyEq : yT = yU :=
                  inj_ty_noNone yT yU (__eo_to_smt_type yT) hbParts.1 rfl hY.symm
                have hxEq : xT = xU :=
                  inj_ty_noNone xT xU (SmtType.Datatype (native_string_lit "@Tuple")
                      (SmtDatatype.sum cT SmtDatatype.null))
                    (by simpa [noNoneTy, noNoneDt, native_and] using hbParts.2)
                    hxT hxU
                subst yU; subst xU; rfl
          · rcases eo_to_smt_type_eq_datatype_non_tuple hs hT with ⟨dT, rfl, hDT⟩
            rcases eo_to_smt_type_eq_datatype_non_tuple hs hU with ⟨dU, rfl, hDU⟩
            rw [inj_dt_noNone dT dU d (by simpa [noNoneTy] using hN) hDT hDU]

theorem inj_dt_noNone :
    (d e : Datatype) → (D : SmtDatatype) → noNoneDt D = true →
      __eo_to_smt_datatype d = D → __eo_to_smt_datatype e = D → d = e
  | d, e, SmtDatatype.null, hN, hd, he => by
      cases d <;> cases e <;> simp [__eo_to_smt_datatype] at hd he ⊢
  | d, e, SmtDatatype.sum C Dtail, hN, hd, he => by
      have hParts : noNoneDtc C = true ∧ noNoneDt Dtail = true := by
        simpa [noNoneDt, native_and] using hN
      cases d with
      | null => simp [__eo_to_smt_datatype] at hd
      | sum c dt =>
          cases e with
          | null => simp [__eo_to_smt_datatype] at he
          | sum c' dt' =>
              simp only [__eo_to_smt_datatype] at hd he
              obtain ⟨hc, hdTail⟩ := by simpa using hd
              obtain ⟨hc', heTail⟩ := by simpa using he
              rw [inj_dtc_noNone c c' C hParts.1 hc hc',
                  inj_dt_noNone dt dt' Dtail hParts.2 hdTail heTail]

theorem inj_dtc_noNone :
    (c e : DatatypeCons) → (C : SmtDatatypeCons) → noNoneDtc C = true →
      __eo_to_smt_datatype_cons c = C → __eo_to_smt_datatype_cons e = C → c = e
  | c, e, SmtDatatypeCons.unit, hN, hc, he => by
      cases c <;> cases e <;> simp [__eo_to_smt_datatype_cons] at hc he ⊢
  | c, e, SmtDatatypeCons.cons A Ctail, hN, hc, he => by
      have hParts : noNoneTy A = true ∧ noNoneDtc Ctail = true := by
        simpa [noNoneDtc, native_and] using hN
      cases c with
      | unit => simp [__eo_to_smt_datatype_cons] at hc
      | cons T ct =>
          cases e with
          | unit => simp [__eo_to_smt_datatype_cons] at he
          | cons U cu =>
              simp only [__eo_to_smt_datatype_cons] at hc he
              obtain ⟨hT, hct⟩ := by simpa using hc
              obtain ⟨hU, hcu⟩ := by simpa using he
              rw [inj_ty_noNone T U A hParts.1 hT hU,
                  inj_dtc_noNone ct cu Ctail hParts.2 hct hcu]
end

end AlignNoNone

/-- EO-to-SMT type translation is injective on well-formed type fields. The field-wf hypothesis is
exactly the diagonal `__smtx_type_wf_rec A A`, which (via `noNoneTy_of_diag_wf`) excludes `None`
everywhere in `A`; injectivity then follows from `inj_ty_noNone`, with no full/unfold reasoning. -/
theorem eo_to_smt_type_injective_of_field_wf_rec
    {T U : Term} {A : SmtType} {refs : RefList}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : smtx_type_field_wf_rec A refs) :
    T = U :=
  inj_ty_noNone T U A (noNoneTy_of_diag_wf A hWF) hT hU

/-- `noNone` follows from self-substituted well-formedness: `__smtx_dt_wf_rec (subst s D D) D` is the
body of `__smtx_type_wf_rec (Datatype s D) (Datatype s D)`, and the substitution image is aligned
with `D` (`alignDt_subst`), so no `None` survives anywhere in `D`. -/
theorem noNoneDt_of_self_wf {s : native_String} {D : SmtDatatype}
    (h : __smtx_dt_wf_rec (__smtx_dt_substitute s D D) D = true) : noNoneDt D = true :=
  noNoneDt_of_align (__smtx_dt_substitute s D D) D h (alignDt_subst s D D)

/-- `noNone` from diagonal datatype well-formedness `__smtx_dt_wf_rec D D` (the reflexive-alignment
case), used when the full side is literally `D` itself. -/
theorem noNoneDt_of_diag_wf {D : SmtDatatype}
    (h : __smtx_dt_wf_rec D D = true) : noNoneDt D = true :=
  noNoneDt_of_align D D h (alignDt_refl D)

/-- EO datatype translation is injective for well-formed datatypes. The full side is the genuine
self-substitution `__smtx_dt_substitute s D D`, whose alignment with `D` (`alignDt_subst`) certifies
`noNone D`; injectivity then follows from `inj_dt_noNone`, with no full/unfold (`hDiag`) reasoning. -/
theorem eo_to_smt_datatype_injective_of_wf_rec
    {d e : Datatype} {D : SmtDatatype} {s : native_String}
    (hd : __eo_to_smt_datatype d = D)
    (he : __eo_to_smt_datatype e = D)
    (hWF : __smtx_dt_wf_rec (__smtx_dt_substitute s D D) D = true) :
    d = e :=
  inj_dt_noNone d e D (noNoneDt_of_self_wf hWF) hd he

/-- Variant of `eo_to_smt_datatype_injective_of_wf_rec` taking diagonal datatype well-formedness
`__smtx_dt_wf_rec D D` directly (the full side is `D` itself, e.g. a translated datatype whose
diagonal well-formedness is established directly). -/
theorem eo_to_smt_datatype_injective_of_diag_wf
    {d e : Datatype} {D : SmtDatatype}
    (hd : __eo_to_smt_datatype d = D)
    (he : __eo_to_smt_datatype e = D)
    (hWF : __smtx_dt_wf_rec D D = true) :
    d = e :=
  inj_dt_noNone d e D (noNoneDt_of_diag_wf hWF) hd he

-/

/-- EO type translation never produces a tuple-private type reference. -/
theorem eo_to_smt_type_ne_tuple_typeref
    (T : Term) :
    __eo_to_smt_type T ≠ SmtType.TypeRef (native_string_lit "@Tuple") := by
  intro h
  have hT : T = Term.DatatypeTypeRef (native_string_lit "@Tuple") := eo_to_smt_type_eq_typeref h
  subst T
  change native_ite (__eo_reserved_datatype_name (native_string_lit "@Tuple")) SmtType.None
      (SmtType.TypeRef (native_string_lit "@Tuple")) = SmtType.TypeRef (native_string_lit "@Tuple") at h
  rw [show __eo_reserved_datatype_name (native_string_lit "@Tuple") = true by native_decide] at h
  simp [native_ite] at h

mutual

/--
If an EO term translates as a well-formed SMT type, the EO term itself has EO
type `Type`.

Datatype fields are the one place where SMT permits recursive `TypeRef`s, so
the tuple case handles `TypeRef` fields by inverting `__eo_to_smt_type`
directly and uses recursive well-formedness for all other field types.
-/
theorem eo_typeof_type_of_smt_type_wf_rec :
    (T : Term) ->
    __smtx_type_wf_rec (__eo_to_smt_type T) = true ->
    __eo_typeof T = Term.Type
  | Term.UOp op, hWF => by
      cases op <;> simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF ⊢ <;>
        first | rfl | contradiction
  | Term.UOp1 op a, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.UOp2 op a b, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.UOp3 op a b c, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.__eo_List, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.__eo_List_nil, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.__eo_List_cons, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Bool, hWF => rfl
  | Term.Boolean b, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Numeral n, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Rational r, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.String s, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Binary w n, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Type, hWF => rfl
  | Term.Stuck, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Apply f x, hWF => by
      cases f with
      | UOp op =>
          cases op <;> try (simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF)
          case BitVec =>
            cases x <;> try (simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF)
            case Numeral n =>
              change __eo_typeof_BitVec (__eo_typeof (Term.Numeral n)) = Term.Type
              rfl
          case Seq =>
            have hSeqWf := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
              (SmtType.Seq (__eo_to_smt_type x)) (by
                simpa [__eo_to_smt_type] using hWF)
            have hxWF := seq_type_wf_rec_component_of_wf hSeqWf
            have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
            change __eo_typeof_Seq (__eo_typeof x) = Term.Type
            rw [hx]
            rfl
          case Set =>
            have hSetWf := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
              (SmtType.Set (__eo_to_smt_type x)) (by
                simpa [__eo_to_smt_type] using hWF)
            have hxWF := set_type_wf_rec_component_of_wf hSetWf
            have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
            change __eo_typeof_Seq (__eo_typeof x) = Term.Type
            rw [hx]
            rfl
          all_goals try contradiction
      | Apply g y =>
          cases g with
          | FunType =>
              have hOuter := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type y)
                (__smtx_typeof_guard (__eo_to_smt_type x)
                  (native_ite
                    (__smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))) (by
                  simpa [__eo_to_smt_type] using hWF)
              have hFun := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                (native_ite
                  (__smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
                  (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
                  (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))) hOuter
              cases hFin :
                  __smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                simp [native_ite, hFin, __smtx_type_wf_rec] at hFun
          | UOp op =>
              cases op <;> try (simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF)
              case Array =>
                have hOuter := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type y)
                  (__smtx_typeof_guard (__eo_to_smt_type x)
                    (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) (by
                    simpa [__eo_to_smt_type] using hWF)
                have hMap := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                  (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) hOuter
                rcases map_type_wf_rec_components_of_wf hMap with ⟨hyWF, hxWF⟩
                have hy := eo_typeof_type_of_smt_type_wf_rec y hyWF
                have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
                change __eo_typeof__at__at_Pair (__eo_typeof y) (__eo_typeof x) = Term.Type
                rw [hy, hx]
                rfl
              case Tuple =>
                let raw :=
                  __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
                have hRawWf : __smtx_type_wf raw = true := by
                  cases hw : __smtx_type_wf raw
                  · simp [raw, hw, __smtx_type_wf_rec] at hWF
                  · rfl
                have hRawNN : raw ≠ SmtType.None := by
                  intro hNone
                  simp [hNone, __smtx_type_wf, __smtx_type_wf_component,
                    __smtx_type_wf_rec, native_and] at hRawWf
                rcases eo_to_smt_type_tuple_eq_none_or_datatype
                    (__eo_to_smt_type y) (__eo_to_smt_type x) with hNone | ⟨dd, hRaw⟩
                · exact False.elim (hRawNN (by simpa [raw] using hNone))
                · have hRaw' :
                      __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) =
                        SmtType.Datatype (native_string_lit "@Tuple") dd := hRaw
                  rcases eo_to_smt_type_tuple_eq_datatype_inv hRaw' with ⟨c, hx, rfl⟩
                  have hyComp :
                      __smtx_type_wf_component (__eo_to_smt_type y) = true := by
                    by_cases hy :
                        __smtx_type_wf_component (__eo_to_smt_type y) = true
                    · exact hy
                    · have hyF :
                          __smtx_type_wf_component (__eo_to_smt_type y) = false :=
                        Bool.eq_false_iff.mpr hy
                      simp [__eo_to_smt_type_tuple, __eo_to_smt_tuple_decl,
                        hx, hyF] at hRaw'
                  have hyWF : __smtx_type_wf_rec (__eo_to_smt_type y) = true := by
                    have hParts :
                        native_inhabited_type (__eo_to_smt_type y) = true ∧
                          __smtx_type_wf_rec (__eo_to_smt_type y) = true := by
                      simpa [__smtx_type_wf_component, native_and] using hyComp
                    exact hParts.2
                  have hyType := eo_typeof_type_of_smt_type_wf_rec y hyWF
                  have hxType := eo_typeof_type_of_smt_tuple x
                    (__eo_to_smt_tuple_decl
                      (SmtDatatype.sum c SmtDatatype.null)) hx
                  change __eo_typeof__at__at_Pair (__eo_typeof y) (__eo_typeof x) =
                    Term.Type
                  rw [hyType, hxType]
                  rfl
          | _ => simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
      | _ => simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.FunType, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Var name T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.DatatypeType s d, hWF => rfl
  | Term.DatatypeTypeRef s, hWF => by
      by_cases hr : __eo_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, hr, __smtx_type_wf_rec] at hWF
  | Term.DtcAppType T U, hWF => by
      have hInner := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U))) (by
          simpa [__eo_to_smt_type] using hWF)
      have hDtc := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type U)
        (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)) hInner
      simp [__smtx_type_wf_rec] at hDtc
  | Term.DtCons s d i, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.DtSel s d i j, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.USort i, hWF => rfl
  | Term.UConst i T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
termination_by T => sizeOf T

/-- A term translating to the private tuple datatype is an EO tuple type. -/
theorem eo_typeof_type_of_smt_tuple :
    (T : Term) ->
    (dd : SmtDatatypeDecl) ->
    __eo_to_smt_type T =
      SmtType.Datatype (native_string_lit "@Tuple") dd ->
    __eo_typeof T = Term.Type
  | T, dd, h => by
      rcases eo_to_smt_type_eq_tuple_datatype h with hUnit | hCons
      · rcases hUnit with ⟨rfl, rfl⟩
        rfl
      · rcases hCons with ⟨y, x, c, rfl, hx, rfl⟩
        have hRawWf :
            __smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) = true := by
          change native_ite
              (__smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)))
              (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
              SmtType.None = _ at h
          cases hw : __smtx_type_wf
              (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
            simp [native_ite, hw] at h ⊢
        have hRaw :
            __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) =
              SmtType.Datatype (native_string_lit "@Tuple")
                (__eo_to_smt_tuple_decl
                  (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) c)
                    SmtDatatype.null)) := by
          change native_ite
              (__smtx_type_wf
                (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)))
              (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
              SmtType.None = _ at h
          simpa [hRawWf] using h
        have hyComp : __smtx_type_wf_component (__eo_to_smt_type y) = true := by
          by_cases hy : __smtx_type_wf_component (__eo_to_smt_type y) = true
          · exact hy
          · have hyF : __smtx_type_wf_component (__eo_to_smt_type y) = false :=
              Bool.eq_false_iff.mpr hy
            simp [__eo_to_smt_type_tuple, __eo_to_smt_tuple_decl,
              hx, hyF] at hRaw
        have hyWF : __smtx_type_wf_rec (__eo_to_smt_type y) = true := by
          have hParts :
              native_inhabited_type (__eo_to_smt_type y) = true ∧
                __smtx_type_wf_rec (__eo_to_smt_type y) = true := by
            simpa [__smtx_type_wf_component, native_and] using hyComp
          exact hParts.2
        have hyType := eo_typeof_type_of_smt_type_wf_rec y hyWF
        have hxType := eo_typeof_type_of_smt_tuple x
          (__eo_to_smt_tuple_decl (SmtDatatype.sum c SmtDatatype.null)) hx
        change __eo_typeof__at__at_Pair (__eo_typeof y) (__eo_typeof x) = Term.Type
        rw [hyType, hxType]
        rfl
termination_by T => sizeOf T

end

theorem eo_typeof_type_of_smt_type_wf
    (T : Term)
    (h : __smtx_type_wf (__eo_to_smt_type T) = true) :
    __eo_typeof T = Term.Type := by
  by_cases hReg : __eo_to_smt_type T = SmtType.RegLan
  · rw [eo_to_smt_type_eq_reglan hReg]
    rfl
  · by_cases hFun : ∃ A B : SmtType, __eo_to_smt_type T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, hTy⟩
      rcases eo_to_smt_type_eq_fun hTy with ⟨U, V, rfl, hU, hV⟩
      rcases fun_type_wf_rec_components_of_wf (by simpa [hTy] using h) with ⟨hURec, hVRec⟩
      have hUType := eo_typeof_type_of_smt_type_wf_rec U (by
        simpa [hU] using hURec)
      have hVType := eo_typeof_type_of_smt_type_wf V (by
        simpa [hV] using hVRec)
      change __eo_typeof_fun_type (__eo_typeof U) (__eo_typeof V) = Term.Type
      rw [hUType, hVType]
      rfl
    · exact eo_typeof_type_of_smt_type_wf_rec T (by
        cases hTy : __eo_to_smt_type T <;>
          simp [hTy, __smtx_type_wf, __smtx_type_wf_component,
            native_and] at h hReg hFun ⊢
        all_goals first | contradiction | exact h.2 | exact h.1.2)
termination_by T

theorem eo_typeof_type_of_smt_type_field_wf_rec
    (T : Term) (refs : RefList)
    (h : smtx_type_field_wf_rec (__eo_to_smt_type T) refs) :
    __eo_typeof T = Term.Type := by
  cases hTy : __eo_to_smt_type T
  case TypeRef s =>
    simp [smtx_type_field_wf_rec, hTy, __smtx_type_wf_rec] at h
  all_goals
    exact eo_typeof_type_of_smt_type_wf_rec T (by
      simpa [smtx_type_field_wf_rec, hTy] using h)

/- `None` is the only source of non-injectivity in type translation.  These
predicates include declaration blocks, which replaced the old substituted
datatype-body representation. -/
mutual

@[expose] def noNoneTy : SmtType → Bool
  | SmtType.None => false
  | SmtType.Datatype _ dd => noNoneDecl dd
  | SmtType.Seq A => noNoneTy A
  | SmtType.Set A => noNoneTy A
  | SmtType.Map A B => native_and (noNoneTy A) (noNoneTy B)
  | SmtType.FunType A B => native_and (noNoneTy A) (noNoneTy B)
  | SmtType.DtcAppType A B => native_and (noNoneTy A) (noNoneTy B)
  | _ => true

@[expose] def noNoneDecl : SmtDatatypeDecl → Bool
  | SmtDatatypeDecl.nil => true
  | SmtDatatypeDecl.cons _ d dd => native_and (noNoneDt d) (noNoneDecl dd)

@[expose] def noNoneDt : SmtDatatype → Bool
  | SmtDatatype.null => true
  | SmtDatatype.sum c d => native_and (noNoneDtc c) (noNoneDt d)

@[expose] def noNoneDtc : SmtDatatypeCons → Bool
  | SmtDatatypeCons.unit => true
  | SmtDatatypeCons.cons T c => native_and (noNoneTy T) (noNoneDtc c)

end

theorem eo_to_smt_dd_lookup (s : native_String) :
    ∀ dd : DatatypeDecl,
      __eo_to_smt_datatype (__eo_dd_lookup s dd) =
        __smtx_dd_lookup s (__eo_to_smt_datatype_decl dd)
  | DatatypeDecl.nil => by
      simp [__eo_dd_lookup, __smtx_dd_lookup, __eo_to_smt_datatype,
        __eo_to_smt_datatype_decl]
  | DatatypeDecl.cons s2 d dd => by
      by_cases hs : s = s2
      · subst s2
        simp [__eo_dd_lookup, __smtx_dd_lookup, __eo_to_smt_datatype_decl,
          native_ite, native_streq]
      · simp [__eo_dd_lookup, __smtx_dd_lookup, __eo_to_smt_datatype_decl,
          native_ite, native_streq, hs, eo_to_smt_dd_lookup s dd]

private theorem eo_dtc_resolve_cons_of_not_ref
    (T : Term) (c : DatatypeCons) (dd : DatatypeDecl)
    (h : ∀ s, T ≠ Term.DatatypeTypeRef s) :
    __eo_dtc_resolve (DatatypeCons.cons T c) dd =
      DatatypeCons.cons T (__eo_dtc_resolve c dd) := by
  cases T <;> simp [__eo_dtc_resolve] at h ⊢

private theorem smtx_dtc_resolve_cons_of_not_typeref
    (T : SmtType) (c : SmtDatatypeCons) (dd : SmtDatatypeDecl)
    (h : ∀ s, T ≠ SmtType.TypeRef s) :
    __smtx_dtc_resolve (SmtDatatypeCons.cons T c) dd =
      SmtDatatypeCons.cons T (__smtx_dtc_resolve c dd) := by
  cases T <;> simp [__smtx_dtc_resolve] at h ⊢

theorem eo_to_smt_dtc_resolve_of_no_none :
    ∀ (c : DatatypeCons) (dd : DatatypeDecl),
      noNoneDtc (__eo_to_smt_datatype_cons c) = true ->
      noNoneDecl (__eo_to_smt_datatype_decl dd) = true ->
      __eo_to_smt_datatype_cons (__eo_dtc_resolve c dd) =
        __smtx_dtc_resolve (__eo_to_smt_datatype_cons c)
          (__eo_to_smt_datatype_decl dd)
  | DatatypeCons.unit, dd, _, _ => by
      simp [__eo_dtc_resolve, __smtx_dtc_resolve, __eo_to_smt_datatype_cons]
  | DatatypeCons.cons T c, dd, hC, hDD => by
      have hp :
          noNoneTy (__eo_to_smt_type T) = true ∧
            noNoneDtc (__eo_to_smt_datatype_cons c) = true := by
        simpa [__eo_to_smt_datatype_cons, noNoneDtc, native_and] using hC
      by_cases hRef : ∃ s, T = Term.DatatypeTypeRef s
      · rcases hRef with ⟨s, rfl⟩
        have hReserved : __eo_reserved_datatype_name s = false := by
          cases hr : __eo_reserved_datatype_name s
          · rfl
          · simp [__eo_to_smt_type, native_ite, hr, noNoneTy] at hp
        simp [__eo_dtc_resolve, __smtx_dtc_resolve,
          __eo_to_smt_datatype_cons, __eo_to_smt_type, native_ite, hReserved,
          eo_to_smt_dtc_resolve_of_no_none c dd hp.2 hDD]
      · have hNotRef : ∀ s, T ≠ Term.DatatypeTypeRef s := by
          intro s hEq
          exact hRef ⟨s, hEq⟩
        have hNotTypeRef : ∀ s, __eo_to_smt_type T ≠ SmtType.TypeRef s := by
          intro s hEq
          exact hRef ⟨s, eo_to_smt_type_eq_typeref hEq⟩
        rw [eo_dtc_resolve_cons_of_not_ref T c dd hNotRef]
        simp only [__eo_to_smt_datatype_cons]
        rw [smtx_dtc_resolve_cons_of_not_typeref
            (__eo_to_smt_type T) (__eo_to_smt_datatype_cons c)
            (__eo_to_smt_datatype_decl dd) hNotTypeRef]
        rw [eo_to_smt_dtc_resolve_of_no_none c dd hp.2 hDD]

theorem eo_to_smt_dt_resolve_of_no_none :
    ∀ (d : Datatype) (dd : DatatypeDecl),
      noNoneDt (__eo_to_smt_datatype d) = true ->
      noNoneDecl (__eo_to_smt_datatype_decl dd) = true ->
      __eo_to_smt_datatype (__eo_dt_resolve d dd) =
        __smtx_dt_resolve (__eo_to_smt_datatype d)
          (__eo_to_smt_datatype_decl dd)
  | Datatype.null, dd, _, _ => by
      simp [__eo_dt_resolve, __smtx_dt_resolve, __eo_to_smt_datatype]
  | Datatype.sum c d, dd, hD, hDD => by
      have hp :
          noNoneDtc (__eo_to_smt_datatype_cons c) = true ∧
            noNoneDt (__eo_to_smt_datatype d) = true := by
        simpa [__eo_to_smt_datatype, noNoneDt, native_and] using hD
      simp [__eo_dt_resolve, __smtx_dt_resolve, __eo_to_smt_datatype,
        eo_to_smt_dtc_resolve_of_no_none c dd hp.1 hDD,
        eo_to_smt_dt_resolve_of_no_none d dd hp.2 hDD]

theorem eo_to_smt_dd_resolve_of_no_none
    (s : native_String) (dd : DatatypeDecl)
    (hLookup :
      noNoneDt (__smtx_dd_lookup s (__eo_to_smt_datatype_decl dd)) = true)
    (hDecl : noNoneDecl (__eo_to_smt_datatype_decl dd) = true) :
    __eo_to_smt_datatype (__eo_dd_resolve s dd) =
      __smtx_dt_resolve
        (__smtx_dd_lookup s (__eo_to_smt_datatype_decl dd))
        (__eo_to_smt_datatype_decl dd) := by
  have hLookup' :
      noNoneDt (__eo_to_smt_datatype (__eo_dd_lookup s dd)) = true := by
    rw [eo_to_smt_dd_lookup]
    exact hLookup
  unfold __eo_dd_resolve
  rw [eo_to_smt_dt_resolve_of_no_none (__eo_dd_lookup s dd) dd hLookup' hDecl,
    eo_to_smt_dd_lookup]

theorem noNoneDtc_resolve :
    ∀ (c : SmtDatatypeCons) (dd : SmtDatatypeDecl),
      noNoneDtc c = true -> noNoneDecl dd = true ->
        noNoneDtc (__smtx_dtc_resolve c dd) = true
  | SmtDatatypeCons.unit, dd, _, _ => by simp [__smtx_dtc_resolve, noNoneDtc]
  | SmtDatatypeCons.cons T c, dd, hC, hDD => by
      have hp : noNoneTy T = true ∧ noNoneDtc c = true := by
        simpa [noNoneDtc, native_and] using hC
      have hTail := noNoneDtc_resolve c dd hp.2 hDD
      cases T <;> simp_all [__smtx_dtc_resolve, noNoneDtc, noNoneTy, native_and]

theorem noNoneDt_resolve :
    ∀ (d : SmtDatatype) (dd : SmtDatatypeDecl),
      noNoneDt d = true -> noNoneDecl dd = true ->
        noNoneDt (__smtx_dt_resolve d dd) = true
  | SmtDatatype.null, dd, _, _ => by simp [__smtx_dt_resolve, noNoneDt]
  | SmtDatatype.sum c d, dd, hD, hDD => by
      have hp : noNoneDtc c = true ∧ noNoneDt d = true := by
        simpa [noNoneDt, native_and] using hD
      simp [__smtx_dt_resolve, noNoneDt, native_and,
        noNoneDtc_resolve c dd hp.1 hDD,
        noNoneDt_resolve d dd hp.2 hDD]

mutual

theorem noNoneTy_of_wf :
    ∀ (T : SmtType), __smtx_type_wf_rec T = true → noNoneTy T = true
  | SmtType.Datatype s dd, h => by
      have hParts :
          __smtx_dd_has_dt s dd = true ∧ __smtx_decl_wf_rec dd dd = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      simpa [noNoneTy] using noNoneDecl_of_wf dd dd hParts.2
  | SmtType.Seq T, h => by
      have hT : __smtx_type_wf_rec T = true := by
        have hp : native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true := by
          simpa [__smtx_type_wf_rec, native_and] using h
        exact hp.2
      simpa [noNoneTy] using noNoneTy_of_wf T hT
  | SmtType.Set T, h => by
      have hT : __smtx_type_wf_rec T = true := by
        have hp : native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true := by
          simpa [__smtx_type_wf_rec, native_and] using h
        exact hp.2
      simpa [noNoneTy] using noNoneTy_of_wf T hT
  | SmtType.Map T U, h => by
      have hp :
          (native_inhabited_type T = true ∧ __smtx_type_wf_rec T = true) ∧
            native_inhabited_type U = true ∧ __smtx_type_wf_rec U = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      simp [noNoneTy, noNoneTy_of_wf T hp.1.2,
        noNoneTy_of_wf U hp.2.2, native_and]
  | SmtType.FunType T U, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.DtcAppType T U, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.TypeRef s, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.None, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.RegLan, h => by simp [__smtx_type_wf_rec] at h
  | SmtType.Bool, _ => by simp [noNoneTy]
  | SmtType.Int, _ => by simp [noNoneTy]
  | SmtType.Real, _ => by simp [noNoneTy]
  | SmtType.BitVec w, _ => by simp [noNoneTy]
  | SmtType.Char, _ => by simp [noNoneTy]
  | SmtType.USort i, _ => by simp [noNoneTy]

theorem noNoneDecl_of_wf :
    ∀ (base dd : SmtDatatypeDecl),
      __smtx_decl_wf_rec base dd = true → noNoneDecl dd = true
  | base, SmtDatatypeDecl.nil, _ => by simp [noNoneDecl]
  | base, SmtDatatypeDecl.cons s d dd, h => by
      have hp :
          __smtx_dt_wf_rec base d = true ∧
            native_inhabited_type (SmtType.Datatype s base) = true ∧
              __smtx_decl_wf_rec base dd = true ∧
                native_not (__smtx_dd_has_dt s dd) = true := by
        simpa [__smtx_decl_wf_rec, native_and] using h
      simp [noNoneDecl, noNoneDt_of_wf base d hp.1,
        noNoneDecl_of_wf base dd hp.2.2.1, native_and]

theorem noNoneDt_of_wf :
    ∀ (base : SmtDatatypeDecl) (d : SmtDatatype),
      __smtx_dt_wf_rec base d = true → noNoneDt d = true
  | base, SmtDatatype.null, _ => by simp [noNoneDt]
  | base, SmtDatatype.sum c d, h => by
      have hp :
          __smtx_dt_cons_wf_rec base c = true ∧
            __smtx_dt_wf_rec base d = true := by
        simpa [__smtx_dt_wf_rec, native_and] using h
      simp [noNoneDt, noNoneDtc_of_wf base c hp.1,
        noNoneDt_of_wf base d hp.2, native_and]

theorem noNoneDtc_of_wf :
    ∀ (base : SmtDatatypeDecl) (c : SmtDatatypeCons),
      __smtx_dt_cons_wf_rec base c = true → noNoneDtc c = true
  | base, SmtDatatypeCons.unit, _ => by simp [noNoneDtc]
  | base, SmtDatatypeCons.cons T c, h => by
      by_cases hRef : ∃ s, T = SmtType.TypeRef s
      · rcases hRef with ⟨s, rfl⟩
        have hp :
            __smtx_dd_has_dt s base = true ∧
              __smtx_dt_cons_wf_rec base c = true := by
          simpa [__smtx_dt_cons_wf_rec, native_and] using h
        simp [noNoneDtc, noNoneTy, noNoneDtc_of_wf base c hp.2, native_and]
      · have hHead : __smtx_type_wf_rec T = true := by
          have hField : smtx_type_field_wf_rec T native_reflist_nil :=
            smtx_type_field_wf_rec_of_cons_wf
              (by intro s hEq; exact hRef ⟨s, hEq⟩) h
          simpa [smtx_type_field_wf_rec] using hField
        have hTail : __smtx_dt_cons_wf_rec base c = true :=
          smtx_dt_cons_wf_rec_tail_of_true h
        simp [noNoneDtc, noNoneTy_of_wf T hHead,
          noNoneDtc_of_wf base c hTail, native_and]

end


/- Translation is injective once every recursively embedded type is known not
to be `None`.  Declaration and tuple cases are handled structurally. -/
mutual

private theorem injTyNoNone :
    ∀ (T U : Term) (A : SmtType),
      noNoneTy A = true →
      __eo_to_smt_type T = A → __eo_to_smt_type U = A → T = U
  | T, U, SmtType.None, hN, _, _ => by simp [noNoneTy] at hN
  | T, U, SmtType.Bool, _, hT, hU =>
      (eo_to_smt_type_eq_bool hT).trans (eo_to_smt_type_eq_bool hU).symm
  | T, U, SmtType.Int, _, hT, hU =>
      (eo_to_smt_type_eq_int hT).trans (eo_to_smt_type_eq_int hU).symm
  | T, U, SmtType.Real, _, hT, hU =>
      (eo_to_smt_type_eq_real hT).trans (eo_to_smt_type_eq_real hU).symm
  | T, U, SmtType.RegLan, _, hT, hU =>
      (eo_to_smt_type_eq_reglan hT).trans (eo_to_smt_type_eq_reglan hU).symm
  | T, U, SmtType.BitVec w, _, hT, hU =>
      (eo_to_smt_type_eq_bitvec hT).trans (eo_to_smt_type_eq_bitvec hU).symm
  | T, U, SmtType.Char, _, hT, hU =>
      (eo_to_smt_type_eq_char hT).trans (eo_to_smt_type_eq_char hU).symm
  | T, U, SmtType.USort i, _, hT, hU =>
      (eo_to_smt_type_eq_usort hT).trans (eo_to_smt_type_eq_usort hU).symm
  | T, U, SmtType.TypeRef s, _, hT, hU =>
      (eo_to_smt_type_eq_typeref hT).trans (eo_to_smt_type_eq_typeref hU).symm
  | T, U, SmtType.Seq A, hN, hT, hU => by
      rcases eo_to_smt_type_eq_seq hT with ⟨T0, rfl, hT0⟩
      rcases eo_to_smt_type_eq_seq hU with ⟨U0, rfl, hU0⟩
      rw [injTyNoNone T0 U0 A (by simpa [noNoneTy] using hN) hT0 hU0]
  | T, U, SmtType.Set A, hN, hT, hU => by
      rcases eo_to_smt_type_eq_set hT with ⟨T0, rfl, hT0⟩
      rcases eo_to_smt_type_eq_set hU with ⟨U0, rfl, hU0⟩
      rw [injTyNoNone T0 U0 A (by simpa [noNoneTy] using hN) hT0 hU0]
  | T, U, SmtType.Map A B, hN, hT, hU => by
      rcases eo_to_smt_type_eq_map hT with ⟨T1, T2, rfl, hT1, hT2⟩
      rcases eo_to_smt_type_eq_map hU with ⟨U1, U2, rfl, hU1, hU2⟩
      have hp : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hN
      rw [injTyNoNone T1 U1 A hp.1 hT1 hU1,
        injTyNoNone T2 U2 B hp.2 hT2 hU2]
  | T, U, SmtType.FunType A B, hN, hT, hU => by
      rcases eo_to_smt_type_eq_fun hT with ⟨T1, T2, rfl, hT1, hT2⟩
      rcases eo_to_smt_type_eq_fun hU with ⟨U1, U2, rfl, hU1, hU2⟩
      have hp : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hN
      rw [injTyNoNone T1 U1 A hp.1 hT1 hU1,
        injTyNoNone T2 U2 B hp.2 hT2 hU2]
  | T, U, SmtType.DtcAppType A B, hN, hT, hU => by
      rcases eo_to_smt_type_eq_dtc_app hT with ⟨T1, T2, rfl, hT1, hT2⟩
      rcases eo_to_smt_type_eq_dtc_app hU with ⟨U1, U2, rfl, hU1, hU2⟩
      have hp : noNoneTy A = true ∧ noNoneTy B = true := by
        simpa [noNoneTy, native_and] using hN
      rw [injTyNoNone T1 U1 A hp.1 hT1 hU1,
        injTyNoNone T2 U2 B hp.2 hT2 hU2]
  | T, U, SmtType.Datatype s dd, hN, hT, hU => by
      by_cases hs : s = native_string_lit "@Tuple"
      · subst s
        rcases eo_to_smt_type_eq_tuple_datatype hT with hUnitT | hConsT
        · rcases hUnitT with ⟨rfl, hddT⟩
          rcases eo_to_smt_type_eq_tuple_datatype hU with hUnitU | hConsU
          · rcases hUnitU with ⟨rfl, _⟩
            rfl
          · rcases hConsU with ⟨y, x, c, rfl, _, hddU⟩
            simp [hddT, __eo_to_smt_tuple_decl] at hddU
        · rcases hConsT with ⟨yT, xT, cT, rfl, hxT, hddT⟩
          rcases eo_to_smt_type_eq_tuple_datatype hU with hUnitU | hConsU
          · rcases hUnitU with ⟨rfl, hddU⟩
            simp [hddU, __eo_to_smt_tuple_decl] at hddT
          · rcases hConsU with ⟨yU, xU, cU, rfl, hxU, hddU⟩
            have hDecl :
                __eo_to_smt_tuple_decl
                    (SmtDatatype.sum
                      (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT)
                      SmtDatatype.null) =
                  __eo_to_smt_tuple_decl
                    (SmtDatatype.sum
                      (SmtDatatypeCons.cons (__eo_to_smt_type yU) cU)
                      SmtDatatype.null) := hddT.symm.trans hddU
            simp [__eo_to_smt_tuple_decl] at hDecl
            rcases hDecl with ⟨hY, hC⟩
            subst cU
            have hp :
                noNoneTy (__eo_to_smt_type yT) = true ∧ noNoneDtc cT = true := by
              rw [hddT] at hN
              simpa [noNoneTy, noNoneDecl, noNoneDt, noNoneDtc,
                __eo_to_smt_tuple_decl,
                native_and] using hN
            have hy : yT = yU :=
              injTyNoNone yT yU (__eo_to_smt_type yT) hp.1 rfl hY.symm
            have hx : xT = xU :=
              injTyNoNone xT xU
                (SmtType.Datatype (native_string_lit "@Tuple")
                  (__eo_to_smt_tuple_decl
                    (SmtDatatype.sum cT SmtDatatype.null)))
                (by simpa [noNoneTy, noNoneDecl, noNoneDt, noNoneDtc,
                    __eo_to_smt_tuple_decl, native_and] using hp.2)
                hxT hxU
            subst yU
            subst xU
            rfl
      · rcases eo_to_smt_type_eq_datatype_non_tuple hs hT with ⟨dT, rfl, hdT⟩
        rcases eo_to_smt_type_eq_datatype_non_tuple hs hU with ⟨dU, rfl, hdU⟩
        rw [injDeclNoNone dT dU dd (by simpa [noNoneTy] using hN) hdT hdU]

private theorem injDeclNoNone :
    ∀ (d e : DatatypeDecl) (D : SmtDatatypeDecl),
      noNoneDecl D = true →
      __eo_to_smt_datatype_decl d = D →
      __eo_to_smt_datatype_decl e = D → d = e
  | d, e, SmtDatatypeDecl.nil, hN, hd, he => by
      cases d <;> cases e <;>
        simp [__eo_to_smt_datatype_decl] at hd he ⊢
  | d, e, SmtDatatypeDecl.cons name body rest, hN, hd, he => by
      have hp : noNoneDt body = true ∧ noNoneDecl rest = true := by
        simpa [noNoneDecl, native_and] using hN
      cases d with
      | nil => simp [__eo_to_smt_datatype_decl] at hd
      | cons s d dd =>
          cases e with
          | nil => simp [__eo_to_smt_datatype_decl] at he
          | cons s' d' dd' =>
              simp only [__eo_to_smt_datatype_decl] at hd he
              injection hd with hs hbody hrest
              injection he with hs' hbody' hrest'
              have hD : d = d' := injDtNoNone d d' body hp.1 hbody hbody'
              have hDD : dd = dd' :=
                injDeclNoNone dd dd' rest hp.2 hrest hrest'
              subst s
              subst s'
              subst d'
              subst dd'
              rfl

private theorem injDtNoNone :
    ∀ (d e : Datatype) (D : SmtDatatype),
      noNoneDt D = true →
      __eo_to_smt_datatype d = D → __eo_to_smt_datatype e = D → d = e
  | d, e, SmtDatatype.null, hN, hd, he => by
      cases d <;> cases e <;> simp [__eo_to_smt_datatype] at hd he ⊢
  | d, e, SmtDatatype.sum C Dtail, hN, hd, he => by
      have hp : noNoneDtc C = true ∧ noNoneDt Dtail = true := by
        simpa [noNoneDt, native_and] using hN
      cases d with
      | null => simp [__eo_to_smt_datatype] at hd
      | sum c d =>
          cases e with
          | null => simp [__eo_to_smt_datatype] at he
          | sum c' d' =>
              simp only [__eo_to_smt_datatype] at hd he
              injection hd with hc hdt
              injection he with hc' hdt'
              have hC : c = c' := injDtcNoNone c c' C hp.1 hc hc'
              have hD : d = d' := injDtNoNone d d' Dtail hp.2 hdt hdt'
              subst c'
              subst d'
              rfl

private theorem injDtcNoNone :
    ∀ (c e : DatatypeCons) (C : SmtDatatypeCons),
      noNoneDtc C = true →
      __eo_to_smt_datatype_cons c = C →
      __eo_to_smt_datatype_cons e = C → c = e
  | c, e, SmtDatatypeCons.unit, hN, hc, he => by
      cases c <;> cases e <;> simp [__eo_to_smt_datatype_cons] at hc he ⊢
  | c, e, SmtDatatypeCons.cons A Ctail, hN, hc, he => by
      have hp : noNoneTy A = true ∧ noNoneDtc Ctail = true := by
        simpa [noNoneDtc, native_and] using hN
      cases c with
      | unit => simp [__eo_to_smt_datatype_cons] at hc
      | cons T c =>
          cases e with
          | unit => simp [__eo_to_smt_datatype_cons] at he
          | cons U cu =>
              simp only [__eo_to_smt_datatype_cons] at hc he
              injection hc with hT hct
              injection he with hU hcu
              have hHead : T = U := injTyNoNone T U A hp.1 hT hU
              have hTail : c = cu := injDtcNoNone c cu Ctail hp.2 hct hcu
              subst U
              subst cu
              rfl

end


/-- EO-to-SMT type translation is injective whenever the translated type
contains no recursively embedded `None`.  This includes the intermediate
`FunType` and `DtcAppType` shapes used while typing applications. -/
theorem eo_to_smt_type_injective_of_no_none
    {T U : Term} {A : SmtType}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hNoNone : noNoneTy A = true) :
    T = U :=
  injTyNoNone T U A hNoNone hT hU


theorem eo_to_smt_type_injective_of_field_wf_rec
    {T U : Term} {A : SmtType} {refs : RefList}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : smtx_type_field_wf_rec A refs) :
    T = U :=
  injTyNoNone T U A
    (noNoneTy_of_wf A (by simpa [smtx_type_field_wf_rec] using hWF)) hT hU

theorem noNoneTy_of_type_wf
    (A : SmtType)
    (hWF : __smtx_type_wf A = true) :
    noNoneTy A = true := by
  by_cases hReg : A = SmtType.RegLan
  · subst A
    simp [noNoneTy]
  · by_cases hFun : ∃ X Y, A = SmtType.FunType X Y
    · rcases hFun with ⟨X, Y, rfl⟩
      have hComponents :
          __smtx_type_wf_component X = true ∧
            __smtx_type_wf Y = true := by
        simpa [__smtx_type_wf, native_and] using hWF
      have hX : __smtx_type_wf_rec X = true := by
        have hp : native_inhabited_type X = true ∧ __smtx_type_wf_rec X = true := by
          simpa [__smtx_type_wf_component, native_and] using hComponents.1
        exact hp.2
      simp [noNoneTy, noNoneTy_of_wf X hX,
        noNoneTy_of_type_wf Y hComponents.2, native_and]
    ·
      have hRec : __smtx_type_wf_rec A = true := by
        have hComponent : __smtx_type_wf_component A = true := by
          cases A <;>
            simp [__smtx_type_wf] at hWF hReg hFun ⊢
          all_goals first | contradiction | exact hWF
        have hp : native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true := by
          simpa [__smtx_type_wf_component, native_and] using hComponent
        exact hp.2
      exact noNoneTy_of_wf A hRec
termination_by A

/-- EO type translation is injective under the public top-level SMT
well-formedness predicate. -/
theorem eo_to_smt_type_injective_of_wf
    {T U : Term} {A : SmtType}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : __smtx_type_wf A = true) :
    T = U :=
  injTyNoNone T U A (noNoneTy_of_type_wf A hWF) hT hU

/-- Recovers the translated EO type from an SMT typing equality using an explicit IH. -/
theorem eo_to_smt_type_typeof_of_smt_type_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  have hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [h]
    exact hT
  exact (ih hNN).symm.trans h

/-- Recovers the exact EO type from an SMT typing equality and field well-formedness. -/
theorem eo_typeof_eq_of_smt_type_from_ih_field_wf
    (t U : Term) {T : SmtType} {refs : RefList}
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hU : __eo_to_smt_type U = T)
    (hWF : smtx_type_field_wf_rec T refs) :
    __eo_typeof t = U := by
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    cases T <;> simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWF hNone
  have hType :=
    eo_to_smt_type_typeof_of_smt_type_from_ih t ih h hTNN
  exact eo_to_smt_type_injective_of_field_wf_rec hType hU hWF

/-- An explicit IH plus SMT `Bool` typing recovers EO `Bool`. -/
theorem eo_typeof_eq_bool_of_smt_bool_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    __eo_typeof t = Term.Bool := by
  exact eo_to_smt_type_eq_bool
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT `Int` typing recovers EO `Int`. -/
theorem eo_typeof_eq_int_of_smt_int_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  exact eo_to_smt_type_eq_int
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT `Real` typing recovers EO `Real`. -/
theorem eo_typeof_eq_real_of_smt_real_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __eo_typeof t = Term.UOp UserOp.Real := by
  exact eo_to_smt_type_eq_real
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT regular-language typing recovers EO `RegLan`. -/
theorem eo_typeof_eq_reglan_of_smt_reglan_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.RegLan) :
    __eo_typeof t = Term.UOp UserOp.RegLan := by
  exact eo_to_smt_type_eq_reglan
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT `Seq Char` typing recovers EO string type. -/
theorem eo_typeof_eq_seq_char_of_smt_seq_char_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  exact eo_to_smt_type_eq_seq_char
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT sequence typing recovers the EO sequence shape. -/
theorem eo_typeof_eq_seq_of_smt_seq_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ U, __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U ∧ __eo_to_smt_type U = T := by
  exact eo_to_smt_type_eq_seq
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT set typing recovers the EO set shape. -/
theorem eo_typeof_eq_set_of_smt_set_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Set T) :
    ∃ U, __eo_typeof t = Term.Apply (Term.UOp UserOp.Set) U ∧ __eo_to_smt_type U = T := by
  exact eo_to_smt_type_eq_set
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT bitvector typing recovers EO `BitVec`. -/
theorem eo_typeof_eq_bitvec_of_smt_bitvec_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (w : native_Nat)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) := by
  exact eo_to_smt_type_eq_bitvec
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

end TranslationProofs
