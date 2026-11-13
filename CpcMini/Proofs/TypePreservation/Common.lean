module

public import CpcMini.Proofs.TypePreservation.CanonicalAssumptions
import all CpcMini.Proofs.TypePreservation.CanonicalAssumptions
public import CpcMini.Proofs.TypePreservation.Predicates
import all CpcMini.Proofs.TypePreservation.Predicates
public import CpcMini.Proofs.Canonical.TypeDefaultBasic
import all CpcMini.Proofs.Canonical.TypeDefaultBasic

public section

variable {uc : SmtUSortDom}

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

@[simp] theorem native_char_valid_zero :
    native_char_valid 0 = true := by
  native_decide

@[simp] theorem native_re_canonical_none :
    __smtx_re_canonical native_re_none = true := by
  native_decide

/-- The two facts the inhabitation check supplies on a recursively well-formed
type: the type is not `None`, and the default value has that type. Canonicity
additionally follows via `type_default_canonical_of_inhabited_wf_rec`. -/
theorem native_inhabited_type_parts {T : SmtType} (h : __smtx_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    T ≠ SmtType.None ∧ __smtx_typeof_value (__smtx_type_default T) = T :=
  ⟨native_inhabited_type_ne_none h, type_default_typed T h hRec⟩

/-- Extracts semantic inhabitation from the generated Boolean inhabitation check. -/
theorem type_inhabited_of_native_inhabited_type
    (T : SmtType)
    (h : __smtx_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    type_inhabited T :=
  ⟨__smtx_type_default T, type_default_typed T h hRec⟩

/-- On a recursively well-formed inhabited type, the default is a typed, canonical witness. -/
theorem type_default_typed_canonical_of_native_inhabited_type (huc : usort_dom_wf uc)
    (T : SmtType)
    (h : __smtx_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      value_canonical uc (__smtx_type_default T) := by
  refine ⟨type_default_typed T h hRec, ?_⟩
  simpa [value_canonical] using
    type_default_canonical_of_inhabited_wf_rec huc T h hRec

/-- Computes the well-formedness/inhabitation guard from a non-`None` result. -/
theorem smtx_typeof_guard_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_typeof_guard_wf T U = U := by
  intro h
  unfold __smtx_typeof_guard_wf at h ⊢
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

theorem smtx_type_wf_component_parts
    {T : SmtType}
    (h : __smtx_type_wf_component T = true) :
    __smtx_inhabited_type T = true ∧
      __smtx_type_wf_rec T = true := by
  simpa [__smtx_type_wf_component, native_and] using h

theorem smtx_type_wf_component_of_parts
    {T : SmtType}
    (hInh : __smtx_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_type_wf_component T = true := by
  simp [__smtx_type_wf_component, native_and, hInh, hRec]

/-- Extracts the domain component facts and recursive codomain well-formedness
from a well-formed function type. -/
theorem fun_type_wf_parts
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_inhabited_type A = true ∧
      __smtx_type_wf_rec A = true ∧
        __smtx_type_wf B = true := by
  have hAll :
      (__smtx_inhabited_type A = true ∧
        __smtx_type_wf_rec A = true) ∧
          __smtx_type_wf B = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, native_and] using h
  exact ⟨hAll.1.1, hAll.1.2, hAll.2⟩

theorem smtx_typeof_guard_wf_inhabited_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    type_inhabited T := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      exact ⟨SmtValue.Fun native_default_fun_id A B, by
        simp [__smtx_typeof_value]⟩
    · have hPair :
        __smtx_inhabited_type T = true ∧
          __smtx_type_wf_rec T = true := by
        cases T <;>
          simp [__smtx_type_wf, __smtx_type_wf_component, native_and] at hWf hReg hFun ⊢
        all_goals first | contradiction | exact hWf.1 | assumption
      exact type_inhabited_of_native_inhabited_type T hPair.1 hPair.2

/-- Extracts well-formedness of the guarded source type from a non-`None` guarded type. -/
theorem smtx_typeof_guard_wf_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_type_wf T = true := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Any well-formed SMT type is different from `None`. -/
theorem type_wf_non_none
    {T : SmtType}
    (h : __smtx_type_wf T = true) :
    T ≠ SmtType.None := by
  intro hNone
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, hNone] at h

/-- Recursive well-formedness rejects `RegLan` at nested positions. -/
theorem type_wf_rec_ne_reglan
    {U : SmtType}
    (h : __smtx_type_wf_rec U = true) :
    U ≠ SmtType.RegLan := by
  intro hReg
  subst hReg
  simp [__smtx_type_wf_rec] at h

/-- Rebuilds public well-formedness from recursive well-formedness plus inhabitation. -/
theorem type_wf_of_inhabited_and_wf_rec
    {T : SmtType}
    (hInh : __smtx_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_type_wf T = true := by
  have hComp : __smtx_type_wf_component T = true := by
    simp [__smtx_type_wf_component, native_and, hInh, hRec]
  cases T
  case RegLan => simp [__smtx_type_wf]
  case FunType A B =>
    exfalso
    simp [__smtx_type_wf_rec] at hRec
  all_goals exact hComp

/-- Every well-formed SMT type is semantically inhabited. -/
theorem type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    type_inhabited T := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      exact ⟨SmtValue.Fun native_default_fun_id A B, rfl⟩
    · have hPair :
          __smtx_inhabited_type T = true ∧ __smtx_type_wf_rec T = true := by
        cases T <;>
          simp [__smtx_type_wf, __smtx_type_wf_component, native_and] at hWF hReg hFun ⊢
        all_goals first | contradiction | exact hWF
      exact type_inhabited_of_native_inhabited_type T hPair.1 hPair.2

/-- Extracts well-formedness of the element type of a well-formed sequence type. -/
theorem seq_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    __smtx_type_wf A = true := by
  have hAll :
      __smtx_inhabited_type (SmtType.Seq A) = true ∧
        (__smtx_inhabited_type A = true ∧
          __smtx_type_wf_rec A = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact type_wf_of_inhabited_and_wf_rec hAll.2.1 hAll.2.2

/-- Extracts well-formedness of the element type of a well-formed set type. -/
theorem set_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_type_wf A = true := by
  have hAll :
      __smtx_inhabited_type (SmtType.Set A) = true ∧
        (__smtx_inhabited_type A = true ∧
          __smtx_type_wf_rec A = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact type_wf_of_inhabited_and_wf_rec hAll.2.1 hAll.2.2

/-- Extracts well-formedness of the domain and codomain of a well-formed map type. -/
theorem map_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  have hAll :
      __smtx_inhabited_type (SmtType.Map A B) = true ∧
        ((__smtx_inhabited_type A = true ∧
          __smtx_type_wf_rec A = true) ∧
          (__smtx_inhabited_type B = true ∧
            __smtx_type_wf_rec B = true)) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      native_and] using h
  exact ⟨type_wf_of_inhabited_and_wf_rec hAll.2.1.1 hAll.2.1.2,
    type_wf_of_inhabited_and_wf_rec hAll.2.2.1 hAll.2.2.2⟩

/-- Extracts well-formedness of the domain and codomain of a well-formed function type. -/
theorem fun_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  have hAll :
      (__smtx_inhabited_type A = true ∧
        __smtx_type_wf_rec A = true) ∧
        __smtx_type_wf B = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, native_and] using h
  exact ⟨type_wf_of_inhabited_and_wf_rec hAll.1.1 hAll.1.2,
    hAll.2⟩

theorem fun_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf_rec A = true ∧
      __smtx_type_wf B = true := by
  exact ⟨(fun_type_wf_parts h).2.1, (fun_type_wf_parts h).2.2⟩

theorem fun_type_domain_ne_reglan_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    A ≠ SmtType.RegLan :=
  type_wf_rec_ne_reglan (fun_type_wf_rec_components_of_wf h).1

/-- A well-formed sequence type has a non-`None` element type. -/
theorem seq_type_component_non_none_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    A ≠ SmtType.None :=
  type_wf_non_none (seq_type_wf_component_of_wf h)

/-- A well-formed set type has a non-`None` element type. -/
theorem set_type_component_non_none_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    A ≠ SmtType.None :=
  type_wf_non_none (set_type_wf_component_of_wf h)

/-- A well-formed map type has non-`None` domain and codomain types. -/
theorem map_type_components_non_none_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rcases map_type_wf_components_of_wf h with ⟨hA, hB⟩
  exact ⟨type_wf_non_none hA, type_wf_non_none hB⟩

/-- A well-formed function type has non-`None` domain and codomain types. -/
theorem fun_type_components_non_none_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rcases fun_type_wf_components_of_wf h with ⟨hA, hB⟩
  exact ⟨type_wf_non_none hA, type_wf_non_none hB⟩

/-- A self-guarded sequence type equal to `Seq A` has a non-`None` element type. -/
theorem smtx_typeof_guard_wf_self_eq_seq_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.Seq A) :
    A ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.Seq A := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact seq_type_component_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq A) (SmtType.Seq A) hNN)

/-- A self-guarded set type equal to `Set A` has a non-`None` element type. -/
theorem smtx_typeof_guard_wf_self_eq_set_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.Set A) :
    A ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.Set A := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact set_type_component_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set A) (SmtType.Set A) hNN)

/-- A self-guarded map type equal to `Map A B` has non-`None` components. -/
theorem smtx_typeof_guard_wf_self_eq_map_components_non_none
    {T A B : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.Map A B := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact map_type_components_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Map A B) (SmtType.Map A B) hNN)

/-- A self-guarded function type equal to `FunType A B` has non-`None` components. -/
theorem smtx_typeof_guard_wf_self_eq_fun_components_non_none
    {T A B : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.FunType A B := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact fun_type_components_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.FunType A B) (SmtType.FunType A B) hNN)

/-- Predicate asserting that an SMT term does not have type `None`. -/
def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

/-- Predicate asserting that the SMT type of a term is inhabited. -/
def term_has_inhabited_type (t : SmtTerm) : Prop :=
  type_inhabited (__smtx_typeof t)

/-- Predicate asserting that application typing is computed by `__smtx_typeof_apply` for a pair of terms. -/
def generic_apply_type (f x : SmtTerm) : Prop :=
  __smtx_typeof (SmtTerm.Apply f x) =
    __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x)

/-- Predicate asserting that application evaluation is computed by `__smtx_model_eval_apply` for a pair of terms. -/
def generic_apply_eval (f x : SmtTerm) : Prop :=
  ∀ M,
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x)

/-- Predicate asserting that a model returns a correctly typed value for well-formed types,
or `NotValue` for non-well-formed types, at a given symbol and type. -/
def model_typed_at (M : SmtModel) (s : native_String) (T : SmtType) : Prop :=
  (__smtx_type_wf T = true -> __smtx_typeof_value (native_model_var_lookup M s T) = T) ∧
  (__smtx_type_wf T = false -> native_model_var_lookup M s T = SmtValue.NotValue)

/-- Shows that the SMT type `bool` is inhabited. -/
theorem type_inhabited_bool : type_inhabited SmtType.Bool :=
  ⟨SmtValue.Boolean true, rfl⟩

/-- Shows that the SMT type `int` is inhabited. -/
theorem type_inhabited_int : type_inhabited SmtType.Int :=
  ⟨SmtValue.Numeral 0, rfl⟩

/-- Shows that the SMT type `real` is inhabited. -/
theorem type_inhabited_real : type_inhabited SmtType.Real :=
  ⟨SmtValue.Real (native_mk_real 0 1), rfl⟩

/-- Shows that the SMT type `reglan` is inhabited. -/
theorem type_inhabited_reglan : type_inhabited SmtType.RegLan :=
  ⟨SmtValue.RegLan native_re_none, rfl⟩

/-- Shows that the SMT type `char` is inhabited. -/
theorem type_inhabited_char : type_inhabited SmtType.Char :=
  ⟨SmtValue.Char 0, rfl⟩

/-- Shows that every uninterpreted sort is inhabited. -/
theorem type_inhabited_usort (i : native_Nat) : type_inhabited (SmtType.USort i) :=
  ⟨SmtValue.UValue i 0, rfl⟩

/-- Shows that the SMT type `seq` is inhabited. -/
theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

/-- Shows that the SMT type `map` is inhabited. -/
theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

/-- Maps have a generated default witness when their codomain does. -/
theorem native_inhabited_type_map
    {A B : SmtType}
    (hB : __smtx_inhabited_type B = true) :
    __smtx_inhabited_type (SmtType.Map A B) = true := by
  simpa [__smtx_inhabited_type] using hB

/-- Builds well-formedness for the fallback map used by sequence nth defaults. -/
theorem seq_nth_wrong_map_type_wf
    {T : SmtType}
    (hTInh : __smtx_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T = true) :
    __smtx_type_wf
      (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)) = true := by
  have hIntInh : __smtx_inhabited_type SmtType.Int = true := by
    simp [__smtx_inhabited_type]
  have hSeqInh : __smtx_inhabited_type (SmtType.Seq T) = true := by
    simp [__smtx_inhabited_type]
  have hMapInh : __smtx_inhabited_type (SmtType.Map SmtType.Int T) = true := by
    exact native_inhabited_type_map hTInh
  have hOuterInh :
      __smtx_inhabited_type
        (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)) = true :=
    by
      exact native_inhabited_type_map hMapInh
  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    native_and, hTInh, hRec, hIntInh, hSeqInh,
    hMapInh, hOuterInh]

/-- Shows that the SMT type `fun` is inhabited. -/
theorem type_inhabited_fun (A B : SmtType) :
    type_inhabited (SmtType.FunType A B) :=
  ⟨SmtValue.Fun native_default_fun_id A B, rfl⟩

/-- Shows that the SMT type `set` is inhabited. -/
theorem type_inhabited_set (A : SmtType) : type_inhabited (SmtType.Set A) :=
  ⟨SmtValue.Set (SmtMap.default A (SmtValue.Boolean false)), by
    simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type]⟩

/-- The generated Boolean inhabitation check accepts `bool`. -/
@[simp] theorem native_inhabited_type_bool :
    __smtx_inhabited_type SmtType.Bool = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts `int`. -/
@[simp] theorem native_inhabited_type_int :
    __smtx_inhabited_type SmtType.Int = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts `real`. -/
@[simp] theorem native_inhabited_type_real :
    __smtx_inhabited_type SmtType.Real = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts regular languages. -/
@[simp] theorem native_inhabited_type_reglan :
    __smtx_inhabited_type SmtType.RegLan = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts characters. -/
@[simp] theorem native_inhabited_type_char :
    __smtx_inhabited_type SmtType.Char = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts uninterpreted sorts. -/
@[simp] theorem native_inhabited_type_usort (i : native_Nat) :
    __smtx_inhabited_type (SmtType.USort i) = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts sequences. -/
@[simp] theorem native_inhabited_type_seq (T : SmtType) :
    __smtx_inhabited_type (SmtType.Seq T) = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts sets. -/
@[simp] theorem native_inhabited_type_set (A : SmtType) :
    __smtx_inhabited_type (SmtType.Set A) = true := by
  simp [__smtx_inhabited_type]

/-- The generated Boolean inhabitation check accepts function types. -/
@[simp] theorem native_inhabited_type_fun (A B : SmtType) :
    __smtx_inhabited_type (SmtType.FunType A B) = true := by
  simp [__smtx_inhabited_type]

end Smtm
