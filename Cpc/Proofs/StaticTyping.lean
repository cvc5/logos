module

public import Cpc.SmtModel
import all Cpc.SmtModel

public section

open SmtEval

set_option linter.unusedSimpArgs false

namespace Smtm

/-- The static information retained from a semantic default. In particular,
a malformed constructed value of type `None` is different from `NotValue`. -/
def semantic_default_info : SmtValue -> Option SmtType
  | SmtValue.NotValue => none
  | v => some (__smtx_typeof_value v)

@[simp] theorem semantic_default_info_none (v : SmtValue) :
    semantic_default_info v = none ↔ v = SmtValue.NotValue := by
  cases v <;> simp [semantic_default_info]

@[simp] theorem semantic_default_info_type (v : SmtValue) :
    __smtx_default_info_type (semantic_default_info v) = __smtx_typeof_value v := by
  cases v <;> rfl

@[simp] theorem semantic_default_info_apply (v w : SmtValue) :
    semantic_default_info (SmtValue.Apply v w) =
      some (__smtx_typeof_apply_value (__smtx_typeof_value v) (__smtx_typeof_value w)) := by
  rfl

/-- The executable abstraction agrees with the semantic generator on every
type, including malformed declarations. No arithmetic value is inspected. -/
theorem default_info_agrees : ∀ T : SmtType,
    __smtx_default_info T = semantic_default_info (__smtx_type_default T) := by
  refine __smtx_type_default.induct
    (motive1 := fun T =>
      __smtx_default_info T = semantic_default_info (__smtx_type_default T))
    (motive2 := fun s dd ddF =>
      __smtx_datatype_decl_default_info s dd ddF =
        semantic_default_info (__smtx_datatype_decl_default s dd ddF))
    (motive3 := fun s dd n dF ddF =>
      __smtx_datatype_default_info s dd n dF ddF =
        semantic_default_info (__smtx_datatype_default s dd n dF ddF))
    (motive4 := fun v dd c ddF =>
      __smtx_datatype_cons_default_info (semantic_default_info v) dd c ddF =
        semantic_default_info (__smtx_datatype_cons_default v dd c ddF))
    (motive5 := fun dd T ddF =>
      __smtx_field_default_info dd T ddF =
        semantic_default_info (__smtx_field_type_default dd T ddF))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    intros
    simp_all [__smtx_default_info, __smtx_type_default,
      __smtx_datatype_decl_default_info, __smtx_datatype_decl_default,
      __smtx_datatype_default_info, __smtx_datatype_default,
      __smtx_datatype_cons_default_info, __smtx_datatype_cons_default,
      __smtx_field_default_info, __smtx_field_type_default,
      semantic_default_info, __smtx_typeof_value, __smtx_typeof_map_value,
      __smtx_typeof_seq_value, __smtx_map_to_set_type,
      native_ite, native_veq, native_not, native_and, native_Teq,
      native_nat_to_int, native_zleq, native_zeq, native_mod_total,
      native_int_to_nat, native_char_valid]
  case refine_6 =>
    rename_i T U ih
    cases h : __smtx_type_default U <;>
      simp_all [__smtx_typeof_value, __smtx_typeof_map_value, native_ite, native_Teq]
  case refine_14 =>
    split <;> simp_all
  case refine_16 =>
    rename_i s dd n c d ddF ihCons ihTail
    cases h : __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd c ddF <;>
      simp_all
  case refine_19 =>
    rename_i v dd T c ddF v0 ihField ihRest
    have hv := semantic_default_info_type v
    simp only [semantic_default_info] at hv
    rw [hv]
    dsimp only [v0] at ihRest
    cases h : __smtx_field_type_default dd T ddF <;>
      simp_all [__smtx_default_info_type, __smtx_typeof_value]

@[simp] theorem default_info_type_agrees (T : SmtType) :
    __smtx_default_info_type (__smtx_default_info T) =
      __smtx_typeof_value (__smtx_type_default T) := by
  rw [default_info_agrees, semantic_default_info_type]

/-- Compatibility with the previous value-based inhabitation definition. -/
theorem native_inhabited_type_eq (T : SmtType) :
    native_inhabited_type T =
      native_and (native_not (native_Teq T SmtType.None))
        (native_Teq (__smtx_typeof_value (__smtx_type_default T)) T) := by
  simp only [native_inhabited_type, default_info_type_agrees]

end Smtm
