module

public import CpcMini.Proofs.Translation.Base
import all CpcMini.Proofs.Translation.Base

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `term_dt_cons`. -/
@[simp] theorem eo_to_smt_term_dt_cons
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.DtCons s d i) =
      native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) := by
  rfl

/-- Simplifies EO-to-SMT translation for `term_dt_sel`. -/
@[simp] theorem eo_to_smt_term_dt_sel
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.DtSel s d i j) =
      native_ite (__eo_to_smt_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) := by
  rfl

/-- Simplifies EO-to-SMT translation for `datatype_cons_unit`. -/
@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

/-- Simplifies EO-to-SMT translation for `datatype_null`. -/
@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

/-- Simplifies EO-to-SMT type translation for `datatype`. -/
@[simp] theorem eo_to_smt_type_datatype (s : native_String) (d : DatatypeDecl) :
    __eo_to_smt_type (Term.DatatypeType s d) =
      native_ite (__eo_to_smt_reserved_datatype_name s) SmtType.None
        (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) := by
  rfl

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
  simp [__smtx_typeof.eq_def]

/-! ### Datatype-declaration lookup -/

/-- Declaration lookup commutes with EO-to-SMT translation. -/
theorem eo_to_smt_datatype_decl_lookup
    : ∀ (s : native_String) (dd : DatatypeDecl),
      __eo_to_smt_datatype (__eo_dd_lookup s dd) =
        __smtx_dd_lookup s (__eo_to_smt_datatype_decl dd)
  | _, DatatypeDecl.nil => rfl
  | s, DatatypeDecl.cons s' d dd => by
      cases hEq : native_streq s s' <;>
        simp [__eo_dd_lookup, __smtx_dd_lookup, __eo_to_smt_datatype_decl,
          native_ite, hEq, eo_to_smt_datatype_decl_lookup s dd]
termination_by _ dd => sizeOf dd

/-- Selector-result lookup commutes with translation. -/
theorem eo_to_smt_type_typeof_dt_sel_return
    : ∀ (d : Datatype) (i j : native_Nat),
      __eo_to_smt_type (__eo_typeof_dt_sel_return d i j) =
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j
  | Datatype.null, _, _ => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_type]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, j => by
      cases j <;>
        simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
          __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __eo_to_smt_type]
  | Datatype.sum DatatypeCons.unit d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return d i j
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero j
  | Datatype.sum c d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype] using
        eo_to_smt_type_typeof_dt_sel_return d i j
termination_by d _ _ => sizeOf d

end TranslationProofs
