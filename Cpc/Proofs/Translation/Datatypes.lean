module

public import Cpc.Proofs.Translation.Base
import all Cpc.Spec
import all Cpc.Logos

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Computes `__eo_typeof` for `tuple_unit`. -/
@[simp] theorem eo_typeof_tuple_unit :
    __eo_typeof (Term.UOp UserOp.tuple_unit) = (Term.UOp UserOp.UnitTuple) := by
  native_decide

/-- Simplifies EO-to-SMT translation for `term_tuple_unit`. -/
@[simp] theorem eo_to_smt_term_tuple_unit :
    __eo_to_smt (Term.UOp UserOp.tuple_unit) =
      SmtTerm.DtCons (native_string_lit "@Tuple")
        (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) SmtDatatypeDecl.nil) 0 := rfl

/-- Simplifies EO-to-SMT translation for `term_dt_cons`. -/
@[simp] theorem eo_to_smt_term_dt_cons
    (s : native_String) (d : DatatypeDecl) (i : native_Nat) :
    __eo_to_smt (Term.DtCons s d i) =
      native_ite (__eo_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype_decl d) i) := rfl

/-- Simplifies EO-to-SMT translation for `term_dt_sel`. -/
@[simp] theorem eo_to_smt_term_dt_sel
    (s : native_String) (d : DatatypeDecl) (i j : native_Nat) :
    __eo_to_smt (Term.DtSel s d i j) =
      native_ite (__eo_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtSel s (__eo_to_smt_datatype_decl d) i j) := rfl

/-- Simplifies EO-to-SMT translation for `datatype_cons_unit`. -/
@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

/-- Simplifies EO-to-SMT translation for `datatype_null`. -/
@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

/-- Simplifies EO-to-SMT translation for `datatype_decl_nil`. -/
@[simp] theorem eo_to_smt_datatype_decl_nil :
    __eo_to_smt_datatype_decl DatatypeDecl.nil = SmtDatatypeDecl.nil := rfl

/-- Simplifies EO-to-SMT type translation for `datatype`. -/
@[simp] theorem eo_to_smt_type_datatype (s : native_String) (d : DatatypeDecl) :
    __eo_to_smt_type (Term.DatatypeType s d) =
      native_ite (__eo_reserved_datatype_name s) SmtType.None
        (SmtType.Datatype s (__eo_to_smt_datatype_decl d)) := by
  rfl

/-- Simplifies EO-to-SMT type translation for `unit_tuple`. -/
@[simp] theorem eo_to_smt_type_unit_tuple :
    __eo_to_smt_type (Term.UOp UserOp.UnitTuple) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) SmtDatatypeDecl.nil) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `tuple_step`. -/
@[simp] theorem eo_to_smt_type_tuple_step (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U) =
      native_ite (__smtx_type_wf (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)))
        (__eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U)) SmtType.None := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT translation for `tester_of_dtcons`. -/
@[simp] theorem eo_to_smt_tester_of_dtcons
    (s : native_String) (d : SmtDatatypeDecl) (n : native_Nat) :
    __eo_to_smt_tester (SmtTerm.DtCons s d n) = SmtTerm.DtTester s d n := rfl

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_none :
    __smtx_typeof SmtTerm.None = SmtType.None := by
  unfold __smtx_typeof
  rfl

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : native_String) (d : SmtDatatypeDecl) (i j : native_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
  unfold __smtx_typeof
  rfl

/-- Computes `__smtx_typeof` for `dt_tester_head_none`. -/
@[simp] theorem smtx_typeof_dt_tester_head_none
    (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    __smtx_typeof (SmtTerm.DtTester s d i) = SmtType.None := by
  unfold __smtx_typeof
  rfl

/-- Computes `__smtx_typeof` for `eo_to_smt_tester_none`. -/
@[simp] theorem smtx_typeof_eo_to_smt_tester_none
    (t : SmtTerm) :
    __smtx_typeof (__eo_to_smt_tester t) = SmtType.None := by
  cases t <;> simp [__eo_to_smt_tester]

/-- Selector return-type computation commutes with EO-to-SMT datatype translation. -/
theorem eo_to_smt_typeof_dt_sel_return :
    (d : Datatype) -> (i j : native_Nat) ->
      __eo_to_smt_type (__eo_typeof_dt_sel_return d i j) =
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j
  | Datatype.null, i, j => by
      cases i <;> cases j <;>
        simp [__eo_typeof_dt_sel_return, __eo_to_smt_type, __eo_to_smt_datatype,
          __smtx_ret_typeof_sel_rec]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, j => by
      cases j <;>
        simp [__eo_typeof_dt_sel_return, __eo_to_smt_type, __eo_to_smt_datatype,
          __eo_to_smt_datatype_cons, __smtx_ret_typeof_sel_rec]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      simp [__eo_typeof_dt_sel_return, __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
        __smtx_ret_typeof_sel_rec]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      simpa [__eo_typeof_dt_sel_return, __eo_to_smt_datatype, __eo_to_smt_datatype_cons,
        __smtx_ret_typeof_sel_rec] using
        eo_to_smt_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero j
  | Datatype.sum c d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __eo_to_smt_datatype,
        __smtx_ret_typeof_sel_rec] using eo_to_smt_typeof_dt_sel_return d i j

/-- Computes `__smtx_typeof` for `tuple_unit_translation`. -/
theorem smtx_typeof_tuple_unit_translation :
    __smtx_typeof
        (SmtTerm.DtCons (native_string_lit "@Tuple")
          (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
            (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) SmtDatatypeDecl.nil) 0) =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatypeDecl.cons (native_string_lit "@Tuple")
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) SmtDatatypeDecl.nil) := by
  native_decide

end TranslationProofs
