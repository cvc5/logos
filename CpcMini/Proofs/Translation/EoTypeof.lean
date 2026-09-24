module

public import CpcMini.Proofs.Translation.Datatypes
import all CpcMini.Proofs.Translation.Datatypes

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

attribute [local simp] native_ite
attribute [local simp] Smtm.__smtx_type_wf_component

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

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- The finite/infinite EO function-type lowering never produces `None`. -/
@[simp] private theorem smt_fun_choice_ne_none
    (T U : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.None := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces an SMT type reference. -/
@[simp] private theorem smt_fun_choice_ne_typeref
    (T U : SmtType) (s : native_String) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.TypeRef s := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces an SMT datatype. -/
@[simp] private theorem smt_fun_choice_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatypeDecl) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.Datatype s d := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces a constructor application type. -/
@[simp] private theorem smt_fun_choice_ne_dtc_app
    (T U A B : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.DtcAppType A B := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces a sequence type. -/
@[simp] private theorem smt_fun_choice_ne_seq
    (T U A : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.Seq A := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces `Bool`. -/
@[simp] private theorem smt_fun_choice_ne_bool
    (T U : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.Bool := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces `Int`. -/
@[simp] private theorem smt_fun_choice_ne_int
    (T U : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.Int := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces `Real`. -/
@[simp] private theorem smt_fun_choice_ne_real
    (T U : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.Real := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces `Char`. -/
@[simp] private theorem smt_fun_choice_ne_char
    (T U : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.Char := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces a universe sort. -/
@[simp] private theorem smt_fun_choice_ne_usort
    (T U : SmtType) (i : native_Nat) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.USort i := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces a bit-vector type. -/
@[simp] private theorem smt_fun_choice_ne_bitvec
    (T U : SmtType) (w : native_Nat) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.BitVec w := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

/-- The finite/infinite EO function-type lowering never produces a regular-language type. -/
@[simp] private theorem smt_fun_choice_ne_reglan
    (T U : SmtType) :
    native_ite (__smtx_is_finite_type (SmtType.FunType T U))
      (SmtType.FunType T U) (SmtType.FunType T U) ≠ SmtType.RegLan := by
  cases __smtx_is_finite_type (SmtType.FunType T U) <;> simp [native_ite]

@[simp] private theorem smt_fun_choice_if_ne_none
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.None := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_typeref
    (T U : SmtType) (s : native_String) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.TypeRef s := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatypeDecl) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.Datatype s d := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_dtc_app
    (T U A B : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.DtcAppType A B := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_seq
    (T U A : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.Seq A := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_bool
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.Bool := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_int
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.Int := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_real
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.Real := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_char
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.Char := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_usort
    (T U : SmtType) (i : native_Nat) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.USort i := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_bitvec
    (T U : SmtType) (w : native_Nat) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.BitVec w := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_reglan
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then
        SmtType.FunType T U
      else
        SmtType.FunType T U) ≠ SmtType.RegLan := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

/-- A translated sequence type is never an SMT type reference. -/
theorem smtx_typeof_guard_seq_ne_typeref
    (T : SmtType) (s : native_String) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.TypeRef s := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT datatype. -/
theorem smtx_typeof_guard_seq_ne_datatype
    (T : SmtType) (s : native_String) (d : SmtDatatypeDecl) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.Datatype s d := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT type reference. -/
theorem smtx_typeof_guard_fun_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T
        (__smtx_typeof_guard U
          (native_ite (__smtx_is_finite_type (SmtType.FunType T U))
            (SmtType.FunType T U) (SmtType.FunType T U))) ≠ SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT datatype. -/
theorem smtx_typeof_guard_fun_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatypeDecl) :
    __smtx_typeof_guard T
        (__smtx_typeof_guard U
          (native_ite (__smtx_is_finite_type (SmtType.FunType T U))
            (SmtType.FunType T U) (SmtType.FunType T U))) ≠ SmtType.Datatype s d := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT type reference. -/
theorem smtx_typeof_guard_dtc_app_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT datatype. -/
theorem smtx_typeof_guard_dtc_app_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatypeDecl) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.Datatype s d := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT function type. -/
theorem smtx_typeof_guard_dtc_app_ne_fun
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.FunType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT constructor-application type. -/
theorem smtx_typeof_guard_fun_ne_dtc_app
    (T U A B : SmtType) :
    __smtx_typeof_guard T
        (__smtx_typeof_guard U
          (native_ite (__smtx_is_finite_type (SmtType.FunType T U))
            (SmtType.FunType T U) (SmtType.FunType T U))) ≠ SmtType.DtcAppType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT constructor-application type. -/
theorem smtx_typeof_guard_seq_ne_dtc_app
    (T A B : SmtType) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.DtcAppType A B := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- An EO application never translates to an SMT type reference. -/
theorem eo_to_smt_type_apply_ne_typeref
    (f x : Term) (s : native_String) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s := by
  cases f with
  | UOp op =>
      cases op with
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true
              · simp [__eo_to_smt_type, native_ite, hz]
              · simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          simpa [__eo_to_smt_type] using
            smtx_typeof_guard_seq_ne_typeref (__eo_to_smt_type x) s
      | _ =>
          simp [__eo_to_smt_type]
  | Apply f1 x1 =>
      cases f1 <;> try simp [__eo_to_smt_type]
      case FunType =>
        simpa [__eo_to_smt_type] using
          smtx_typeof_guard_fun_ne_typeref (__eo_to_smt_type x1) (__eo_to_smt_type x) s
  | _ =>
      simp [__eo_to_smt_type]

/-- An EO application never translates to an SMT datatype. -/
theorem eo_to_smt_type_apply_ne_datatype
    (f x : Term) (s : native_String) (d : SmtDatatypeDecl) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.Datatype s d := by
  cases f with
  | UOp op =>
      cases op with
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true
              · simp [__eo_to_smt_type, native_ite, hz]
              · simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          simpa [__eo_to_smt_type] using
            smtx_typeof_guard_seq_ne_datatype (__eo_to_smt_type x) s d
      | _ =>
          simp [__eo_to_smt_type]
  | Apply f1 x1 =>
      cases f1 <;> try simp [__eo_to_smt_type]
      case FunType =>
        simpa [__eo_to_smt_type] using
          smtx_typeof_guard_fun_ne_datatype (__eo_to_smt_type x1) (__eo_to_smt_type x) s d
  | _ =>
      simp [__eo_to_smt_type]

/-- A translated EO datatype-constructor application type is never an SMT datatype. -/
theorem eo_to_smt_type_dtc_app_ne_datatype
    (T U : Term) (s : native_String) (d : SmtDatatypeDecl) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Datatype s d := by
  simpa [__eo_to_smt_type] using
    smtx_typeof_guard_dtc_app_ne_datatype (__eo_to_smt_type T) (__eo_to_smt_type U) s d

/-- Characterizes `__smtx_typeof_guard` producing a function type. -/
private theorem smtx_typeof_guard_eq_fun_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.FunType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.FunType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT function type. -/
theorem eo_to_smt_type_eq_fun_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.FunType A B ↔
      ∃ T1 T2,
        T = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op with
            | BitVec =>
                cases x with
                | Numeral n =>
                    by_cases hz : native_zleq 0 n = true <;>
                      simp [__eo_to_smt_type, native_ite, hz] at h
                | _ =>
                    simp [__eo_to_smt_type] at h
            | Seq =>
                by_cases hx : __eo_to_smt_type x = SmtType.None
                · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
                · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Apply g y =>
            cases g with
            | FunType =>
                have hOuter :
                    __smtx_typeof_guard (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (native_ite
                          (__smtx_is_finite_type
                            (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
                          (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
                          (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))) =
                      SmtType.FunType A B := by
                  simpa [__eo_to_smt_type] using h
                rcases smtx_typeof_guard_eq_fun_iff.mp hOuter with ⟨hyNN, hInner⟩
                rcases smtx_typeof_guard_eq_fun_iff.mp hInner with ⟨hxNN, hFun⟩
                cases hFin :
                    __smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                  simp [native_ite, hFin] at hFun
                · rcases hFun with ⟨hA, hB⟩
                  exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
                · rcases hFun with ⟨hA, hB⟩
                  exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
            | _ =>
                simp [__eo_to_smt_type] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_fun
              (__eo_to_smt_type T1) (__eo_to_smt_type T2) A B)
            (by simpa [__eo_to_smt_type] using h))
    | UOp op =>
        cases op <;> simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [eo_to_smt_type_fun, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, native_ite, native_Teq]

private theorem smtx_typeof_guard_eq_dtc_app_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.DtcAppType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.DtcAppType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT constructor-application type. -/
theorem eo_to_smt_type_eq_dtc_app_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.DtcAppType A B ↔
      ∃ T1 T2,
        T = Term.DtcAppType T1 T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | DtcAppType T1 T2 =>
        have hOuter :
            __smtx_typeof_guard (__eo_to_smt_type T1)
              (__smtx_typeof_guard (__eo_to_smt_type T2)
                (SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2))) =
              SmtType.DtcAppType A B := by
          simpa [__eo_to_smt_type] using h
        rcases smtx_typeof_guard_eq_dtc_app_iff.mp hOuter with ⟨hT1NN, hInner⟩
        rcases smtx_typeof_guard_eq_dtc_app_iff.mp hInner with ⟨hT2NN, hDtc⟩
        injection hDtc with hA hB
        exact ⟨T1, T2, rfl, hA, hB, hT1NN, hT2NN⟩
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op with
            | BitVec =>
                cases x with
                | Numeral n =>
                    by_cases hz : native_zleq 0 n = true <;>
                      simp [__eo_to_smt_type, native_ite, hz] at h
                | _ =>
                    simp [__eo_to_smt_type] at h
            | Seq =>
                exact False.elim
                  ((smtx_typeof_guard_seq_ne_dtc_app (__eo_to_smt_type x) A B)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  ((smtx_typeof_guard_fun_ne_dtc_app
                      (__eo_to_smt_type y) (__eo_to_smt_type x) A B)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | UOp op =>
        cases op <;> simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [__eo_to_smt_type, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT datatype. -/
theorem eo_to_smt_type_eq_datatype_iff
    {T : Term} {s : native_String} {d : SmtDatatypeDecl} :
    __eo_to_smt_type T = SmtType.Datatype s d ↔
      ∃ d0,
        T = Term.DatatypeType s d0 ∧
        __eo_to_smt_reserved_datatype_name s = false ∧
        __eo_to_smt_datatype_decl d0 = d := by
  constructor
  · intro h
    cases T with
    | DatatypeType s0 d0 =>
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s0 = true
        · simp [__eo_to_smt_type, hReserved] at h
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s0 = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s0 <;> simp [hName] at hReserved ⊢
          simp [__eo_to_smt_type, hReservedFalse] at h
          rcases h with ⟨hs, hd⟩
          subst hs
          exact ⟨d0, rfl, hReservedFalse, hd⟩
    | Apply f x =>
        exact False.elim (eo_to_smt_type_apply_ne_datatype f x s d h)
    | DtcAppType T1 T2 =>
        exact False.elim (eo_to_smt_type_dtc_app_ne_datatype T1 T2 s d h)
    | UOp op =>
        cases op <;> simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨d0, rfl, hReserved, hd⟩
    simp [__eo_to_smt_type, hReserved, hd]

/-- Characterizes translated EO types equal to an SMT type reference. -/
theorem eo_to_smt_type_eq_typeref_iff
    {T : Term} {s : native_String} :
    __eo_to_smt_type T = SmtType.TypeRef s ↔
      T = Term.DatatypeTypeRef s ∧ __eo_to_smt_reserved_datatype_name s = false := by
  constructor
  · intro h
    cases T with
    | DatatypeTypeRef s0 =>
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s0 = true
        · simp [__eo_to_smt_type, hReserved] at h
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s0 = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s0 <;> simp [hName] at hReserved ⊢
          simp [__eo_to_smt_type, hReservedFalse] at h
          subst h
          exact ⟨rfl, hReservedFalse⟩
    | Apply f x =>
        exact False.elim (eo_to_smt_type_apply_ne_typeref f x s h)
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_typeref
              (__eo_to_smt_type T1) (__eo_to_smt_type T2) s)
            (by simpa [__eo_to_smt_type] using h))
    | UOp op =>
        cases op <;> simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨rfl, hReserved⟩
    simp [__eo_to_smt_type, hReserved]

/-- A translated function type is never an SMT sequence type. -/
private theorem smtx_typeof_guard_fun_ne_seq
    (T U V : SmtType) :
    __smtx_typeof_guard T
        (__smtx_typeof_guard U
          (native_ite (__smtx_is_finite_type (SmtType.FunType T U))
            (SmtType.FunType T U) (SmtType.FunType T U))) ≠ SmtType.Seq V := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT sequence type. -/
private theorem smtx_typeof_guard_dtc_app_ne_seq
    (T U V : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠ SmtType.Seq V := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT sequence type. -/
theorem eo_to_smt_type_eq_seq_iff
    {T : Term} {A : SmtType} :
    __eo_to_smt_type T = SmtType.Seq A ↔
      ∃ U,
        T = Term.Apply (Term.UOp UserOp.Seq) U ∧
        __eo_to_smt_type U = A ∧
        __eo_to_smt_type U ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op with
            | Seq =>
                by_cases hx : __eo_to_smt_type x = SmtType.None
                · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
                · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
                  exact ⟨x, rfl, h, hx⟩
            | BitVec =>
                cases x with
                | Numeral n =>
                    by_cases hz : native_zleq 0 n = true <;>
                      simp [__eo_to_smt_type, native_ite, hz] at h
                | _ =>
                    simp [__eo_to_smt_type] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  ((smtx_typeof_guard_fun_ne_seq (__eo_to_smt_type y) (__eo_to_smt_type x) A)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_seq (__eo_to_smt_type T1) (__eo_to_smt_type T2) A)
            (by simpa [__eo_to_smt_type] using h))
    | UOp op =>
        cases op <;> simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨U, rfl, hU, hUNN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hU]
    simp [__eo_to_smt_type, hU, hANN, __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to SMT `Bool`. -/
theorem eo_to_smt_type_eq_bool
    {T : Term} :
    __eo_to_smt_type T = SmtType.Bool ->
    T = Term.Bool := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hz : native_zleq 0 n = true <;>
                    simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  simp [__eo_to_smt_type]
          | Seq =>
              cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `Int`. -/
theorem eo_to_smt_type_eq_int
    {T : Term} :
    __eo_to_smt_type T = SmtType.Int ->
    T = Term.UOp UserOp.Int := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hz : native_zleq 0 n = true <;>
                    simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  simp [__eo_to_smt_type]
          | Seq =>
              cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `Real`. -/
theorem eo_to_smt_type_eq_real
    {T : Term} :
    __eo_to_smt_type T = SmtType.Real ->
    T = Term.UOp UserOp.Real := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hz : native_zleq 0 n = true <;>
                    simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  simp [__eo_to_smt_type]
          | Seq =>
              cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `Char`. -/
theorem eo_to_smt_type_eq_char
    {T : Term} :
    __eo_to_smt_type T = SmtType.Char ->
    T = Term.UOp UserOp.Char := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hz : native_zleq 0 n = true <;>
                    simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  simp [__eo_to_smt_type]
          | Seq =>
              cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `USort`. -/
theorem eo_to_smt_type_eq_usort
    {T : Term} {i : native_Nat} :
    __eo_to_smt_type T = SmtType.USort i ->
    T = Term.USort i := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hz : native_zleq 0 n = true <;>
                    simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  simp [__eo_to_smt_type]
          | Seq =>
              cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to an SMT bit-vector type. -/
theorem eo_to_smt_type_eq_bitvec_iff
    {T : Term} {w : native_Nat} :
    __eo_to_smt_type T = SmtType.BitVec w ↔
      ∃ n : native_Int,
        T = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) ∧
        native_zleq 0 n = true ∧
        native_int_to_nat n = w := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op with
            | BitVec =>
                cases x with
                | Numeral n =>
                    by_cases hz : native_zleq 0 n = true
                    · simp [__eo_to_smt_type, native_ite, hz] at h
                      exact ⟨n, rfl, hz, h⟩
                    · simp [__eo_to_smt_type, native_ite, hz] at h
                | _ =>
                    simp [__eo_to_smt_type] at h
            | Seq =>
                cases hX : __eo_to_smt_type x <;>
                  simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  (by
                    cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                      simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX] at h)
            | _ =>
                simp [__eo_to_smt_type] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        cases hT : __eo_to_smt_type T1 <;> cases hU : __eo_to_smt_type T2 <;>
          simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU] at h
    | UOp op =>
        cases op <;> simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨n, rfl, hz, hw⟩
    simp [__eo_to_smt_type, native_ite, hz, hw]

/--
Extracts the EO function-type witness carried by a translated SMT function
typing equality.
-/
theorem eo_typeof_eq_translated_eo_fun_of_smt_fun
    {x : Term} {A B : SmtType}
    (hRec : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.FunType A B) :
    ∃ T1 T2,
      __eo_typeof x = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
      __eo_to_smt_type T1 = A ∧
      __eo_to_smt_type T2 = B ∧
      __eo_to_smt_type T1 ≠ SmtType.None ∧
      __eo_to_smt_type T2 ≠ SmtType.None := by
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.FunType A B := by
    rw [← hRec, hx]
  exact eo_to_smt_type_eq_fun_iff.mp hTy

theorem eo_typeof_eq_translated_eo_dtc_app_of_smt_dtc_app
    {x : Term} {A B : SmtType}
    (hRec : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.DtcAppType A B) :
    ∃ T1 T2,
      __eo_typeof x = Term.DtcAppType T1 T2 ∧
      __eo_to_smt_type T1 = A ∧
      __eo_to_smt_type T2 = B ∧
      __eo_to_smt_type T1 ≠ SmtType.None ∧
      __eo_to_smt_type T2 ≠ SmtType.None := by
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.DtcAppType A B := by
    rw [← hRec, hx]
  exact eo_to_smt_type_eq_dtc_app_iff.mp hTy

/- The datatype names made available to references inside a declaration block. -/
def eo_datatype_decl_names : DatatypeDecl -> List native_String
  | DatatypeDecl.nil => []
  | DatatypeDecl.cons s _ dd => s :: eo_datatype_decl_names dd

/- Proof-side validity predicates for the EO type fragment meant to survive translation. -/
mutual

def eo_type_valid_rec (refs : List native_String) : Term -> Prop
  | Term.Bool => True
  | Term.DatatypeType s dd =>
      __eo_to_smt_reserved_datatype_name s = false ∧
        s ∈ eo_datatype_decl_names dd ∧
        eo_datatype_decl_valid_rec (eo_datatype_decl_names dd) dd
  | Term.DatatypeTypeRef s => __eo_to_smt_reserved_datatype_name s = false ∧ s ∈ refs
  | Term.DtcAppType T U => eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U
  | Term.USort _ => True
  | Term.Apply (Term.Apply Term.FunType T1) T2 =>
      eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2
  | Term.UOp UserOp.Int => True
  | Term.UOp UserOp.Real => True
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n) => 0 <= n
  | Term.UOp UserOp.Char => True
  | Term.Apply (Term.UOp UserOp.Seq) x => eo_type_valid_rec [] x
  | _ => False

def eo_datatype_cons_valid_rec (refs : List native_String) : DatatypeCons -> Prop
  | DatatypeCons.unit => True
  | DatatypeCons.cons T c =>
      eo_type_valid_rec refs T ∧ eo_datatype_cons_valid_rec refs c

def eo_datatype_valid_rec (refs : List native_String) : Datatype -> Prop
  | Datatype.null => True
  | Datatype.sum c d =>
      eo_datatype_cons_valid_rec refs c ∧ eo_datatype_valid_rec refs d

def eo_datatype_decl_valid_rec (refs : List native_String) : DatatypeDecl -> Prop
  | DatatypeDecl.nil => True
  | DatatypeDecl.cons _ d dd =>
      eo_datatype_valid_rec refs d ∧ eo_datatype_decl_valid_rec refs dd

end

/-- Valid EO types always translate to a non-`None` SMT type. -/
theorem eo_type_valid_rec_non_none :
    ∀ {refs : List native_String} {T : Term},
      eo_type_valid_rec refs T -> __eo_to_smt_type T ≠ SmtType.None
  | refs, Term.UOp op, h => by
      cases op with
      | Int =>
          simp [__eo_to_smt_type]
      | Real =>
          simp [__eo_to_smt_type]
      | Char =>
          simp [__eo_to_smt_type]
      | _ =>
          simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_nil, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_cons, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Bool, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.Boolean b, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Numeral n, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Rational q, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.String s, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Binary w n, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Type, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Stuck, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.USort i, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.FunType, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Var name ty, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.DatatypeType s d, h => by
      rcases h with ⟨hReserved, _⟩
      simp [__eo_to_smt_type, hReserved]
  | refs, Term.DatatypeTypeRef s, h => by
      rcases h with ⟨hReserved, _⟩
      simp [__eo_to_smt_type, hReserved]
  | refs, Term.DtcAppType T U, h => by
      rcases h with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.Apply Term.FunType T1) T2, h => by
      rcases h with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      simp [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      have hz : native_zleq 0 n = true := by
        simpa [eo_type_valid_rec, native_zleq] using h
      simp [__eo_to_smt_type, native_ite, hz]
  | refs, Term.Apply (Term.UOp UserOp.Seq) x, h => by
      have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none h
      simp [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  have hz : native_zleq 0 n = true := by
                    simpa [eo_type_valid_rec, native_zleq] using h
                  simp [__eo_to_smt_type, native_ite, hz]
              | _ =>
                  simp [eo_type_valid_rec] at h
          | Seq =>
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := by
                have hx : eo_type_valid_rec [] x := by
                  simpa [eo_type_valid_rec] using h
                exact eo_type_valid_rec_non_none hx
              simp [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
          | _ =>
              simp [eo_type_valid_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using h :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              have hyNN : __eo_to_smt_type y ≠ SmtType.None := eo_type_valid_rec_non_none hy
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
              simp [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
          | _ =>
              simp [eo_type_valid_rec] at h
      | _ =>
          simp [eo_type_valid_rec] at h
  | refs, Term.DtCons s d i, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.DtSel s d i j, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.UConst i T, h => by
      simp [eo_type_valid_rec] at h

/-- `native_int_to_nat` is injective on nonnegative integers. -/
private theorem native_int_to_nat_injective_of_nonneg
    {m n : native_Int}
    (hm : 0 <= m) (hn : 0 <= n)
    (h : native_int_to_nat m = native_int_to_nat n) :
    m = n := by
  rw [← Int.toNat_of_nonneg hm, ← Int.toNat_of_nonneg hn]
  exact congrArg Int.ofNat h

/- On valid EO types, `__eo_to_smt_type` is injective. -/
mutual

private theorem eo_to_smt_type_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {T U : Term},
      eo_type_valid_rec refs T ->
      __eo_to_smt_type T = __eo_to_smt_type U ->
      T = U
  | Term.UOp op, U, hValid, hEq => by
      cases op with
      | Int =>
          have hU : __eo_to_smt_type U = SmtType.Int := by
            simpa using hEq.symm
          exact (eo_to_smt_type_eq_int hU).symm
      | Real =>
          have hU : __eo_to_smt_type U = SmtType.Real := by
            simpa using hEq.symm
          exact (eo_to_smt_type_eq_real hU).symm
      | Char =>
          have hU : __eo_to_smt_type U = SmtType.Char := by
            simpa using hEq.symm
          exact (eo_to_smt_type_eq_char hU).symm
      | _ =>
          simp [eo_type_valid_rec] at hValid
  | Term.__eo_List, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List_nil, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List_cons, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Bool, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Bool := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_bool hU).symm
  | Term.Boolean b, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Numeral n, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Rational q, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.String s, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Binary w n, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Type, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Stuck, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.USort i, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.USort i := by
        simpa [__eo_to_smt_type] using hEq.symm
      exact (eo_to_smt_type_eq_usort hU).symm
  | Term.FunType, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Var name ty, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.DatatypeType s d, U, hValid, hEq => by
      rcases hValid with ⟨hReserved, _hMem, hValid⟩
      have hU :
          __eo_to_smt_type U =
            SmtType.Datatype s (__eo_to_smt_datatype_decl d) := by
        simpa [__eo_to_smt_type, hReserved] using hEq.symm
      rcases eo_to_smt_type_eq_datatype_iff.mp hU with ⟨d0, hU', _, hd0⟩
      subst hU'
      have hd : d = d0 :=
        eo_to_smt_datatype_decl_unique_of_valid_rec
          (eo_datatype_decl_names d) hValid hd0.symm
      cases hd
      rfl
  | Term.DatatypeTypeRef s, U, hValid, hEq => by
      rcases hValid with ⟨hReserved, _⟩
      have hU : __eo_to_smt_type U = SmtType.TypeRef s := by
        simpa [__eo_to_smt_type, hReserved] using hEq.symm
      exact (eo_to_smt_type_eq_typeref_iff.mp hU).1.symm
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), U, hValid, hEq => by
      have hz : native_zleq 0 n = true := by
        simpa [eo_type_valid_rec, native_zleq] using hValid
      have hU : __eo_to_smt_type U = SmtType.BitVec (native_int_to_nat n) := by
        simpa [__eo_to_smt_type, native_ite, hz] using hEq.symm
      rcases eo_to_smt_type_eq_bitvec_iff.mp hU with ⟨m, hU', hm, hmn⟩
      subst hU'
      have hm' : 0 <= m := by
        simpa [native_zleq] using hm
      have hmn' : m = n :=
        native_int_to_nat_injective_of_nonneg hm' hValid hmn
      cases hmn'
      rfl
  | Term.Apply (Term.UOp UserOp.Seq) T1, U, hValid, hEq => by
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hValid
      have hU : __eo_to_smt_type U = SmtType.Seq (__eo_to_smt_type T1) := by
        simp [__eo_to_smt_type, hT1NN, __smtx_typeof_guard, native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_seq_iff.mp hU with ⟨U1, hU', hU1, _⟩
      subst hU'
      have hSub : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec [] hValid hU1.symm
      cases hSub
      rfl
  | Term.Apply (Term.Apply Term.FunType T1) T2, U, hValid, hEq => by
      rcases hValid with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      by_cases hFin :
          __smtx_is_finite_type
            (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) = true
      · have hU :
            __eo_to_smt_type U =
              SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
          simpa [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard,
            native_ite, native_Teq, hFin] using hEq.symm
        rcases eo_to_smt_type_eq_fun_iff.mp hU with
          ⟨U1, U2, hU', hU1, hU2, _, _⟩
        subst hU'
        have hSub1 : T1 = U1 :=
          eo_to_smt_type_unique_of_valid_rec [] hT1 hU1.symm
        have hSub2 : T2 = U2 :=
          eo_to_smt_type_unique_of_valid_rec [] hT2 hU2.symm
        cases hSub1
        cases hSub2
        rfl
      · have hFinFalse :
            __smtx_is_finite_type
              (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) = false := by
          cases hFin' :
              __smtx_is_finite_type
                (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) <;>
            simp [hFin'] at hFin ⊢
        have hU :
            __eo_to_smt_type U =
              SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
          simpa [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard,
            native_ite, native_Teq, hFinFalse] using hEq.symm
        rcases eo_to_smt_type_eq_fun_iff.mp hU with
          ⟨U1, U2, hU', hU1, hU2, _, _⟩
        subst hU'
        have hSub1 : T1 = U1 :=
          eo_to_smt_type_unique_of_valid_rec [] hT1 hU1.symm
        have hSub2 : T2 = U2 :=
          eo_to_smt_type_unique_of_valid_rec [] hT2 hU2.symm
        cases hSub1
        cases hSub2
        rfl
  | Term.DtcAppType T1 T2, U, hValid, hEq => by
      rcases hValid with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      have hU :
          __eo_to_smt_type U =
            SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
        simp [__eo_to_smt_type, hT1NN, hT2NN, __smtx_typeof_guard,
          native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_dtc_app_iff.mp hU with
        ⟨U1, U2, hU', hU1, hU2, _, _⟩
      subst hU'
      have hSub1 : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec [] hT1 hU1.symm
      have hSub2 : T2 = U2 :=
        eo_to_smt_type_unique_of_valid_rec [] hT2 hU2.symm
      cases hSub1
      cases hSub2
      rfl
  | Term.Apply f x, U, hValid, hEq => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  have hz : native_zleq 0 n = true := by
                    simpa [eo_type_valid_rec, native_zleq] using hValid
                  have hU : __eo_to_smt_type U = SmtType.BitVec (native_int_to_nat n) := by
                    simpa [__eo_to_smt_type, native_ite, hz] using hEq.symm
                  rcases eo_to_smt_type_eq_bitvec_iff.mp hU with ⟨m, hU', hm, hmn⟩
                  subst hU'
                  have hm' : 0 <= m := by
                    simpa [native_zleq] using hm
                  have hmn' : m = n :=
                    native_int_to_nat_injective_of_nonneg hm'
                      (by simpa [eo_type_valid_rec] using hValid) hmn
                  cases hmn'
                  rfl
              | _ =>
                  simp [eo_type_valid_rec] at hValid
          | Seq =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using hValid
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
              have hU : __eo_to_smt_type U = SmtType.Seq (__eo_to_smt_type x) := by
                simpa [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite, native_Teq] using hEq.symm
              rcases eo_to_smt_type_eq_seq_iff.mp hU with ⟨U1, hU', hU1, _⟩
              subst hU'
              have hSub : x = U1 := eo_to_smt_type_unique_of_valid_rec [] hx hU1.symm
              cases hSub
              rfl
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using hValid :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              have hyNN : __eo_to_smt_type y ≠ SmtType.None := eo_type_valid_rec_non_none hy
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
              by_cases hFin :
                  __smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) = true
              · have hU :
                    __eo_to_smt_type U =
                      SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x) := by
                  simpa [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard,
                    native_ite, native_Teq, hFin] using hEq.symm
                rcases eo_to_smt_type_eq_fun_iff.mp hU with
                  ⟨U1, U2, hU', hU1, hU2, _, _⟩
                subst hU'
                have hSub1 : y = U1 := eo_to_smt_type_unique_of_valid_rec [] hy hU1.symm
                have hSub2 : x = U2 := eo_to_smt_type_unique_of_valid_rec [] hx hU2.symm
                cases hSub1
                cases hSub2
                rfl
              · have hFinFalse :
                    __smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) = false := by
                  cases hFin' :
                      __smtx_is_finite_type
                        (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                    simp [hFin'] at hFin ⊢
                have hU :
                    __eo_to_smt_type U =
                      SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x) := by
                  simpa [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard,
                    native_ite, native_Teq, hFinFalse] using hEq.symm
                rcases eo_to_smt_type_eq_fun_iff.mp hU with
                  ⟨U1, U2, hU', hU1, hU2, _, _⟩
                subst hU'
                have hSub1 : y = U1 := eo_to_smt_type_unique_of_valid_rec [] hy hU1.symm
                have hSub2 : x = U2 := eo_to_smt_type_unique_of_valid_rec [] hx hU2.symm
                cases hSub1
                cases hSub2
                rfl
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | _ =>
          simp [eo_type_valid_rec] at hValid
  | Term.DtCons s d i, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.DtSel s d i j, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.UConst i T, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid

private theorem eo_to_smt_datatype_cons_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {c c' : DatatypeCons},
      eo_datatype_cons_valid_rec refs c ->
      __eo_to_smt_datatype_cons c = __eo_to_smt_datatype_cons c' ->
      c = c'
  | DatatypeCons.unit, c', _, hEq => by
      cases c' <;> simp [__eo_to_smt_datatype_cons] at hEq
      rfl
  | DatatypeCons.cons T c, c', hValid, hEq => by
      rcases hValid with ⟨hT, hC⟩
      cases c' with
      | unit =>
          simp [__eo_to_smt_datatype_cons] at hEq
      | cons U c' =>
          simp [__eo_to_smt_datatype_cons] at hEq
          rcases hEq with ⟨hTU, hCC⟩
          have hT' : T = U := eo_to_smt_type_unique_of_valid_rec refs hT hTU
          have hC' : c = c' := eo_to_smt_datatype_cons_unique_of_valid_rec refs hC hCC
          cases hT'
          cases hC'
          rfl

private theorem eo_to_smt_datatype_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {d d' : Datatype},
      eo_datatype_valid_rec refs d ->
      __eo_to_smt_datatype d = __eo_to_smt_datatype d' ->
      d = d'
  | Datatype.null, d', _, hEq => by
      cases d' <;> simp [__eo_to_smt_datatype] at hEq
      rfl
  | Datatype.sum c d, d', hValid, hEq => by
      rcases hValid with ⟨hC, hD⟩
      cases d' with
      | null =>
          simp [__eo_to_smt_datatype] at hEq
      | sum c' d' =>
          simp [__eo_to_smt_datatype] at hEq
          rcases hEq with ⟨hCC, hDD⟩
          have hC' : c = c' := eo_to_smt_datatype_cons_unique_of_valid_rec refs hC hCC
          have hD' : d = d' := eo_to_smt_datatype_unique_of_valid_rec refs hD hDD
          cases hC'
          cases hD'
          rfl

private theorem eo_to_smt_datatype_decl_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {d d' : DatatypeDecl},
      eo_datatype_decl_valid_rec refs d ->
      __eo_to_smt_datatype_decl d = __eo_to_smt_datatype_decl d' ->
      d = d'
  | DatatypeDecl.nil, d', _, hEq => by
      cases d' <;> simp [__eo_to_smt_datatype_decl] at hEq
      rfl
  | DatatypeDecl.cons s d dd, d', hValid, hEq => by
      rcases hValid with ⟨hD, hDD⟩
      cases d' with
      | nil =>
          simp [__eo_to_smt_datatype_decl] at hEq
      | cons s' d' dd' =>
          simp [__eo_to_smt_datatype_decl] at hEq
          rcases hEq with ⟨hS, hD', hDD'⟩
          subst s'
          have hd : d = d' :=
            eo_to_smt_datatype_unique_of_valid_rec refs hD hD'
          have hdd : dd = dd' :=
            eo_to_smt_datatype_decl_unique_of_valid_rec refs hDD hDD'
          cases hd
          cases hdd
          rfl

end

/-- Injectivity of EO-to-SMT type translation on the proof-side valid fragment. -/
theorem eo_to_smt_type_eq_of_valid_rec
    {refs : List native_String} {T U : Term}
    (hValid : eo_type_valid_rec refs T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_unique_of_valid_rec refs hValid hEq

/-- Top-level specialization of `eo_to_smt_type_eq_of_valid_rec`. -/
theorem eo_to_smt_type_eq_of_valid
    {T U : Term}
    (hValid : eo_type_valid_rec [] T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid_rec hValid hEq

/- BEGIN obsolete body-substitution development.
The declaration-based datatype model resolves references through a shared
declaration environment instead; the replacement lemmas follow this block.
/-- Converts a reflected ref-list membership test into propositional membership. -/
private theorem native_reflist_contains_true
    {refs : List native_String} {s : native_String}
    (h : native_reflist_contains refs s = true) :
    s ∈ refs := by
  simpa [native_reflist_contains] using h

/-- Decomposes `if a then b else false = true` into its two boolean witnesses. -/
private theorem native_ite_false_eq_true
    {a b : native_Bool}
    (h : native_ite a b false = true) :
    a = true ∧ b = true := by
  cases ha : a <;> cases hb : b <;> simp [native_ite, ha, hb] at h
  exact ⟨rfl, rfl⟩

/-- Extracts the element recursive well-formedness from a diagonal sequence wf proof. -/
private theorem smtx_type_wf_rec_seq_component
    {T : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Seq T) (SmtType.Seq T) = true) :
    __smtx_type_wf_rec T T = true := by
  have hPair :
      (native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true) ∧
        __smtx_type_no_alias_rec native_reflist_nil T = true := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact hPair.1.2

/- A proof-side relation for the left-hand, folded SMT shape that the generated
datatype wf predicates compare against the original EO datatype. The relation
records the scope information needed by the datatype-constructor special case:
a folded SMT datatype may stand opposite an EO `DatatypeTypeRef` only when that
reference name is in the current datatype-reference scope. -/
mutual

private def smt_fold_type_rec (refs : List native_String) (TF : SmtType) : Term -> Prop
  | Term.DatatypeType s d =>
      if __eo_to_smt_reserved_datatype_name s = true then
        TF = SmtType.None
      else
        ∃ dF, TF = SmtType.Datatype s dF ∧ smt_fold_datatype_rec (s :: refs) dF d
  | Term.DatatypeTypeRef s =>
      if __eo_to_smt_reserved_datatype_name s = true then
        TF = SmtType.None
      else
        TF = SmtType.TypeRef s ∨
          (s ∈ refs ∧ ∃ sF dF, TF = SmtType.Datatype sF dF)
  | T => TF = __eo_to_smt_type T

private def smt_fold_datatype_cons_rec
    (refs : List native_String) (cF : SmtDatatypeCons) : DatatypeCons -> Prop
  | DatatypeCons.unit => cF = SmtDatatypeCons.unit
  | DatatypeCons.cons T c =>
      ∃ TF cTailF,
        cF = SmtDatatypeCons.cons TF cTailF ∧
        smt_fold_type_rec refs TF T ∧
        smt_fold_datatype_cons_rec refs cTailF c

private def smt_fold_datatype_rec
    (refs : List native_String) (dF : SmtDatatype) : Datatype -> Prop
  | Datatype.null => dF = SmtDatatype.null
  | Datatype.sum c d =>
      ∃ cF dTailF,
        dF = SmtDatatype.sum cF dTailF ∧
        smt_fold_datatype_cons_rec refs cF c ∧
        smt_fold_datatype_rec refs dTailF d

end

mutual

private theorem smt_fold_type_rec_refl
    (refs : List native_String) :
    ∀ T : Term, smt_fold_type_rec refs (__eo_to_smt_type T) T
  | Term.DatatypeType s d => by
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
      · simp [smt_fold_type_rec, __eo_to_smt_type, hReserved]
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
        simpa [smt_fold_type_rec, __eo_to_smt_type, hReserved, hReservedFalse] using
          (⟨__eo_to_smt_datatype d, by simp [__eo_to_smt_type, hReservedFalse],
            smt_fold_datatype_rec_refl (s :: refs) d⟩ :
            ∃ dF,
              __eo_to_smt_type (Term.DatatypeType s d) = SmtType.Datatype s dF ∧
              smt_fold_datatype_rec (s :: refs) dF d)
  | Term.DatatypeTypeRef s => by
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
      · simp [smt_fold_type_rec, __eo_to_smt_type, hReserved]
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
        simp [smt_fold_type_rec, __eo_to_smt_type, hReserved]
  | T => by
      cases T <;> try simp [smt_fold_type_rec]
      case DatatypeType s d =>
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
        · simp [hReserved]
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
          simpa [smt_fold_type_rec, __eo_to_smt_type, hReserved, hReservedFalse] using
            (⟨__eo_to_smt_datatype d, by simp [__eo_to_smt_type, hReservedFalse],
              smt_fold_datatype_rec_refl (s :: refs) d⟩ :
              ∃ dF,
                __eo_to_smt_type (Term.DatatypeType s d) = SmtType.Datatype s dF ∧
                smt_fold_datatype_rec (s :: refs) dF d)
      case DatatypeTypeRef s =>
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
        · simp [__eo_to_smt_type, hReserved]
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
          simp [__eo_to_smt_type, hReserved]

private theorem smt_fold_datatype_cons_rec_refl
    (refs : List native_String) :
    ∀ c : DatatypeCons,
      smt_fold_datatype_cons_rec refs (__eo_to_smt_datatype_cons c) c
  | DatatypeCons.unit => by
      simp [smt_fold_datatype_cons_rec, __eo_to_smt_datatype_cons]
  | DatatypeCons.cons T c => by
      refine ⟨__eo_to_smt_type T, __eo_to_smt_datatype_cons c, ?_, ?_, ?_⟩
      · simp [__eo_to_smt_datatype_cons]
      · exact smt_fold_type_rec_refl refs T
      · exact smt_fold_datatype_cons_rec_refl refs c

private theorem smt_fold_datatype_rec_refl
    (refs : List native_String) :
    ∀ d : Datatype, smt_fold_datatype_rec refs (__eo_to_smt_datatype d) d
  | Datatype.null => by
      simp [smt_fold_datatype_rec, __eo_to_smt_datatype]
  | Datatype.sum c d => by
      refine ⟨__eo_to_smt_datatype_cons c, __eo_to_smt_datatype d, ?_, ?_, ?_⟩
      · simp [__eo_to_smt_datatype]
      · exact smt_fold_datatype_cons_rec_refl refs c
      · exact smt_fold_datatype_rec_refl refs d

end

mutual

private theorem smt_fold_type_rec_weaken
    {refs refs' : List native_String} {TF : SmtType} {T : Term}
    (hFold : smt_fold_type_rec refs TF T)
    (hsub : ∀ t, t ∈ refs -> t ∈ refs') :
    smt_fold_type_rec refs' TF T := by
  cases T with
  | DatatypeType s d =>
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
      · simpa [smt_fold_type_rec, hReserved] using hFold
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
        rcases (by simpa [smt_fold_type_rec, hReserved] using hFold) with
          ⟨dF, hTF, hD⟩
        simpa [smt_fold_type_rec, hReserved] using
          (⟨dF, hTF, smt_fold_datatype_rec_weaken hD (by
            intro t ht
            simp at ht ⊢
            rcases ht with rfl | ht
            · exact Or.inl rfl
            · exact Or.inr (hsub t ht))⟩ :
            ∃ dF, TF = SmtType.Datatype s dF ∧
              smt_fold_datatype_rec (s :: refs') dF d)
  | DatatypeTypeRef s =>
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
      · simpa [smt_fold_type_rec, hReserved] using hFold
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
        rcases (by simpa [smt_fold_type_rec, hReserved] using hFold) with
          hTypeRef | ⟨hMem, hDatatype⟩
        · simpa [smt_fold_type_rec, hReserved] using
            (Or.inl hTypeRef :
              TF = SmtType.TypeRef s ∨
                (s ∈ refs' ∧ ∃ sF dF, TF = SmtType.Datatype sF dF))
        · simpa [smt_fold_type_rec, hReserved] using
            (Or.inr ⟨hsub s hMem, hDatatype⟩ :
              TF = SmtType.TypeRef s ∨
                (s ∈ refs' ∧ ∃ sF dF, TF = SmtType.Datatype sF dF))
  | _ =>
      simpa [smt_fold_type_rec] using hFold

private theorem smt_fold_datatype_cons_rec_weaken
    {refs refs' : List native_String} {cF : SmtDatatypeCons} {c : DatatypeCons}
    (hFold : smt_fold_datatype_cons_rec refs cF c)
    (hsub : ∀ t, t ∈ refs -> t ∈ refs') :
    smt_fold_datatype_cons_rec refs' cF c := by
  cases c with
  | unit =>
      simpa [smt_fold_datatype_cons_rec] using hFold
  | cons T c =>
      rcases hFold with ⟨TF, cTailF, hEq, hT, hC⟩
      exact ⟨TF, cTailF, hEq, smt_fold_type_rec_weaken hT hsub,
        smt_fold_datatype_cons_rec_weaken hC hsub⟩

private theorem smt_fold_datatype_rec_weaken
    {refs refs' : List native_String} {dF : SmtDatatype} {d : Datatype}
    (hFold : smt_fold_datatype_rec refs dF d)
    (hsub : ∀ t, t ∈ refs -> t ∈ refs') :
    smt_fold_datatype_rec refs' dF d := by
  cases d with
  | null =>
      simpa [smt_fold_datatype_rec] using hFold
  | sum c d =>
      rcases hFold with ⟨cF, dTailF, hEq, hC, hD⟩
      exact ⟨cF, dTailF, hEq, smt_fold_datatype_cons_rec_weaken hC hsub,
        smt_fold_datatype_rec_weaken hD hsub⟩

end

private theorem smt_fold_datatype_rec_swap_cons
    {s s2 : native_String} {refs : List native_String}
    {dF : SmtDatatype} {d : Datatype}
    (hFold : smt_fold_datatype_rec (s :: s2 :: refs) dF d) :
    smt_fold_datatype_rec (s2 :: s :: refs) dF d :=
  smt_fold_datatype_rec_weaken hFold (by
    intro t ht
    simp at ht ⊢
    rcases ht with rfl | rfl | ht
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ht))

mutual

private theorem smt_fold_type_rec_substitute
    (s : native_String) (base : SmtDatatype) {refs : List native_String}
    {TF : SmtType} {T : Term}
    (hFold : smt_fold_type_rec refs TF T) :
    smt_fold_type_rec (s :: refs) (__smtx_type_substitute s base TF) T := by
  cases T with
  | DatatypeType s2 d2 =>
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
      · have hTF : TF = SmtType.None := by
          simpa [smt_fold_type_rec, hReserved] using hFold
        subst hTF
        simp [smt_fold_type_rec, __smtx_type_substitute, hReserved]
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s2 = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s2 <;> simp [hName] at hReserved ⊢
        rcases (by simpa [smt_fold_type_rec, hReserved] using hFold) with
          ⟨dF, hTF, hD⟩
        subst hTF
        by_cases hst : native_streq s s2 = true
        · simpa [smt_fold_type_rec, __smtx_type_substitute, hReserved, hst] using
            (⟨dF, by simp [__smtx_type_substitute, hst],
              smt_fold_datatype_rec_weaken hD (by
                intro t ht
                simp at ht ⊢
                rcases ht with rfl | ht
                · exact Or.inl rfl
                · exact Or.inr (Or.inr ht))⟩ :
              ∃ dF_1,
                __smtx_type_substitute s base (SmtType.Datatype s2 dF) =
                  SmtType.Datatype s2 dF_1 ∧
                smt_fold_datatype_rec (s2 :: s :: refs) dF_1 d2)
        · have hDSub :
              smt_fold_datatype_rec (s :: s2 :: refs)
                (__smtx_dt_substitute s (__smtx_dt_lift s2 dF base) dF) d2 :=
            smt_fold_datatype_rec_substitute s (__smtx_dt_lift s2 dF base) hD
          simpa [smt_fold_type_rec, __smtx_type_substitute, hReserved, hst] using
            (⟨__smtx_dt_substitute s (__smtx_dt_lift s2 dF base) dF,
              by simp [__smtx_type_substitute, hst],
              smt_fold_datatype_rec_swap_cons hDSub⟩ :
              ∃ dF_1,
                __smtx_type_substitute s base (SmtType.Datatype s2 dF) =
                  SmtType.Datatype s2 dF_1 ∧
                smt_fold_datatype_rec (s2 :: s :: refs) dF_1 d2)
  | DatatypeTypeRef s2 =>
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
      · have hTF : TF = SmtType.None := by
          simpa [smt_fold_type_rec, hReserved] using hFold
        subst hTF
        simp [smt_fold_type_rec, __smtx_type_substitute, hReserved]
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s2 = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s2 <;> simp [hName] at hReserved ⊢
        rcases (by simpa [smt_fold_type_rec, hReserved] using hFold) with
          hTypeRef | ⟨hMem, hDatatype⟩
        · subst hTypeRef
          by_cases hs : s = s2
          · subst s2
            simp [smt_fold_type_rec, __smtx_type_substitute, hReserved, native_streq]
          · have hst : native_streq s s2 = false := by
              simp [native_streq, hs]
            simp [smt_fold_type_rec, __smtx_type_substitute, hReserved, hst]
        · rcases hDatatype with ⟨sF, dF, hTF⟩
          subst hTF
          have hDatatype' :
              ∃ sF' dF',
                __smtx_type_substitute s base (SmtType.Datatype sF dF) =
                  SmtType.Datatype sF' dF' := by
            cases hResult : __smtx_type_substitute s base (SmtType.Datatype sF dF) with
            | Datatype sF' dF' =>
                exact ⟨sF', dF', rfl⟩
            | _ =>
                simp [__smtx_type_substitute] at hResult
          simpa [smt_fold_type_rec, hReserved] using
            (Or.inr ⟨List.mem_cons_of_mem s hMem, hDatatype'⟩ :
              __smtx_type_substitute s base (SmtType.Datatype sF dF) =
                  SmtType.TypeRef s2 ∨
                (s2 ∈ s :: refs ∧
                  ∃ sF' dF',
                    __smtx_type_substitute s base (SmtType.Datatype sF dF) =
                      SmtType.Datatype sF' dF'))
  | UOp op =>
      have hTF : TF = __eo_to_smt_type (Term.UOp op) := by
        simpa [smt_fold_type_rec] using hFold
      subst hTF
      cases op <;> simp [smt_fold_type_rec, __eo_to_smt_type, __smtx_type_substitute]
  | Apply f x =>
      have hTF : TF = __eo_to_smt_type (Term.Apply f x) := by
        simpa [smt_fold_type_rec] using hFold
      subst hTF
      cases hTy : __eo_to_smt_type (Term.Apply f x) <;>
        simp [smt_fold_type_rec, __smtx_type_substitute, hTy]
      case TypeRef r =>
        exact False.elim (eo_to_smt_type_apply_ne_typeref f x r hTy)
      case Datatype sF dF =>
        exact False.elim (eo_to_smt_type_apply_ne_datatype f x sF dF hTy)
  | DtcAppType T U =>
      have hTF : TF = __eo_to_smt_type (Term.DtcAppType T U) := by
        simpa [smt_fold_type_rec] using hFold
      subst hTF
      cases hTy : __eo_to_smt_type (Term.DtcAppType T U) <;>
        simp [smt_fold_type_rec, __smtx_type_substitute, hTy]
      case TypeRef r =>
        exact False.elim
          (smtx_typeof_guard_dtc_app_ne_typeref
            (__eo_to_smt_type T) (__eo_to_smt_type U) r hTy)
      case Datatype sF dF =>
        exact False.elim (eo_to_smt_type_dtc_app_ne_datatype T U sF dF hTy)
  | _ =>
      subst TF
      simp [smt_fold_type_rec, __smtx_type_substitute, __eo_to_smt_type]

private theorem smt_fold_datatype_cons_rec_substitute
    (s : native_String) (base : SmtDatatype) {refs : List native_String}
    {cF : SmtDatatypeCons} {c : DatatypeCons}
    (hFold : smt_fold_datatype_cons_rec refs cF c) :
    smt_fold_datatype_cons_rec (s :: refs)
      (__smtx_dtc_substitute s base cF) c := by
  cases c with
  | unit =>
      have hEq : cF = SmtDatatypeCons.unit := by
        simpa [smt_fold_datatype_cons_rec] using hFold
      subst hEq
      simp [smt_fold_datatype_cons_rec, __smtx_dtc_substitute]
  | cons T c =>
      rcases hFold with ⟨TF, cTailF, hEq, hT, hC⟩
      subst hEq
      refine ⟨__smtx_type_substitute s base TF,
        __smtx_dtc_substitute s base cTailF, ?_, ?_, ?_⟩
      · simp [__smtx_dtc_substitute]
      · exact smt_fold_type_rec_substitute s base hT
      · exact smt_fold_datatype_cons_rec_substitute s base hC

private theorem smt_fold_datatype_rec_substitute
    (s : native_String) (base : SmtDatatype) {refs : List native_String}
    {dF : SmtDatatype} {d : Datatype}
    (hFold : smt_fold_datatype_rec refs dF d) :
    smt_fold_datatype_rec (s :: refs)
      (__smtx_dt_substitute s base dF) d := by
  cases d with
  | null =>
      have hEq : dF = SmtDatatype.null := by
        simpa [smt_fold_datatype_rec] using hFold
      subst hEq
      simp [smt_fold_datatype_rec, __smtx_dt_substitute]
  | sum c d =>
      rcases hFold with ⟨cF, dTailF, hEq, hC, hD⟩
      subst hEq
      refine ⟨__smtx_dtc_substitute s base cF,
        __smtx_dt_substitute s base dTailF, ?_, ?_, ?_⟩
      · simp [__smtx_dt_substitute]
      · exact smt_fold_datatype_cons_rec_substitute s base hC
      · exact smt_fold_datatype_rec_substitute s base hD

end

private theorem smtx_dt_cons_wf_rec_generic_parts
    {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (hNotSpecial : ¬ ∃ sF dF r, TF = SmtType.Datatype sF dF ∧ TU = SmtType.TypeRef r)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_type_wf_rec TF TU = true ∧ __smtx_dt_cons_wf_rec cF cU = true := by
  cases TF <;> cases TU <;>
    simp [__smtx_dt_cons_wf_rec, native_ite, native_and] at h hNotSpecial ⊢
  all_goals first | exact ⟨h.1.2, h.2⟩ | contradiction

mutual

private theorem eo_type_valid_of_folded_smt_wf_rec
    {refs : List native_String} {TF : SmtType} {T : Term}
    (hFold : smt_fold_type_rec refs TF T) :
    __smtx_type_wf_rec TF (__eo_to_smt_type T) = true ->
      eo_type_valid_rec refs T
  | h => by
      cases T with
      | Bool =>
          simp [eo_type_valid_rec]
      | UOp op =>
          have hTF : TF = __eo_to_smt_type (Term.UOp op) := by
            simpa [smt_fold_type_rec] using hFold
          subst hTF
          cases op with
          | Int => simp [eo_type_valid_rec]
          | Real => simp [eo_type_valid_rec]
          | Char => simp [eo_type_valid_rec]
          | _ =>
              have : False := by
                simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
              exact False.elim this
      | USort _ =>
          simp [eo_type_valid_rec]
      | DatatypeType s d =>
          by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
          · have hTF : TF = SmtType.None := by
              simpa [smt_fold_type_rec, hReserved] using hFold
            subst hTF
            have : False := by
              simp [__eo_to_smt_type, __smtx_type_wf_rec, hReserved] at h
            exact False.elim this
          · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
              cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
            rcases (by simpa [smt_fold_type_rec, hReserved] using hFold) with
              ⟨dF, hTF, hD⟩
            subst hTF
            have hBodyWf :
                __smtx_dt_wf_rec (__smtx_dt_substitute s dF dF)
                  (__eo_to_smt_datatype d) = true := by
              simpa [__eo_to_smt_type, __smtx_type_wf_rec, hReservedFalse] using h
            have hBodyFoldDup :
                smt_fold_datatype_rec (s :: s :: refs)
                  (__smtx_dt_substitute s dF dF) d :=
              smt_fold_datatype_rec_substitute s dF hD
            have hBodyFold :
                smt_fold_datatype_rec (s :: refs)
                  (__smtx_dt_substitute s dF dF) d :=
              smt_fold_datatype_rec_weaken hBodyFoldDup (by
                intro t ht
                cases ht with
                | head =>
                    simp
                | tail _ ht' =>
                    cases ht' with
                    | head =>
                        simp
                    | tail _ ht'' =>
                        exact List.mem_cons_of_mem s ht'')
            exact ⟨hReservedFalse, eo_datatype_valid_of_folded_smt_wf_rec hBodyFold hBodyWf⟩
      | DatatypeTypeRef s =>
          have : False := by
            by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
            · have hTF : TF = SmtType.None := by
                simpa [smt_fold_type_rec, hReserved] using hFold
              subst hTF
              simp [__eo_to_smt_type, __smtx_type_wf_rec, hReserved] at h
            · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
                cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
              rcases (by simpa [smt_fold_type_rec, hReserved] using hFold) with
                hTypeRef | ⟨_hMem, hDatatype⟩
              · subst hTypeRef
                simp [__eo_to_smt_type, __smtx_type_wf_rec, hReservedFalse] at h
              · rcases hDatatype with ⟨sF, dF, hTF⟩
                subst hTF
                simp [__eo_to_smt_type, __smtx_type_wf_rec, hReservedFalse] at h
          exact False.elim this
      | DtcAppType T U =>
          have hTF : TF = __eo_to_smt_type (Term.DtcAppType T U) := by
            simpa [smt_fold_type_rec] using hFold
          subst hTF
          have : False := by
            cases hT : __eo_to_smt_type T <;>
            cases hU : __eo_to_smt_type U <;>
              simp [__eo_to_smt_type, __smtx_type_wf_rec, __smtx_typeof_guard,
                native_ite, native_Teq, hT, hU] at h
          exact False.elim this
      | Apply f x =>
          have hTF : TF = __eo_to_smt_type (Term.Apply f x) := by
            simpa [smt_fold_type_rec] using hFold
          subst hTF
          cases f with
          | UOp op =>
              cases op with
              | Seq =>
                  have hx : __smtx_type_wf_rec (__eo_to_smt_type x) (__eo_to_smt_type x) = true := by
                    have hSeq :
                        __smtx_type_wf_rec (SmtType.Seq (__eo_to_smt_type x))
                          (SmtType.Seq (__eo_to_smt_type x)) = true := by
                      cases hTy : __eo_to_smt_type x <;>
                        simp [__eo_to_smt_type, hTy, __smtx_typeof_guard,
                          __smtx_type_wf_rec, native_and, native_ite, native_Teq] at h ⊢
                      all_goals first | exact h | contradiction
                    exact smtx_type_wf_rec_seq_component hSeq
                  change eo_type_valid_rec [] x
                  exact eo_type_valid_of_folded_smt_wf_rec
                    (by
                      change smt_fold_type_rec [] (__eo_to_smt_type x) x
                      exact smt_fold_type_rec_refl [] x) hx
              | BitVec =>
                  cases x with
                  | Numeral n =>
                      by_cases hz : native_zleq 0 n = true
                      · simpa [eo_type_valid_rec, native_zleq] using hz
                      · have : False := by
                          simp [__eo_to_smt_type, __smtx_type_wf_rec, hz] at h
                        exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
                  exact False.elim this
          | Apply g y =>
              cases g with
              | FunType =>
                  have : False := by
                    cases hY : __eo_to_smt_type y <;>
                    cases hX : __eo_to_smt_type x <;>
                      simp [__eo_to_smt_type, hY, hX,
                        __smtx_typeof_guard, __smtx_type_wf_rec, native_ite,
                        native_Teq] at h
                  exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
              exact False.elim this
      | _ =>
          simp [smt_fold_type_rec] at hFold
          subst TF
          have : False := by
            simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
          exact False.elim this

private theorem eo_datatype_cons_valid_of_folded_smt_wf_rec
    {refs : List native_String} {cF : SmtDatatypeCons} {c : DatatypeCons}
    (hFold : smt_fold_datatype_cons_rec refs cF c) :
    __smtx_dt_cons_wf_rec cF (__eo_to_smt_datatype_cons c) = true ->
      eo_datatype_cons_valid_rec refs c
  | h => by
      cases c with
      | unit =>
          simp [eo_datatype_cons_valid_rec]
      | cons T c =>
          rcases hFold with ⟨TF, cTailF, hEq, hTFold, hCFold⟩
          subst hEq
          by_cases hSpecial :
              ∃ sF dF r,
                TF = SmtType.Datatype sF dF ∧ __eo_to_smt_type T = SmtType.TypeRef r
          · rcases hSpecial with ⟨sF, dF, r, hTF, hU⟩
            subst hTF
            have hTail :
                __smtx_dt_cons_wf_rec cTailF (__eo_to_smt_datatype_cons c) = true := by
              simpa [__smtx_dt_cons_wf_rec, __eo_to_smt_datatype_cons, hU] using h
            rcases eo_to_smt_type_eq_typeref_iff.mp hU with ⟨hT, hReserved⟩
            subst hT
            have hFoldRef :
                SmtType.Datatype sF dF = SmtType.TypeRef r ∨
                  (r ∈ refs ∧
                    ∃ sF' dF', SmtType.Datatype sF dF = SmtType.Datatype sF' dF') := by
              simpa [smt_fold_type_rec, hReserved] using hTFold
            rcases hFoldRef with hEqRef | ⟨hMem, _⟩
            · cases hEqRef
            · exact ⟨⟨hReserved, hMem⟩,
                eo_datatype_cons_valid_of_folded_smt_wf_rec hCFold hTail⟩
          · have hParts :=
              smtx_dt_cons_wf_rec_generic_parts hSpecial h
            exact ⟨eo_type_valid_of_folded_smt_wf_rec hTFold hParts.1,
              eo_datatype_cons_valid_of_folded_smt_wf_rec hCFold hParts.2⟩

private theorem eo_datatype_valid_of_folded_smt_wf_rec
    {refs : List native_String} {dF : SmtDatatype} {d : Datatype}
    (hFold : smt_fold_datatype_rec refs dF d) :
    __smtx_dt_wf_rec dF (__eo_to_smt_datatype d) = true ->
      eo_datatype_valid_rec refs d
  | h => by
      cases d with
      | null =>
          simp [eo_datatype_valid_rec]
      | sum c d =>
          rcases hFold with ⟨cF, dTailF, hEq, hCFold, hDFold⟩
          subst hEq
          have hParts :
              __smtx_dt_cons_wf_rec cF (__eo_to_smt_datatype_cons c) = true ∧
                __smtx_dt_wf_rec dTailF (__eo_to_smt_datatype d) = true :=
            native_ite_false_eq_true (by simpa [__smtx_dt_wf_rec, __eo_to_smt_datatype] using h)
          exact ⟨eo_datatype_cons_valid_of_folded_smt_wf_rec hCFold hParts.1,
            eo_datatype_valid_of_folded_smt_wf_rec hDFold hParts.2⟩

end

/- Well-formed translated EO types have valid EO field shapes. -/
theorem eo_type_valid_of_smt_wf_rec
    (refs : List native_String) :
    ∀ {T : Term},
      __smtx_type_wf_rec (__eo_to_smt_type T) (__eo_to_smt_type T) = true ->
      eo_type_valid_rec refs T
  | T, h => eo_type_valid_of_folded_smt_wf_rec
      (smt_fold_type_rec_refl refs T) h

private theorem smtx_typeof_guard_ne_reglan
    (T U : SmtType) (hU : U ≠ SmtType.RegLan) :
    __smtx_typeof_guard T U ≠ SmtType.RegLan := by
  cases T <;> simp [__smtx_typeof_guard, native_Teq, hU]

theorem eo_to_smt_type_ne_reglan (T : Term) :
    __eo_to_smt_type T ≠ SmtType.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type]
  | UOp1 op x =>
      cases op <;> simp [__eo_to_smt_type]
  | UOp2 op x y =>
      cases op <;> simp [__eo_to_smt_type]
  | UOp3 op x y z =>
      cases op <;> simp [__eo_to_smt_type]
  | __eo_List => simp [__eo_to_smt_type]
  | __eo_List_nil => simp [__eo_to_smt_type]
  | __eo_List_cons => simp [__eo_to_smt_type]
  | Bool => simp [__eo_to_smt_type]
  | Boolean b => simp [__eo_to_smt_type]
  | Numeral n => simp [__eo_to_smt_type]
  | Rational q => simp [__eo_to_smt_type]
  | String s => simp [__eo_to_smt_type]
  | Binary w n => simp [__eo_to_smt_type]
  | «Type» => simp [__eo_to_smt_type]
  | Stuck => simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | Int => simp [__eo_to_smt_type]
          | Real => simp [__eo_to_smt_type]
          | BitVec =>
              cases x <;> try simp [__eo_to_smt_type]
              rename_i n
              by_cases h : native_zleq 0 n = true <;> simp [h]
          | Char => simp [__eo_to_smt_type]
          | Seq =>
              simpa [__eo_to_smt_type] using
                smtx_typeof_guard_ne_reglan (__eo_to_smt_type x)
                  (SmtType.Seq (__eo_to_smt_type x)) (by simp)
          | not => simp [__eo_to_smt_type]
          | or => simp [__eo_to_smt_type]
          | and => simp [__eo_to_smt_type]
          | imp => simp [__eo_to_smt_type]
          | eq => simp [__eo_to_smt_type]
      | UOp1 op y =>
          cases op <;> simp [__eo_to_smt_type]
      | UOp2 op y z =>
          cases op <;> simp [__eo_to_smt_type]
      | UOp3 op y z w =>
          cases op <;> simp [__eo_to_smt_type]
      | __eo_List => simp [__eo_to_smt_type]
      | __eo_List_nil => simp [__eo_to_smt_type]
      | __eo_List_cons => simp [__eo_to_smt_type]
      | Bool => simp [__eo_to_smt_type]
      | Boolean b => simp [__eo_to_smt_type]
      | Numeral n => simp [__eo_to_smt_type]
      | Rational q => simp [__eo_to_smt_type]
      | String s => simp [__eo_to_smt_type]
      | Binary w n => simp [__eo_to_smt_type]
      | «Type» => simp [__eo_to_smt_type]
      | Stuck => simp [__eo_to_smt_type]
      | Apply f1 f2 =>
            cases f1 <;> try simp [__eo_to_smt_type]
            simpa [__eo_to_smt_type] using
              smtx_typeof_guard_ne_reglan (__eo_to_smt_type f2)
                (__smtx_typeof_guard (__eo_to_smt_type x)
                  (native_ite
                    (__smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x)))
                    (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x))
                    (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x))))
                (smtx_typeof_guard_ne_reglan (__eo_to_smt_type x)
                  (native_ite
                    (__smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x)))
                    (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x))
                    (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x)))
                    (by
                      cases __smtx_is_finite_type
                          (SmtType.FunType (__eo_to_smt_type f2) (__eo_to_smt_type x)) <;>
                        simp [native_ite]))
      | FunType => simp [__eo_to_smt_type]
      | Var T U => simp [__eo_to_smt_type]
      | DatatypeType s d => simp [__eo_to_smt_type]
      | DatatypeTypeRef s => simp [__eo_to_smt_type]
      | DtcAppType T1 T2 => simp [__eo_to_smt_type]
      | DtCons s d i => simp [__eo_to_smt_type]
      | DtSel s d i j => simp [__eo_to_smt_type]
      | USort i => simp [__eo_to_smt_type]
      | UConst i T => simp [__eo_to_smt_type]
  | FunType => simp [__eo_to_smt_type]
  | Var T U => simp [__eo_to_smt_type]
  | DatatypeType s d =>
      by_cases h : __eo_to_smt_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, h]
  | DatatypeTypeRef s =>
      by_cases h : __eo_to_smt_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, h]
  | DtcAppType T1 T2 =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_ne_reglan (__eo_to_smt_type T1)
          (__smtx_typeof_guard (__eo_to_smt_type T2)
            (SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2)))
          (smtx_typeof_guard_ne_reglan (__eo_to_smt_type T2)
            (SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) (by simp))
  | DtCons s d i => simp [__eo_to_smt_type]
  | DtSel s d i j => simp [__eo_to_smt_type]
  | USort i => simp [__eo_to_smt_type]
  | UConst i T => simp [__eo_to_smt_type]

/-- Extracts component wf facts from top-level finite function type wf. -/
private theorem smtx_fun_type_wf_parts
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    native_inhabited_type A = true ∧
      __smtx_type_wf_rec A A = true ∧
        native_inhabited_type B = true ∧
          __smtx_type_wf_rec B B = true := by
  have hAll :
      ((native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true) ∧
          __smtx_type_no_alias_rec native_reflist_nil A = true) ∧
          ((native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true) ∧
              __smtx_type_no_alias_rec native_reflist_nil B = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, native_and] using h
  exact ⟨hAll.1.1.1, hAll.1.1.2, hAll.2.1.1, hAll.2.1.2⟩

/-- A non-`None` well-formedness guard witnesses proof-side EO type validity. -/
theorem eo_type_valid_of_guard_wf_non_none
    {T U : Term}
    (h : __smtx_typeof_guard_wf (__eo_to_smt_type T) (__eo_to_smt_type U) ≠ SmtType.None) :
    eo_type_valid_rec [] T := by
  unfold __smtx_typeof_guard_wf at h
  have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
    by_cases h1 : __smtx_type_wf (__eo_to_smt_type T) = true
    · exact h1
    · exfalso
      simp [native_ite, h1] at h
  by_cases hFun : ∃ A B, __eo_to_smt_type T = SmtType.FunType A B
  · rcases hFun with ⟨A, B, hTy⟩
    rcases (eo_to_smt_type_eq_fun_iff.mp hTy) with
      ⟨T1, T2, hTerm, hT1, hT2, _hT1NN, _hT2NN⟩
    subst T
    have hParts :
        native_inhabited_type A = true ∧
          __smtx_type_wf_rec A A = true ∧
            native_inhabited_type B = true ∧
              __smtx_type_wf_rec B B = true := by
      exact smtx_fun_type_wf_parts (by simpa [hTy] using hWf)
    simp [eo_type_valid_rec]
    exact ⟨
      eo_type_valid_of_smt_wf_rec [] (by simpa [hT1] using hParts.2.1),
      eo_type_valid_of_smt_wf_rec [] (by simpa [hT2] using hParts.2.2.2)⟩
  · have hPair :
        native_inhabited_type (__eo_to_smt_type T) = true ∧
          __smtx_type_wf_rec (__eo_to_smt_type T) (__eo_to_smt_type T) = true := by
        cases hTy : __eo_to_smt_type T <;> simp [__smtx_type_wf, native_and, hTy] at hWf ⊢
        case RegLan =>
          exact False.elim (eo_to_smt_type_ne_reglan T hTy)
        case FunType A B =>
          exact False.elim (hFun ⟨A, B, hTy⟩)
        all_goals
          first | exact hWf | exact hWf.1
    exact eo_type_valid_of_smt_wf_rec [] hPair.2

/-- Translating EO type-reference substitution matches the corresponding SMT substitution step. -/
theorem eo_to_smt_type_substitute_typeref
    (s : native_String) (d : Datatype) :
    ∀ T : Term,
      __eo_to_smt_type
          (native_ite (native_teq T (Term.DatatypeTypeRef s))
            (Term.DatatypeType s d) T) =
        native_ite (native_Teq (__eo_to_smt_type T) (SmtType.TypeRef s))
          (SmtType.Datatype s (__eo_to_smt_datatype d))
          (__eo_to_smt_type T)
  | Term.UOp op => by
      cases op <;> simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UOp1 op x => by
      cases op <;> simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UOp2 op x y => by
      cases op <;> simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UOp3 op x y z => by
      cases op <;> simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_nil => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_cons => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Bool => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Boolean b => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Numeral n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Rational q => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.String str => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Binary w n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Type => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Stuck => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Apply f x => by
      have hneq : __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s :=
        eo_to_smt_type_apply_ne_typeref f x s
      simp [native_ite, native_teq, native_Teq, hneq]
  | Term.FunType => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Var name ty => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeType s2 d2 => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeTypeRef s2 => by
      by_cases hs : s2 = s
      · subst s2
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s = true
        · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hReserved]
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s <;> simp [hName] at hReserved ⊢
          simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hReservedFalse]
      · by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
        · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs, hReserved]
        · have hReservedFalse : __eo_to_smt_reserved_datatype_name s2 = false := by
            cases hName : __eo_to_smt_reserved_datatype_name s2 <;> simp [hName] at hReserved ⊢
          simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs, hReservedFalse]
  | Term.DtcAppType T U => by
      let V :=
        __smtx_typeof_guard (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)))
      have hneq : V ≠ SmtType.TypeRef s := by
        dsimp [V]
        exact smtx_typeof_guard_dtc_app_ne_typeref (__eo_to_smt_type T) (__eo_to_smt_type U) s
      by_cases hV : V = SmtType.TypeRef s
      · exact False.elim (hneq hV)
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, V, hV]
  | Term.DtCons s2 d2 i => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DtSel s2 d2 i j => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.USort u => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UConst i T => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]

/-- Constructor congruence for SMT datatype constructors. -/
private theorem smt_datatype_cons_congr
    {T1 T2 : SmtType} {c1 c2 : SmtDatatypeCons}
    (hT : T1 = T2) (hc : c1 = c2) :
    SmtDatatypeCons.cons T1 c1 = SmtDatatypeCons.cons T2 c2 := by
  cases hT
  cases hc
  rfl

/-- `__smtx_dtc_substitute` takes its generic branch when the head type is not a datatype. -/
private theorem smtx_dtc_substitute_non_datatype
    (s : native_String) (d : SmtDatatype) (T : SmtType) (c : SmtDatatypeCons)
    (hT : ∀ s2 d2, T ≠ SmtType.Datatype s2 d2) :
    __smtx_dtc_substitute s d (SmtDatatypeCons.cons T c) =
      SmtDatatypeCons.cons
        (native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T)
        (__smtx_dtc_substitute s d c) := by
  cases T <;> simp [__smtx_dtc_substitute, __smtx_type_substitute,
    native_ite, native_Teq, native_streq] at hT ⊢
  case TypeRef r =>
    by_cases hEq : s = r
    · simp [hEq]
    · have hEq' : r ≠ s := fun h => hEq h.symm
      simp [hEq, hEq']

/-- Recursive calls from a datatype-constructor tail decrease the `Sum` measure. -/
private theorem sum_size_inl_lt_cons (T : Term) (c : DatatypeCons) :
    Sum.elim sizeOf sizeOf ((Sum.inl c : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inl (DatatypeCons.cons T c) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.DatatypeCons.cons.sizeOf_spec]
  omega

/-- Recursive calls into a datatype-valued field decrease the `Sum` measure. -/
private theorem sum_size_inr_lt_datatype_cons
    (s : native_String) (d : Datatype) (c : DatatypeCons) :
    Sum.elim sizeOf sizeOf ((Sum.inr d : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf
        (Sum.inl (DatatypeCons.cons (Term.DatatypeType s d) c) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.DatatypeCons.cons.sizeOf_spec, Eo.Term.DatatypeType.sizeOf_spec]
  omega

/-- Recursive calls from the constructor part of a datatype sum decrease the `Sum` measure. -/
private theorem sum_size_inl_lt_sum (c : DatatypeCons) (d : Datatype) :
    Sum.elim sizeOf sizeOf ((Sum.inl c : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inr (Datatype.sum c d) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.Datatype.sum.sizeOf_spec]
  omega

/-- Recursive calls from the tail part of a datatype sum decrease the `Sum` measure. -/
private theorem sum_size_inr_lt_sum (c : DatatypeCons) (d : Datatype) :
    Sum.elim sizeOf sizeOf ((Sum.inr d : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inr (Datatype.sum c d) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.Datatype.sum.sizeOf_spec]
  omega

/- Weakening EO validity along ref-list inclusion. Kept local so the Mini substitution
translation theorem can carry the validity context it actually needs. -/
mutual
private theorem eo_type_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {T : Term},
      eo_type_valid_rec refs T ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      eo_type_valid_rec refs' T
  | Term.UOp op, h, _ => by
      cases op <;> simp [eo_type_valid_rec] at h ⊢
  | Term.Bool, _h, _ => by
      simp [eo_type_valid_rec]
  | Term.DatatypeType s d, h, hsub => by
      rcases h with ⟨hReserved, hD⟩
      exact ⟨hReserved, eo_datatype_valid_rec_weaken hD (by
        intro t ht
        simp at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (hsub t ht))⟩
  | Term.DatatypeTypeRef s, h, hsub => by
      rcases h with ⟨hReserved, hMem⟩
      exact ⟨hReserved, hsub s hMem⟩
  | Term.DtcAppType T U, h, _ => by
      simpa [eo_type_valid_rec] using h
  | Term.USort i, _h, _ => by
      simp [eo_type_valid_rec]
  | Term.Apply (Term.Apply Term.FunType T1) T2, h, _ => by
      simpa [eo_type_valid_rec] using h
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h, _ => by
      simpa [eo_type_valid_rec] using h
  | Term.Apply (Term.UOp UserOp.Seq) T, h, _ => by
      simpa [eo_type_valid_rec] using h
  | Term.Apply f x, h, _ => by
      cases f with
      | UOp op =>
          cases op <;>
            try (cases x <;> simp [eo_type_valid_rec] at h)
          all_goals
            try simp [eo_type_valid_rec] at h ⊢
            try exact h
      | Apply g y =>
          cases g with
          | FunType =>
              simpa [eo_type_valid_rec] using h
          | _ =>
              simp [eo_type_valid_rec] at h
      | _ =>
          simp [eo_type_valid_rec] at h
  | Term.__eo_List, h, _ => by simp [eo_type_valid_rec] at h
  | Term.__eo_List_nil, h, _ => by simp [eo_type_valid_rec] at h
  | Term.__eo_List_cons, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Boolean b, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Numeral n, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Rational q, h, _ => by simp [eo_type_valid_rec] at h
  | Term.String s, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Binary w n, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Type, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Stuck, h, _ => by simp [eo_type_valid_rec] at h
  | Term.FunType, h, _ => by simp [eo_type_valid_rec] at h
  | Term.Var name T, h, _ => by simp [eo_type_valid_rec] at h
  | Term.DtCons s d i, h, _ => by simp [eo_type_valid_rec] at h
  | Term.DtSel s d i j, h, _ => by simp [eo_type_valid_rec] at h
  | Term.UConst i T, h, _ => by simp [eo_type_valid_rec] at h
  | Term.UOp1 op x, h, _ => by cases op <;> simp [eo_type_valid_rec] at h
  | Term.UOp2 op x y, h, _ => by cases op <;> simp [eo_type_valid_rec] at h
  | Term.UOp3 op x y z, h, _ => by cases op <;> simp [eo_type_valid_rec] at h

private theorem eo_datatype_cons_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {c : DatatypeCons},
      eo_datatype_cons_valid_rec refs c ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      eo_datatype_cons_valid_rec refs' c
  | DatatypeCons.unit, _h, _ => by
      simp [eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h, hsub => by
      rcases h with ⟨hT, hC⟩
      exact ⟨eo_type_valid_rec_weaken hT hsub,
        eo_datatype_cons_valid_rec_weaken hC hsub⟩

private theorem eo_datatype_valid_rec_weaken
    {refs refs' : List native_String} :
    ∀ {d : Datatype},
      eo_datatype_valid_rec refs d ->
      (∀ t, t ∈ refs -> t ∈ refs') ->
      eo_datatype_valid_rec refs' d
  | Datatype.null, _h, _ => by
      simp [eo_datatype_valid_rec]
  | Datatype.sum c d, h, hsub => by
      rcases h with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_rec_weaken hC hsub,
        eo_datatype_valid_rec_weaken hD hsub⟩
end

private theorem eo_datatype_valid_rec_swap_cons
    {s s2 : native_String} {refs : List native_String} {d : Datatype}
    (h : eo_datatype_valid_rec (s2 :: s :: refs) d) :
    eo_datatype_valid_rec (s :: s2 :: refs) d :=
  eo_datatype_valid_rec_weaken h (by
    intro t ht
    simp at ht ⊢
    rcases ht with rfl | rfl | ht
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ht))

private theorem smtx_type_lift_eq_self_of_not_datatype
    (s : native_String) (d : SmtDatatype) (T : SmtType)
    (hT : ∀ s2 d2, T ≠ SmtType.Datatype s2 d2) :
    __smtx_type_lift s d T = T := by
  cases T with
  | Datatype s2 d2 =>
      exact False.elim (hT s2 d2 rfl)
  | _ =>
      rfl

/- In Mini, unlike the full CPC translation, there is no tuple type translation that can hide
datatype bodies under a shallow EO lift. The lift commutation is therefore valid once the
re-fold target body is in the injective/valid fragment. -/
mutual
private theorem eo_to_smt_type_lift_of_valid (s : native_String) (dRef : Datatype)
    {refs : List native_String}
    (hRef : eo_datatype_valid_rec refs dRef) :
    (T : Term) →
      __eo_to_smt_type (__eo_type_lift s dRef T) =
        __smtx_type_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_type T)
  | Term.DatatypeType s2 d2 => by
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
      · simp only [__eo_type_lift]
        by_cases hteq : native_teq (Term.DatatypeType s dRef) (Term.DatatypeType s2 d2) = true
        · rw [native_ite, if_pos hteq]
          have hEq : Term.DatatypeType s dRef = Term.DatatypeType s2 d2 :=
            of_decide_eq_true hteq
          injection hEq with hs _hd
          subst hs
          simp [__eo_to_smt_type, __smtx_type_lift, native_ite, hReserved]
        · rw [native_ite, if_neg hteq]
          simp [__eo_to_smt_type, __smtx_type_lift, native_ite, hReserved]
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s2 = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s2 <;> simp [hName] at hReserved ⊢
        simp only [__eo_type_lift]
        by_cases hteq : native_teq (Term.DatatypeType s dRef) (Term.DatatypeType s2 d2) = true
        · rw [native_ite, if_pos hteq]
          have hEq : Term.DatatypeType s dRef = Term.DatatypeType s2 d2 :=
            of_decide_eq_true hteq
          injection hEq with hs hd
          subst hs
          subst hd
          simp [__eo_to_smt_type, __smtx_type_lift, native_ite, hReservedFalse, native_Teq]
        · rw [native_ite, if_neg hteq]
          have hNoFold :
              ¬ native_Teq (SmtType.Datatype s (__eo_to_smt_datatype dRef))
                  (SmtType.Datatype s2 (__eo_to_smt_datatype d2)) = true := by
            intro hFold
            have hSmtEq :
                SmtType.Datatype s (__eo_to_smt_datatype dRef) =
                  SmtType.Datatype s2 (__eo_to_smt_datatype d2) :=
              of_decide_eq_true (by simpa [native_Teq] using hFold)
            injection hSmtEq with hs hd
            subst hs
            have hd' : dRef = d2 :=
              eo_to_smt_datatype_unique_of_valid_rec refs hRef hd
            subst hd'
            exact hteq (by simp [native_teq])
          simp [__eo_to_smt_type, __smtx_type_lift, native_ite, hReservedFalse, hNoFold,
            eo_to_smt_datatype_lift_of_valid s dRef hRef d2]
  | Term.Stuck => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.UOp op => by
      cases op <;> simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Apply f x => by
      rw [smtx_type_lift_eq_self_of_not_datatype s (__eo_to_smt_datatype dRef)
        (__eo_to_smt_type (Term.Apply f x)) (by
          intro s2 d2
          exact eo_to_smt_type_apply_ne_datatype f x s2 d2)]
      simp [__eo_type_lift]
  | Term.DtcAppType T U => by
      rw [smtx_type_lift_eq_self_of_not_datatype s (__eo_to_smt_datatype dRef)
        (__eo_to_smt_type (Term.DtcAppType T U)) (by
          intro s2 d2
          exact eo_to_smt_type_dtc_app_ne_datatype T U s2 d2)]
      simp [__eo_type_lift]
  | Term.DatatypeTypeRef s2 => by
      by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
      · simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift, native_ite, hReserved]
      · have hReservedFalse : __eo_to_smt_reserved_datatype_name s2 = false := by
          cases hName : __eo_to_smt_reserved_datatype_name s2 <;> simp [hName] at hReserved ⊢
        simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift, native_ite,
          hReservedFalse]
  | Term.Bool => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.USort i => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.__eo_List => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.__eo_List_nil => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.__eo_List_cons => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Boolean b => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Numeral n => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Rational q => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.String str => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Binary w n => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Type => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.FunType => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.Var name ty => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.DtCons s2 d2 i => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.DtSel s2 d2 i j => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.UConst i T => by
      simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.UOp1 op x => by
      cases op <;> simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.UOp2 op x y => by
      cases op <;> simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]
  | Term.UOp3 op x y z => by
      cases op <;> simp [__eo_type_lift, __eo_to_smt_type, __smtx_type_lift]

private theorem eo_to_smt_datatype_cons_lift_of_valid (s : native_String) (dRef : Datatype)
    {refs : List native_String}
    (hRef : eo_datatype_valid_rec refs dRef) :
    (c : DatatypeCons) →
      __eo_to_smt_datatype_cons (__eo_dtc_lift s dRef c) =
        __smtx_dtc_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype_cons c)
  | DatatypeCons.unit => by
      simp [__eo_dtc_lift, __eo_to_smt_datatype_cons, __smtx_dtc_lift]
  | DatatypeCons.cons T c => by
      simp [__eo_dtc_lift, __eo_to_smt_datatype_cons, __smtx_dtc_lift,
        eo_to_smt_type_lift_of_valid s dRef hRef T,
        eo_to_smt_datatype_cons_lift_of_valid s dRef hRef c]

private theorem eo_to_smt_datatype_lift_of_valid (s : native_String) (dRef : Datatype)
    {refs : List native_String}
    (hRef : eo_datatype_valid_rec refs dRef) :
    (d : Datatype) →
      __eo_to_smt_datatype (__eo_dt_lift s dRef d) =
        __smtx_dt_lift s (__eo_to_smt_datatype dRef) (__eo_to_smt_datatype d)
  | Datatype.null => by
      simp [__eo_dt_lift, __eo_to_smt_datatype, __smtx_dt_lift]
  | Datatype.sum c d => by
      simp [__eo_dt_lift, __eo_to_smt_datatype, __smtx_dt_lift,
        eo_to_smt_datatype_cons_lift_of_valid s dRef hRef c,
        eo_to_smt_datatype_lift_of_valid s dRef hRef d]
end

/--
Auxiliary commutation theorem for EO/SMT datatype substitution, indexed over the
sum of datatype constructors and datatypes so the recursion can descend into
nested datatype fields.
-/
private theorem eo_to_smt_substitute_aux
    (s : native_String) (d : Datatype) :
    ∀ x : Sum DatatypeCons Datatype,
      Sum.elim
        (fun c => ∀ refs, eo_datatype_cons_valid_rec (s :: refs) c →
          __eo_to_smt_datatype_cons (__eo_dtc_substitute s d c) =
            __smtx_dtc_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype_cons c))
        (fun d0 => ∀ refs, eo_datatype_valid_rec (s :: refs) d0 →
          __eo_to_smt_datatype (__eo_dt_substitute s d d0) =
            __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0))
        x
  | .inl DatatypeCons.unit => by
      intro refs _
      simp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
  | .inl (DatatypeCons.cons T c) => by
      intro refs hValid
      rcases hValid with ⟨hTValid, hCValid⟩
      cases T
      case DatatypeType s2 d2 =>
        rcases hTValid with ⟨hReservedFalse, hD2Valid⟩
        by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
        · rw [hReserved] at hReservedFalse
          cases hReservedFalse
        by_cases hst : native_streq s s2 = true
        · have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
          simpa [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute,
            __smtx_type_substitute, __eo_to_smt_type, native_ite, native_Teq,
            hst, hReserved] using hc
        · have hD2Swap : eo_datatype_valid_rec (s :: s2 :: refs) d2 :=
            eo_datatype_valid_rec_swap_cons hD2Valid
          have hd2 := eo_to_smt_substitute_aux s (__eo_dt_lift s2 d2 d) (.inr d2)
            (s2 :: refs) hD2Swap
          have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
          have hLift := eo_to_smt_datatype_lift_of_valid s2 d2 hD2Valid d
          simpa [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute,
            __smtx_type_substitute, __eo_to_smt_type, native_ite, native_Teq,
            hst, hReserved, hLift] using And.intro hd2 hc
      case Apply f x =>
        have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.Apply f x)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.Apply f x))
            (by simpa using hc)
        · intro s2 d2
          exact eo_to_smt_type_apply_ne_datatype f x s2 d2
      case DtcAppType T1 T2 =>
        have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.DtcAppType T1 T2)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.DtcAppType T1 T2))
            (by simpa using hc)
        · intro s2 d2
          exact eo_to_smt_type_dtc_app_ne_datatype T1 T2 s2 d2
      case DatatypeTypeRef s2 =>
        have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.DatatypeTypeRef s2)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.DatatypeTypeRef s2))
            (by simpa using hc)
        · intro s3 d3
          by_cases hReserved : __eo_to_smt_reserved_datatype_name s2 = true
          · simp [__eo_to_smt_type, hReserved]
          · have hReservedFalse : __eo_to_smt_reserved_datatype_name s2 = false := by
              cases hName : __eo_to_smt_reserved_datatype_name s2 <;> simp [hName] at hReserved ⊢
            simp [__eo_to_smt_type, hReservedFalse]
      case UOp op =>
        cases op <;>
          (have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
           dsimp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
           exact smt_datatype_cons_congr
             (eo_to_smt_type_substitute_typeref s d _)
             (by simpa using hc))
      all_goals
        have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
        dsimp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
        exact smt_datatype_cons_congr
          (eo_to_smt_type_substitute_typeref s d _)
          (by simpa using hc)
  | .inr Datatype.null => by
      intro refs _
      simp [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute]
  | .inr (Datatype.sum c d0) => by
      intro refs hValid
      rcases hValid with ⟨hCValid, hDValid⟩
      have hc := eo_to_smt_substitute_aux s d (.inl c) refs hCValid
      have hd0 := eo_to_smt_substitute_aux s d (.inr d0) refs hDValid
      simpa [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute] using
        And.intro hc hd0
termination_by x => Sum.elim sizeOf sizeOf x
decreasing_by
  all_goals
    first
    | exact sum_size_inl_lt_cons _ _
    | exact sum_size_inr_lt_datatype_cons _ _ _
    | exact sum_size_inl_lt_sum _ _
    | exact sum_size_inr_lt_sum _ _

/- The old unconditional substitution theorem is false on invalid datatypes: translation is not
injective there. The usable statement carries validity of the datatype being traversed. -/
theorem eo_to_smt_datatype_substitute
    (s : native_String) (d d0 : Datatype)
    (hValid : eo_datatype_valid_rec [s] d0) :
    __eo_to_smt_datatype (__eo_dt_substitute s d d0) =
      __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0) := by
  simpa using eo_to_smt_substitute_aux s d (.inr d0) [] hValid

/- The previous unconditional shape is intentionally not provided: it fails on invalid
datatype bodies whose distinct EO syntax translates to the same SMT body. -/

/-- Selector return typing commutes with EO-to-SMT type translation. -/
theorem eo_to_smt_type_typeof_dt_sel_return :
    ∀ d : Datatype, ∀ i j : native_Nat,
      __eo_to_smt_type (__eo_typeof_dt_sel_return d i j) =
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero j
  | Datatype.sum c d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return d i j
  | Datatype.null, i, j => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_type]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, j => by
      cases j <;> simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __eo_to_smt_type]
termination_by d i j => sizeOf d + i + j

/-- Selector return typing commutes with EO-to-SMT type translation on the EO-side substituted datatype. -/
theorem eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (hValid : eo_datatype_valid_rec [s] d) :
    __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  simp [__smtx_ret_typeof_sel, eo_to_smt_datatype_substitute s d d hValid,
    eo_to_smt_type_typeof_dt_sel_return]

/--
If the EO argument already has the exact datatype expected by a selector, the
translated EO result type matches the SMT selector return type.
-/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hValid : eo_datatype_valid_rec [s] d)
    (hx : __eo_typeof x = Term.DatatypeType s d) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  simp [__eo_typeof, __eo_typeof_apply, __eo_requires, hx,
    eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype s d i j hValid,
    native_ite, native_teq, native_not]

end TranslationProofs
-/

/-- Reflected declaration membership agrees with membership in the EO name list. -/
theorem eo_to_smt_datatype_decl_has
    : ∀ (s : native_String) (dd : DatatypeDecl),
      __smtx_dd_has_dt s (__eo_to_smt_datatype_decl dd) = true ↔
        s ∈ eo_datatype_decl_names dd
  | _, DatatypeDecl.nil => by
      simp [__smtx_dd_has_dt, __eo_to_smt_datatype_decl, eo_datatype_decl_names]
  | s, DatatypeDecl.cons s' d dd => by
      simp [__smtx_dd_has_dt, __eo_to_smt_datatype_decl, eo_datatype_decl_names,
        native_or, eo_to_smt_datatype_decl_has s dd, native_streq]
termination_by _ dd => sizeOf dd

/-- The ordinary (non-reference) constructor-field branch exposes recursive
well-formedness of the field and tail. -/
private theorem smtx_datatype_cons_wf_generic_parts
    {base : SmtDatatypeDecl} {T : SmtType} {c : SmtDatatypeCons}
    (hNotRef : ∀ s, T ≠ SmtType.TypeRef s)
    (h : __smtx_dt_cons_wf_rec base (SmtDatatypeCons.cons T c) = true) :
    __smtx_type_wf_rec T = true ∧ __smtx_dt_cons_wf_rec base c = true := by
  cases T <;>
    simp_all [__smtx_dt_cons_wf_rec, native_and, native_inhabited_type,
      __smtx_type_wf_rec]

/- Recover proof-side validity from the declaration-aware SMT well-formedness
predicates. The four statements are mutual because EO terms and datatype
declarations form one mutually inductive syntax. -/
mutual

private theorem eo_type_valid_of_smt_wf_rec_aux
    (refs : List native_String) :
    ∀ (T : Term),
      __smtx_type_wf_rec (__eo_to_smt_type T) = true ->
        eo_type_valid_rec refs T
  | Term.UOp op, h => by
      cases op <;> simp [__eo_to_smt_type, __smtx_type_wf_rec,
        eo_type_valid_rec] at h ⊢
  | Term.Bool, _ => by simp [eo_type_valid_rec]
  | Term.DatatypeType s dd, h => by
      cases hReserved : __eo_to_smt_reserved_datatype_name s
      · have hParts :
            __smtx_dd_has_dt s (__eo_to_smt_datatype_decl dd) = true ∧
              __smtx_decl_wf_rec (__eo_to_smt_datatype_decl dd)
                (__eo_to_smt_datatype_decl dd) = true := by
          simpa [__eo_to_smt_type, hReserved, __smtx_type_wf_rec,
            native_and] using h
        exact ⟨hReserved,
          (eo_to_smt_datatype_decl_has s dd).mp hParts.1,
          eo_datatype_decl_valid_of_smt_wf dd dd hParts.2⟩
      · simp [__eo_to_smt_type, hReserved, __smtx_type_wf_rec] at h
  | Term.DatatypeTypeRef s, h => by
      cases hReserved : __eo_to_smt_reserved_datatype_name s <;>
        simp [__eo_to_smt_type, hReserved, __smtx_type_wf_rec] at h
  | Term.USort i, _ => by simp [eo_type_valid_rec]
  | Term.Apply (Term.UOp UserOp.Seq) T, h => by
      have hT : __smtx_type_wf_rec (__eo_to_smt_type T) = true := by
        cases hTy : __eo_to_smt_type T <;>
          simp [__eo_to_smt_type, __smtx_typeof_guard, __smtx_type_wf_rec,
            native_ite, native_Teq, hTy, native_and] at h ⊢
        all_goals exact h.2
      simpa [eo_type_valid_rec] using eo_type_valid_of_smt_wf_rec_aux [] T hT
  | Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      cases hz : native_zleq 0 n
      · simp [__eo_to_smt_type, hz, __smtx_type_wf_rec] at h
      · simpa [eo_type_valid_rec, native_zleq] using hz
  | Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  cases hz : native_zleq 0 n
                  · simp [__eo_to_smt_type, hz, __smtx_type_wf_rec] at h
                  · simpa [eo_type_valid_rec, native_zleq] using hz
              | _ =>
                  simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
          | Seq =>
              have hx : __smtx_type_wf_rec (__eo_to_smt_type x) = true := by
                cases hTy : __eo_to_smt_type x <;>
                  simp [__eo_to_smt_type, __smtx_typeof_guard,
                    __smtx_type_wf_rec, native_ite, native_Teq, hTy,
                    native_and] at h ⊢
                all_goals exact h.2
              simpa [eo_type_valid_rec] using
                eo_type_valid_of_smt_wf_rec_aux [] x hx
          | _ =>
              simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;>
                cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard,
                  __smtx_type_wf_rec, native_ite, native_Teq, hY, hX] at h
          | _ =>
              simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
      | _ =>
          simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.__eo_List, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.__eo_List_nil, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.__eo_List_cons, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Boolean b, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Numeral n, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Rational q, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.String s, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Binary w n, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Type, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Stuck, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.FunType, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.Var name ty, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.DtcAppType T U, h => by
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_type_wf_rec,
          __smtx_typeof_guard, native_ite, native_Teq, hT, hU] at h
  | Term.DtCons s dd i, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.DtSel s dd i j, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
  | Term.UConst i T, h => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at h

private theorem eo_datatype_cons_valid_of_smt_wf
    (base : DatatypeDecl) :
    ∀ (c : DatatypeCons),
      __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_decl base)
        (__eo_to_smt_datatype_cons c) = true ->
      eo_datatype_cons_valid_rec (eo_datatype_decl_names base) c
  | DatatypeCons.unit, _ => by simp [eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h => by
      by_cases hRef : ∃ s, __eo_to_smt_type T = SmtType.TypeRef s
      · rcases hRef with ⟨s, hTy⟩
        rcases eo_to_smt_type_eq_typeref_iff.mp hTy with ⟨rfl, hReserved⟩
        have hParts :
            __smtx_dd_has_dt s (__eo_to_smt_datatype_decl base) = true ∧
              __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_decl base)
                (__eo_to_smt_datatype_cons c) = true := by
          simpa [__eo_to_smt_datatype_cons, __eo_to_smt_type, hReserved,
            __smtx_dt_cons_wf_rec, native_and] using h
        exact ⟨⟨hReserved,
          (eo_to_smt_datatype_decl_has s base).mp hParts.1⟩,
          eo_datatype_cons_valid_of_smt_wf base c hParts.2⟩
      · have hParts :
            __smtx_type_wf_rec (__eo_to_smt_type T) = true ∧
              __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_decl base)
                (__eo_to_smt_datatype_cons c) = true :=
          smtx_datatype_cons_wf_generic_parts
            (by intro s hs; exact hRef ⟨s, hs⟩)
            (by simpa [__eo_to_smt_datatype_cons] using h)
        exact ⟨eo_type_valid_of_smt_wf_rec_aux
            (eo_datatype_decl_names base) T hParts.1,
          eo_datatype_cons_valid_of_smt_wf base c hParts.2⟩

private theorem eo_datatype_valid_of_smt_wf
    (base : DatatypeDecl) :
    ∀ (d : Datatype),
      __smtx_dt_wf_rec (__eo_to_smt_datatype_decl base)
        (__eo_to_smt_datatype d) = true ->
      eo_datatype_valid_rec (eo_datatype_decl_names base) d
  | Datatype.null, _ => by simp [eo_datatype_valid_rec]
  | Datatype.sum c d, h => by
      have hParts :
          __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_decl base)
              (__eo_to_smt_datatype_cons c) = true ∧
            __smtx_dt_wf_rec (__eo_to_smt_datatype_decl base)
              (__eo_to_smt_datatype d) = true := by
        simpa [__eo_to_smt_datatype, __smtx_dt_wf_rec, native_and] using h
      exact ⟨eo_datatype_cons_valid_of_smt_wf base c hParts.1,
        eo_datatype_valid_of_smt_wf base d hParts.2⟩

private theorem eo_datatype_decl_valid_of_smt_wf
    (base : DatatypeDecl) :
    ∀ (dd : DatatypeDecl),
      __smtx_decl_wf_rec (__eo_to_smt_datatype_decl base)
        (__eo_to_smt_datatype_decl dd) = true ->
      eo_datatype_decl_valid_rec (eo_datatype_decl_names base) dd
  | DatatypeDecl.nil, _ => by simp [eo_datatype_decl_valid_rec]
  | DatatypeDecl.cons s d dd, h => by
      simp only [__eo_to_smt_datatype_decl, __smtx_decl_wf_rec, native_and,
        Bool.and_eq_true] at h
      exact ⟨eo_datatype_valid_of_smt_wf base d h.1,
        eo_datatype_decl_valid_of_smt_wf base dd h.2.2.1⟩

end

/-- A translated EO type satisfying recursive SMT well-formedness is valid. -/
theorem eo_type_valid_of_smt_wf_rec
    (refs : List native_String) (T : Term)
    (h : __smtx_type_wf_rec (__eo_to_smt_type T) = true) :
    eo_type_valid_rec refs T :=
  eo_type_valid_of_smt_wf_rec_aux refs T h

private theorem smtx_typeof_guard_ne_reglan_new
    (T U : SmtType) (hU : U ≠ SmtType.RegLan) :
    __smtx_typeof_guard T U ≠ SmtType.RegLan := by
  cases T <;> simp [__smtx_typeof_guard, native_Teq, hU]

/-- EO type translation never produces the SMT regular-language type. -/
theorem eo_to_smt_type_ne_reglan (T : Term) :
    __eo_to_smt_type T ≠ SmtType.RegLan := by
  cases T with
  | UOp op => cases op <;> simp [__eo_to_smt_type]
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x <;> try simp [__eo_to_smt_type]
              rename_i n
              cases h : native_zleq 0 n <;> simp
          | Seq =>
              simpa [__eo_to_smt_type] using
                smtx_typeof_guard_ne_reglan_new (__eo_to_smt_type x)
                  (SmtType.Seq (__eo_to_smt_type x)) (by simp)
          | _ => simp [__eo_to_smt_type]
      | Apply g y =>
          cases g <;> try simp [__eo_to_smt_type]
          simpa [__eo_to_smt_type] using
            smtx_typeof_guard_ne_reglan_new (__eo_to_smt_type y)
              (__smtx_typeof_guard (__eo_to_smt_type x)
                (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
              (smtx_typeof_guard_ne_reglan_new (__eo_to_smt_type x)
                (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) (by simp))
      | _ => simp [__eo_to_smt_type]
  | DtcAppType T U =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_ne_reglan_new (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)))
          (smtx_typeof_guard_ne_reglan_new (__eo_to_smt_type U)
            (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)) (by simp))
  | DatatypeType s dd =>
      cases h : __eo_to_smt_reserved_datatype_name s <;> simp [__eo_to_smt_type, h]
  | DatatypeTypeRef s =>
      cases h : __eo_to_smt_reserved_datatype_name s <;> simp [__eo_to_smt_type, h]
  | _ => simp [__eo_to_smt_type]

/-- Public SMT well-formedness of a translated EO type implies proof-side validity. -/
theorem eo_type_valid_of_smt_wf
    (refs : List native_String) (T : Term)
    (h : __smtx_type_wf (__eo_to_smt_type T) = true) :
    eo_type_valid_rec refs T := by
  cases hTy : __eo_to_smt_type T
  case FunType A B =>
      rcases eo_to_smt_type_eq_fun_iff.mp hTy with
        ⟨T1, T2, hT, hT1, hT2, _, _⟩
      subst T
      have hComponents :
          __smtx_type_wf_component A = true ∧
            __smtx_type_wf B = true := by
        simpa [__smtx_type_wf, native_and, hTy] using h
      have hA :
          native_inhabited_type A = true ∧ __smtx_type_wf_rec A = true := by
        simpa [__smtx_type_wf_component, native_and] using hComponents.1
      exact ⟨
        eo_type_valid_of_smt_wf_rec_aux [] T1 (by simpa [hT1] using hA.2),
        eo_type_valid_of_smt_wf [] T2 (by simpa [hT2] using hComponents.2)⟩
  case RegLan =>
      exact False.elim (eo_to_smt_type_ne_reglan T hTy)
  all_goals
      have hRec : __smtx_type_wf_rec (__eo_to_smt_type T) = true := by
        have hComponent :
            __smtx_type_wf_component (__eo_to_smt_type T) = true := by
          simpa [__smtx_type_wf, hTy] using h
        have hParts :
            native_inhabited_type (__eo_to_smt_type T) = true ∧
              __smtx_type_wf_rec (__eo_to_smt_type T) = true := by
          simpa [__smtx_type_wf_component, native_and] using hComponent
        exact hParts.2
      exact eo_type_valid_of_smt_wf_rec_aux refs T hRec
termination_by T

/-- A non-`None` well-formedness guard validates its translated EO input type. -/
theorem eo_type_valid_of_guard_wf_non_none
    (refs : List native_String) (T : Term) (U : SmtType)
    (h : __smtx_typeof_guard_wf (__eo_to_smt_type T) U ≠ SmtType.None) :
    eo_type_valid_rec refs T := by
  cases hWF : __smtx_type_wf (__eo_to_smt_type T)
  · exfalso
    exact h (by simp [__smtx_typeof_guard_wf, hWF, native_ite])
  · exact eo_type_valid_of_smt_wf refs T hWF

/-- Resolving a translated constructor chain agrees with translating EO
declaration resolution. -/
theorem eo_to_smt_datatype_cons_resolve
    : ∀ (c : DatatypeCons) (dd : DatatypeDecl),
      __eo_to_smt_datatype_cons (__eo_dtc_resolve c dd) =
        __smtx_dtc_resolve (__eo_to_smt_datatype_cons c)
          (__eo_to_smt_datatype_decl dd)
  | DatatypeCons.unit, _ => rfl
  | DatatypeCons.cons T c, dd => by
      by_cases hRef : ∃ s, T = Term.DatatypeTypeRef s
      · rcases hRef with ⟨s, rfl⟩
        cases hReserved : __eo_to_smt_reserved_datatype_name s <;>
          simp [__eo_dtc_resolve, __smtx_dtc_resolve,
            __eo_to_smt_datatype_cons, __eo_to_smt_type, hReserved,
            eo_to_smt_datatype_cons_resolve c dd]
      · have hTranslated :
            ∀ s, __eo_to_smt_type T ≠ SmtType.TypeRef s := by
          intro s h
          exact hRef ⟨s, (eo_to_smt_type_eq_typeref_iff.mp h).1⟩
        have hResolve :
            __smtx_dtc_resolve
                (SmtDatatypeCons.cons (__eo_to_smt_type T)
                  (__eo_to_smt_datatype_cons c))
                (__eo_to_smt_datatype_decl dd) =
              SmtDatatypeCons.cons (__eo_to_smt_type T)
                (__smtx_dtc_resolve (__eo_to_smt_datatype_cons c)
                  (__eo_to_smt_datatype_decl dd)) := by
          cases hT : __eo_to_smt_type T <;>
            simp_all [__smtx_dtc_resolve]
        rw [show __eo_dtc_resolve (DatatypeCons.cons T c) dd =
            DatatypeCons.cons T (__eo_dtc_resolve c dd) by
          cases T <;> simp_all [__eo_dtc_resolve]]
        simp [__eo_to_smt_datatype_cons, hResolve,
          eo_to_smt_datatype_cons_resolve c dd]
termination_by c _ => sizeOf c

/-- Datatype-body resolution commutes with translation. -/
theorem eo_to_smt_datatype_resolve
    : ∀ (d : Datatype) (dd : DatatypeDecl),
      __eo_to_smt_datatype (__eo_dt_resolve d dd) =
        __smtx_dt_resolve (__eo_to_smt_datatype d)
          (__eo_to_smt_datatype_decl dd)
  | Datatype.null, _ => rfl
  | Datatype.sum c d, dd => by
      simp [__eo_dt_resolve, __smtx_dt_resolve, __eo_to_smt_datatype,
        eo_to_smt_datatype_cons_resolve,
        eo_to_smt_datatype_resolve d dd]
termination_by d _ => sizeOf d

/-- Fully resolved declaration lookup commutes with translation. -/
theorem eo_to_smt_datatype_decl_resolve
    (s : native_String) (dd : DatatypeDecl) :
    __eo_to_smt_datatype (__eo_dd_resolve s dd) =
      __smtx_dt_resolve
        (__smtx_dd_lookup s (__eo_to_smt_datatype_decl dd))
        (__eo_to_smt_datatype_decl dd) := by
  rw [__eo_dd_resolve, eo_to_smt_datatype_resolve,
    eo_to_smt_datatype_decl_lookup]

/-- Exact datatype typing makes selector-result translation commute directly
with declaration lookup and resolution. -/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
    (x : Term) (s : native_String) (dd : DatatypeDecl) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s dd) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s dd i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype_decl dd) i j := by
  simp [__eo_typeof, __eo_typeof_apply, __eo_requires, hx,
    __smtx_ret_typeof_sel, eo_to_smt_datatype_decl_resolve,
    eo_to_smt_type_typeof_dt_sel_return, native_ite, native_teq, native_not]

end TranslationProofs
