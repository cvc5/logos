module

public import Cpc.Proofs.Translation.Base
import all Cpc.Proofs.Translation.Base

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Computes `__eo_typeof` for `to_int`. -/
@[simp] theorem eo_typeof_to_int :
    __eo_typeof (Term.UOp UserOp.to_int) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `is_int`. -/
@[simp] theorem eo_typeof_is_int :
    __eo_typeof (Term.UOp UserOp.is_int) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_to_lower`. -/
@[simp] theorem eo_typeof_str_to_lower :
    __eo_typeof (Term.UOp UserOp.str_to_lower) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_to_upper`. -/
@[simp] theorem eo_typeof_str_to_upper :
    __eo_typeof (Term.UOp UserOp.str_to_upper) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_to_code`. -/
@[simp] theorem eo_typeof_str_to_code :
    __eo_typeof (Term.UOp UserOp.str_to_code) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_from_code`. -/
@[simp] theorem eo_typeof_str_from_code :
    __eo_typeof (Term.UOp UserOp.str_from_code) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_is_digit`. -/
@[simp] theorem eo_typeof_str_is_digit :
    __eo_typeof (Term.UOp UserOp.str_is_digit) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_to_int`. -/
@[simp] theorem eo_typeof_str_to_int :
    __eo_typeof (Term.UOp UserOp.str_to_int) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_from_int`. -/
@[simp] theorem eo_typeof_str_from_int :
    __eo_typeof (Term.UOp UserOp.str_from_int) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `str_to_re`. -/
@[simp] theorem eo_typeof_str_to_re :
    __eo_typeof (Term.UOp UserOp.str_to_re) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `re_mult`. -/
@[simp] theorem eo_typeof_re_mult :
    __eo_typeof (Term.UOp UserOp.re_mult) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `re_plus`. -/
@[simp] theorem eo_typeof_re_plus :
    __eo_typeof (Term.UOp UserOp.re_plus) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `re_opt`. -/
@[simp] theorem eo_typeof_re_opt :
    __eo_typeof (Term.UOp UserOp.re_opt) = Term.Stuck := by
  decide +kernel

/-- Computes `__eo_typeof` for `re_comp`. -/
@[simp] theorem eo_typeof_re_comp :
    __eo_typeof (Term.UOp UserOp.re_comp) = Term.Stuck := by
  decide +kernel

end TranslationProofs
