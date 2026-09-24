module

public import Cpc.Proofs.TypePreservation.Helpers
import all Cpc.Proofs.TypePreservation.Helpers

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Value equality reflected from `native_veq`. -/
theorem eq_of_native_veq_true {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = true) :
    v1 = v2 := by
  simpa [native_veq] using h

/-- Disequality reflected from `native_veq`. -/
theorem ne_of_native_veq_false {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    v1 = v2 -> False := by
  intro hEq
  subst v2
  simp [native_veq] at h

/-- `native_veq` is symmetric on false results. -/
theorem native_veq_false_symm {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    native_veq v2 v1 = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

/-- Unfolding helper for the canonicality predicate. -/
theorem value_canonical_bool_eq_true {v : SmtValue} :
    value_canonical v = (__smtx_value_canonical v = true) := by
  rfl

/-- `NotValue` is canonical as a value constructor, although it is not well typed. -/
theorem value_canonical_notValue :
    value_canonical SmtValue.NotValue := by
  simp [value_canonical, __smtx_value_canonical]

theorem value_canonical_boolean (b : native_Bool) :
    value_canonical (SmtValue.Boolean b) := by
  simp [value_canonical, __smtx_value_canonical]

theorem value_canonical_numeral (n : native_Int) :
    value_canonical (SmtValue.Numeral n) := by
  simp [value_canonical, __smtx_value_canonical]

theorem value_canonical_rational (q : native_Rat) :
    value_canonical (SmtValue.Rational q) := by
  simp [value_canonical, __smtx_value_canonical]

theorem value_canonical_char (c : native_Char)
    (hc : native_char_valid c = true) :
    value_canonical (SmtValue.Char c) := by
  simp [value_canonical, __smtx_value_canonical, hc]

theorem value_canonical_reglan (r : SmtRegLan)
    (hr : __smtx_re_canonical r = true) :
    value_canonical (SmtValue.RegLan r) := by
  simp [value_canonical, __smtx_value_canonical, hr]

theorem value_canonical_char_zero :
    value_canonical (SmtValue.Char 0) := by
  exact value_canonical_char 0 (by native_decide)

theorem value_canonical_char_one :
    value_canonical (SmtValue.Char 1) := by
  exact value_canonical_char 1 (by native_decide)

theorem value_canonical_reglan_allchar :
    value_canonical (SmtValue.RegLan native_re_allchar) := by
  exact value_canonical_reglan native_re_allchar (by native_decide)

theorem value_canonical_reglan_none :
    value_canonical (SmtValue.RegLan native_re_none) := by
  exact value_canonical_reglan native_re_none (by native_decide)

theorem value_canonical_reglan_all :
    value_canonical (SmtValue.RegLan native_re_all) := by
  exact value_canonical_reglan native_re_all (by native_decide)

theorem value_canonical_uvalue (u n : native_Nat) :
    value_canonical (SmtValue.UValue u n) := by
  simp [value_canonical, __smtx_value_canonical]

theorem value_canonical_dt_cons (s : native_String) (d : SmtDatatypeDecl) (i : native_Nat) :
    value_canonical (SmtValue.DtCons s d i) := by
  simp [value_canonical, __smtx_value_canonical]

theorem value_canonical_apply
    {f x : SmtValue}
    (hf : value_canonical f)
    (hx : value_canonical x) :
    value_canonical (SmtValue.Apply f x) := by
  have hfBool : __smtx_value_canonical f = true := by
    simpa [value_canonical] using hf
  have hxBool : __smtx_value_canonical x = true := by
    simpa [value_canonical] using hx
  simp [value_canonical, __smtx_value_canonical, hfBool, hxBool,
    SmtEval.native_and]

/-- Boolean-typed values are canonical. -/
theorem value_canonical_of_bool_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    value_canonical v := by
  rcases bool_value_canonical h with ⟨b, rfl⟩
  exact value_canonical_boolean b

/-- Integer-typed values are canonical. -/
theorem value_canonical_of_int_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Int) :
    value_canonical v := by
  rcases int_value_canonical h with ⟨n, rfl⟩
  exact value_canonical_numeral n

/-- Real-typed values are canonical. -/
theorem value_canonical_of_real_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Real) :
    value_canonical v := by
  rcases real_value_canonical h with ⟨q, rfl⟩
  exact value_canonical_rational q

/-- Bit-vector typing includes the payload normalization condition, so typed bit-vectors are canonical. -/
theorem value_canonical_of_bitvec_type
    {v : SmtValue}
    {w : native_Nat}
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    value_canonical v := by
  rcases bitvec_value_canonical h with ⟨n, rfl⟩
  have hPayload :
      native_zeq n
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) = true :=
    bitvec_payload_canonical h
  simp [value_canonical, __smtx_value_canonical, native_ite,
    hPayload]

/-- Canonical regex-typed values are canonical. -/
theorem value_canonical_of_reglan_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.RegLan)
    (hCan : __smtx_value_canonical v = true) :
    value_canonical v := by
  simpa [value_canonical] using hCan

end Smtm
