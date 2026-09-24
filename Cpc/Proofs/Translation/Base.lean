module

public import Cpc.Spec
import all Cpc.Spec
public import Cpc.Proofs.TermCompat
public import Cpc.Logos
import all Cpc.Logos

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Proof-local compatibility name for the reserved datatype-name guard. -/
abbrev __eo_reserved_datatype_name : native_String -> native_Bool :=
  __eo_to_smt_reserved_datatype_name

/-- Computes `__eo_typeof` for `boolean`. -/
@[simp] theorem eo_typeof_boolean (b : native_Bool) :
    __eo_typeof (Term.Boolean b) = Term.Bool := by
  cases b <;> native_decide

/-- Computes `__eo_typeof` for `re_allchar`. -/
@[simp] theorem eo_typeof_re_allchar :
    __eo_typeof (Term.UOp UserOp.re_allchar) = Term.UOp UserOp.RegLan := by
  native_decide

/-- Computes `__eo_typeof` for `re_none`. -/
@[simp] theorem eo_typeof_re_none :
    __eo_typeof (Term.UOp UserOp.re_none) = Term.UOp UserOp.RegLan := by
  native_decide

/-- Computes `__eo_typeof` for `re_all`. -/
@[simp] theorem eo_typeof_re_all :
    __eo_typeof (Term.UOp UserOp.re_all) = Term.UOp UserOp.RegLan := by
  native_decide

/-- Simplifies EO-to-SMT translation for `boolean`. -/
@[simp] theorem eo_to_smt_boolean (b : native_Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := rfl

/-- Simplifies EO-to-SMT translation for `re_allchar`. -/
@[simp] theorem eo_to_smt_re_allchar :
    __eo_to_smt (Term.UOp UserOp.re_allchar) = SmtTerm.re_allchar := rfl

/-- Simplifies EO-to-SMT translation for `re_none`. -/
@[simp] theorem eo_to_smt_re_none :
    __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none := rfl

/-- Simplifies EO-to-SMT translation for `re_all`. -/
@[simp] theorem eo_to_smt_re_all :
    __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all := rfl

/-- Simplifies EO-to-SMT translation for `var`. -/
@[simp] theorem eo_to_smt_var (s : native_String) (T : Term) :
    __eo_to_smt (Term.Var (Term.String s) T) = SmtTerm.Var s (__eo_to_smt_type T) := rfl

/-- Simplifies EO-to-SMT translation for `uconst`. -/
@[simp] theorem eo_to_smt_uconst (i : native_Nat) (T : Term) :
    __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T) := rfl

/-- Simplifies EO-to-SMT translation for common binary operators. These
explicit equations keep proof simplification independent of which generated
equations Lean exposes for `__eo_to_smt`. -/
@[simp] theorem eo_to_smt_or (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) =
      SmtTerm.or (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_and (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) =
      SmtTerm.and (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_ite (c t e : Term) :
    __eo_to_smt
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) t) e) =
      SmtTerm.ite (__eo_to_smt c) (__eo_to_smt t) (__eo_to_smt e) := rfl

@[simp] theorem eo_to_smt_concat (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y) =
      SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_bvand (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y) =
      SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_bvor (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y) =
      SmtTerm.bvor (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_bvxor (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y) =
      SmtTerm.bvxor (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_str_concat (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y) =
      SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_re_concat (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) x) y) =
      SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_re_inter (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) x) y) =
      SmtTerm.re_inter (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_re_union (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) x) y) =
      SmtTerm.re_union (__eo_to_smt x) (__eo_to_smt y) := rfl

@[simp] theorem eo_to_smt_aci_sorted_marker (f t : Term) :
    __eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) t) =
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt f))
        (__eo_to_smt t) := rfl

/-- Simplifies EO-to-SMT translation for `@const`. -/
theorem eo_to_smt_at_const (i T : Term) :
    __eo_to_smt (Term.UOp2 UserOp2._at_const i T) =
      native_ite (__eo_to_smt_nat_is_valid i)
        (SmtTerm.UConst (native_const_id (__eo_to_smt_nat i)) (__eo_to_smt_type T))
        SmtTerm.None := rfl

/-- Only EO numerals are valid indices for the EO-to-SMT numeral translation. -/
theorem eo_to_smt_nat_is_valid_eq_numeral {i : Term}
    (h : __eo_to_smt_nat_is_valid i = true) :
    ∃ n : native_Int, i = Term.Numeral n := by
  cases i <;> simp [__eo_to_smt_nat_is_valid] at h ⊢

/-- Simplifies EO-to-SMT translation for `@const` at a valid index. -/
theorem eo_to_smt_at_const_of_valid {i T : Term}
    (h : __eo_to_smt_nat_is_valid i = true) :
    __eo_to_smt (Term.UOp2 UserOp2._at_const i T) =
      SmtTerm.UConst (native_const_id (__eo_to_smt_nat i)) (__eo_to_smt_type T) := by
  rw [eo_to_smt_at_const, h]
  simp [native_ite]

/-- Simplifies EO-to-SMT translation for `@const` at an invalid index. -/
theorem eo_to_smt_at_const_of_invalid {i T : Term}
    (h : __eo_to_smt_nat_is_valid i = false) :
    __eo_to_smt (Term.UOp2 UserOp2._at_const i T) = SmtTerm.None := by
  rw [eo_to_smt_at_const, h]
  simp [native_ite]

/-- `@const` never translates to a datatype constructor. -/
theorem eo_to_smt_at_const_ne_dt_cons (i T : Term) (s : native_String)
    (d : SmtDatatypeDecl) (k : native_Nat) :
    __eo_to_smt (Term.UOp2 UserOp2._at_const i T) ≠ SmtTerm.DtCons s d k := by
  cases hv : __eo_to_smt_nat_is_valid i
  · rw [eo_to_smt_at_const_of_invalid hv]
    intro h
    cases h
  · rw [eo_to_smt_at_const_of_valid hv]
    intro h
    cases h

/-- `@const` never translates to a datatype selector. -/
theorem eo_to_smt_at_const_ne_dt_sel (i T : Term) (s : native_String)
    (d : SmtDatatypeDecl) (k l : native_Nat) :
    __eo_to_smt (Term.UOp2 UserOp2._at_const i T) ≠ SmtTerm.DtSel s d k l := by
  cases hv : __eo_to_smt_nat_is_valid i
  · rw [eo_to_smt_at_const_of_invalid hv]
    intro h
    cases h
  · rw [eo_to_smt_at_const_of_valid hv]
    intro h
    cases h

/-- `@const` never translates to a datatype tester. -/
theorem eo_to_smt_at_const_ne_dt_tester (i T : Term) (s : native_String)
    (d : SmtDatatypeDecl) (k : native_Nat) :
    __eo_to_smt (Term.UOp2 UserOp2._at_const i T) ≠ SmtTerm.DtTester s d k := by
  cases hv : __eo_to_smt_nat_is_valid i
  · rw [eo_to_smt_at_const_of_invalid hv]
    intro h
    cases h
  · rw [eo_to_smt_at_const_of_valid hv]
    intro h
    cases h

/-- Computes `__eo_typeof` for a `@const` with a valid index and a type argument. -/
theorem eo_typeof_at_const {i T : Term}
    (hi : __eo_to_smt_nat_is_valid i = true)
    (hT : __eo_typeof T = Term.Type) :
    __eo_typeof (Term.UOp2 UserOp2._at_const i T) = T := by
  obtain ⟨n, rfl⟩ := eo_to_smt_nat_is_valid_eq_numeral hi
  have hTns : T ≠ Term.Stuck := by
    intro hStuck
    rw [hStuck] at hT
    cases hT
  change __eo_typeof__at_const (__eo_typeof (Term.Numeral n)) (__eo_typeof T) T = T
  have hn : __eo_typeof (Term.Numeral n) = Term.UOp UserOp.Int := rfl
  rw [hn, hT]
  cases T <;> first | rfl | exact absurd rfl hTns

/-- Simplifies EO-to-SMT translation for `set_empty`. -/
@[simp] theorem eo_to_smt_set_empty (T : Term) :
    __eo_to_smt (Term.set_empty T) = __eo_to_smt_set_empty (__eo_to_smt_type T) := rfl

/-- Simplifies EO-to-SMT type translation for `bool`. -/
@[simp] theorem eo_to_smt_type_bool :
    __eo_to_smt_type Term.Bool = SmtType.Bool := rfl

/-- Simplifies EO-to-SMT type translation for `int`. -/
@[simp] theorem eo_to_smt_type_int :
    __eo_to_smt_type (Term.UOp UserOp.Int) = SmtType.Int := rfl

/-- Simplifies EO-to-SMT type translation for `real`. -/
@[simp] theorem eo_to_smt_type_real :
    __eo_to_smt_type (Term.UOp UserOp.Real) = SmtType.Real := rfl

/-- Simplifies EO-to-SMT type translation for `fun`. -/
@[simp] theorem eo_to_smt_type_fun (T U : Term) :
      __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) =
        __smtx_typeof_guard (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U))) := by
    simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
@[simp] theorem eo_to_smt_type_dtc_app (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) =
      __smtx_typeof_guard (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U))) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `bitvec`. -/
@[simp] theorem eo_to_smt_type_bitvec (n : native_Int) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n)) =
      native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `char`. -/
@[simp] theorem eo_to_smt_type_char :
    __eo_to_smt_type (Term.UOp UserOp.Char) = SmtType.Char := rfl

/-- Simplifies EO-to-SMT type translation for `reglan`. -/
@[simp] theorem eo_to_smt_type_reglan :
    __eo_to_smt_type (Term.UOp UserOp.RegLan) = SmtType.RegLan := rfl

@[simp] theorem guarded_eo_datatype_ne_bool (s : native_String) (d : SmtDatatypeDecl) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Bool := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_int (s : native_String) (d : SmtDatatypeDecl) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Int := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_real (s : native_String) (d : SmtDatatypeDecl) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Real := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_reglan (s : native_String) (d : SmtDatatypeDecl) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.RegLan := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_char (s : native_String) (d : SmtDatatypeDecl) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Char := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_bitvec
    (s : native_String) (d : SmtDatatypeDecl) (w : native_Nat) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.BitVec w := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_seq
    (s : native_String) (d : SmtDatatypeDecl) (U : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Seq U := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_set
    (s : native_String) (d : SmtDatatypeDecl) (U : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Set U := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_map
    (s : native_String) (d : SmtDatatypeDecl) (A B : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.Map A B := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_fun
    (s : native_String) (d : SmtDatatypeDecl) (A B : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.FunType A B := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_datatype_ne_dtc_app
    (s : native_String) (d : SmtDatatypeDecl) (A B : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.Datatype s d) ≠
      SmtType.DtcAppType A B := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_bool (s : native_String) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Bool := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_int (s : native_String) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Int := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_real (s : native_String) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Real := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_reglan (s : native_String) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.RegLan := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_char (s : native_String) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Char := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_bitvec (s : native_String) (w : native_Nat) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.BitVec w := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_seq (s : native_String) (U : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Seq U := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_set (s : native_String) (U : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Set U := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_map (s : native_String) (A B : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.Map A B := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_fun (s : native_String) (A B : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.FunType A B := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

@[simp] theorem guarded_eo_typeref_ne_dtc_app (s : native_String) (A B : SmtType) :
    native_ite (__eo_reserved_datatype_name s) SmtType.None (SmtType.TypeRef s) ≠
      SmtType.DtcAppType A B := by
  cases h : __eo_reserved_datatype_name s <;> simp [native_ite]

/-- Simplifies EO-to-SMT type translation for `seq`. -/
@[simp] theorem eo_to_smt_type_seq (T : Term) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) =
      __smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Seq (__eo_to_smt_type T)) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `array`. -/
@[simp] theorem eo_to_smt_type_array (A B : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) A) B) =
      __smtx_typeof_guard (__eo_to_smt_type A)
        (__smtx_typeof_guard (__eo_to_smt_type B)
          (SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B))) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `set`. -/
@[simp] theorem eo_to_smt_type_set (T : Term) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) =
      __smtx_typeof_guard (__eo_to_smt_type T) (SmtType.Set (__eo_to_smt_type T)) := by
  simp [__eo_to_smt_type]

/-- Computes `__smtx_typeof` for `guard_wf_of_non_none`. -/
theorem smtx_typeof_guard_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_typeof_guard_wf T U = U := by
  intro h
  unfold __smtx_typeof_guard_wf at h ⊢
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Computes `__smtx_typeof` for `var_of_non_none`. -/
theorem smtx_typeof_var_of_non_none
    (s : native_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.Var s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Var s T) = T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none T T h

/-- Computes `__smtx_typeof` for `uconst_of_non_none`. -/
theorem smtx_typeof_uconst_of_non_none
    (s : native_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.UConst s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.UConst s T) = T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none T T h

/-- Computes `__smtx_typeof` for `seq_empty_of_non_none`. -/
theorem smtx_typeof_seq_empty_of_non_none
    (T : SmtType) :
    __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none (SmtType.Seq T) (SmtType.Seq T) h

/-- Computes `__smtx_typeof` for `set_empty_of_non_none`. -/
theorem smtx_typeof_set_empty_of_non_none
    (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.set_empty T) = SmtType.Set T := by
  intro h
  unfold __smtx_typeof at h ⊢
  exact smtx_typeof_guard_wf_of_non_none (SmtType.Set T) (SmtType.Set T) h

/-- Derives `smtx_binary_well_formed` from `non_none`. -/
theorem smtx_binary_well_formed_of_non_none
    (w n : native_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    native_zleq 0 w = true ∧
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
  intro h
  let g :=
    native_and (native_zleq 0 w)
      (native_zeq n (native_mod_total n (native_int_pow2 w)))
  have hg : g = true := by
    cases h' : g with
    | false =>
        exfalso
        apply h
        unfold __smtx_typeof
        simp [g, native_ite, h']
    | true =>
        rfl
  have hWidth : native_zleq 0 w = true := by
    cases hw : native_zleq 0 w <;> simp [g, SmtEval.native_and, hw] at hg
    rfl
  have hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) = true := by
    cases hm : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
      simp [g, SmtEval.native_and, hWidth, hm] at hg
    rfl
  exact ⟨hWidth, hMod⟩

/-- Computes `__smtx_typeof` for `binary_of_non_none`. -/
theorem smtx_typeof_binary_of_non_none
    (w n : native_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec (native_int_to_nat w) := by
  intro h
  obtain ⟨hWidth, hMod⟩ := smtx_binary_well_formed_of_non_none w n h
  have hAnd :
      native_and (native_zleq 0 w)
        (native_zeq n (native_mod_total n (native_int_pow2 w))) = true := by
    simp [SmtEval.native_and, hWidth, hMod]
  unfold __smtx_typeof
  simp [hAnd, native_ite]

/-- A non-`None` BV-size witness must come from a bitvector SMT type. -/
theorem smtx_bv_sizeof_term_non_none
    (t : SmtTerm)
    (h :
      __smtx_typeof
          (let _v0 := __eo_to_smt_bv_size (__smtx_typeof t)
           native_ite (native_zleq 0 _v0)
             (SmtTerm._at_purify (SmtTerm.Numeral _v0))
             SmtTerm.None) ≠
        SmtType.None) :
    ∃ w : native_Nat, __smtx_typeof t = SmtType.BitVec w := by
  cases hTy : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, by simp⟩
  | _ =>
      exfalso
      have hNone :
          __smtx_typeof
              (let _v0 := __eo_to_smt_bv_size (__smtx_typeof t)
               native_ite (native_zleq 0 _v0)
                 (SmtTerm._at_purify (SmtTerm.Numeral _v0))
                 SmtTerm.None) =
            SmtType.None := by
        have hNeg : native_zleq 0 (native_zneg 1) = false := by
          native_decide
        rw [hTy]
        simp [__eo_to_smt_bv_size, hNeg, native_ite]
        unfold __smtx_typeof
        rfl
      exact h hNone

end TranslationProofs
